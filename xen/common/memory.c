/******************************************************************************
 * memory.c
 *
 * Code to handle memory-related requests.
 *
 * Copyright (c) 2003-2004, B Dragovic
 * Copyright (c) 2003-2005, K A Fraser
 */

#include <xen/types.h>
#include <xen/lib.h>
#include <xen/mm.h>
#include <xen/perfc.h>
#include <xen/sched.h>
#include <xen/event.h>
#include <xen/paging.h>
#include <xen/iocap.h>
#include <xen/guest_access.h>
#include <xen/hypercall.h>
#include <xen/errno.h>
#include <xen/tmem.h>
#include <xen/tmem_xen.h>
#include <xen/numa.h>
#include <xen/mem_access.h>
#include <xen/trace.h>
#include <asm/current.h>
#include <asm/hardirq.h>
#include <asm/p2m.h>
#include <public/memory.h>
#include <xsm/xsm.h>
#include <asm-arm/smccc.h>
#include <xen/vmap.h>

#ifdef CONFIG_X86
#include <asm/guest.h>
#endif

#include <xen/delay.h>
#include <xen/time.h>

#define kmalloc(size, flags)      _xmalloc(size, sizeof(void *))
#define kmalloc2(size)            xzalloc_bytes(size)

#define kfree xfree
#define kzalloc(size, flags)		_xzalloc(size, sizeof(void *))

void schrodintext_change_page_permission(struct domain *d, paddr_t addr,
						int log_type, int op);

struct memop_args {
    /* INPUT */
    struct domain *domain;     /* Domain to be affected. */
    XEN_GUEST_HANDLE(xen_pfn_t) extent_list; /* List of extent base addrs. */
    unsigned int nr_extents;   /* Number of extents to allocate or free. */
    unsigned int extent_order; /* Size of each extent. */
    unsigned int memflags;     /* Allocation flags. */

    /* INPUT/OUTPUT */
    unsigned int nr_done;    /* Number of extents processed so far. */
    int          preempted;  /* Was the hypercall preempted? */
};

#ifndef CONFIG_CTLDOM_MAX_ORDER
#define CONFIG_CTLDOM_MAX_ORDER CONFIG_PAGEALLOC_MAX_ORDER
#endif
#ifndef CONFIG_PTDOM_MAX_ORDER
#define CONFIG_PTDOM_MAX_ORDER CONFIG_HWDOM_MAX_ORDER
#endif

static unsigned int __read_mostly domu_max_order = CONFIG_DOMU_MAX_ORDER;
static unsigned int __read_mostly ctldom_max_order = CONFIG_CTLDOM_MAX_ORDER;
static unsigned int __read_mostly hwdom_max_order = CONFIG_HWDOM_MAX_ORDER;
#ifdef HAS_PASSTHROUGH
static unsigned int __read_mostly ptdom_max_order = CONFIG_PTDOM_MAX_ORDER;
#endif

static int __init parse_max_order(const char *s)
{
    if ( *s != ',' )
        domu_max_order = simple_strtoul(s, &s, 0);
    if ( *s == ',' && *++s != ',' )
        ctldom_max_order = simple_strtoul(s, &s, 0);
    if ( *s == ',' && *++s != ',' )
        hwdom_max_order = simple_strtoul(s, &s, 0);
#ifdef HAS_PASSTHROUGH
    if ( *s == ',' && *++s != ',' )
        ptdom_max_order = simple_strtoul(s, &s, 0);
#endif

    return *s ? -EINVAL : 0;
}
custom_param("memop-max-order", parse_max_order);

static unsigned int max_order(const struct domain *d)
{
    unsigned int order = domu_max_order;

#ifdef HAS_PASSTHROUGH
    if ( cache_flush_permitted(d) && order < ptdom_max_order )
        order = ptdom_max_order;
#endif

    if ( is_control_domain(d) && order < ctldom_max_order )
        order = ctldom_max_order;

    if ( is_hardware_domain(d) && order < hwdom_max_order )
        order = hwdom_max_order;

    return min(order, MAX_ORDER + 0U);
}

static void increase_reservation(struct memop_args *a)
{
    struct page_info *page;
    unsigned long i;
    xen_pfn_t mfn;
    struct domain *d = a->domain;

    if ( !guest_handle_is_null(a->extent_list) &&
         !guest_handle_subrange_okay(a->extent_list, a->nr_done,
                                     a->nr_extents-1) )
        return;

    if ( a->extent_order > max_order(current->domain) )
        return;

    for ( i = a->nr_done; i < a->nr_extents; i++ )
    {
        if ( i != a->nr_done && hypercall_preempt_check() )
        {
            a->preempted = 1;
            goto out;
        }

        page = alloc_domheap_pages(d, a->extent_order, a->memflags);
        if ( unlikely(page == NULL) ) 
        {
            gdprintk(XENLOG_INFO, "Could not allocate order=%d extent: "
                    "id=%d memflags=%x (%ld of %d)\n",
                     a->extent_order, d->domain_id, a->memflags,
                     i, a->nr_extents);
            goto out;
        }

        /* Inform the domain of the new page's machine address. */ 
        if ( !paging_mode_translate(d) &&
             !guest_handle_is_null(a->extent_list) )
        {
            mfn = page_to_mfn(page);
            if ( unlikely(__copy_to_guest_offset(a->extent_list, i, &mfn, 1)) )
                goto out;
        }
    }

 out:
    a->nr_done = i;
}

static void populate_physmap(struct memop_args *a)
{
    struct page_info *page;
    unsigned int i, j;
    xen_pfn_t gpfn, mfn;
    struct domain *d = a->domain, *curr_d = current->domain;
    bool need_tlbflush = false;
    uint32_t tlbflush_timestamp = 0;

    if ( !guest_handle_subrange_okay(a->extent_list, a->nr_done,
                                     a->nr_extents-1) )
        return;

    if ( a->extent_order > (a->memflags & MEMF_populate_on_demand ? MAX_ORDER :
                            max_order(curr_d)) )
        return;

    if ( unlikely(!d->creation_finished) )
    {
        /*
         * With MEMF_no_tlbflush set, alloc_heap_pages() will ignore
         * TLB-flushes. After VM creation, this is a security issue (it can
         * make pages accessible to guest B, when guest A may still have a
         * cached mapping to them). So we do this only during domain creation,
         * when the domain itself has not yet been unpaused for the first
         * time.
         */
        a->memflags |= MEMF_no_tlbflush;
        /*
         * With MEMF_no_icache_flush, alloc_heap_pages() will skip
         * performing icache flushes. We do it only before domain
         * creation as once the domain is running there is a danger of
         * executing instructions from stale caches if icache flush is
         * delayed.
         */
        a->memflags |= MEMF_no_icache_flush;
    }

    for ( i = a->nr_done; i < a->nr_extents; i++ )
    {
        if ( i != a->nr_done && hypercall_preempt_check() )
        {
            a->preempted = 1;
            goto out;
        }

        if ( unlikely(__copy_from_guest_offset(&gpfn, a->extent_list, i, 1)) )
            goto out;

        if ( a->memflags & MEMF_populate_on_demand )
        {
            /* Disallow populating PoD pages on oneself. */
            if ( d == curr_d )
                goto out;

            if ( guest_physmap_mark_populate_on_demand(d, gpfn,
                                                       a->extent_order) < 0 )
                goto out;
        }
        else
        {
            if ( is_domain_direct_mapped(d) )
            {
                mfn = gpfn;

                for ( j = 0; j < (1U << a->extent_order); j++, mfn++ )
                {
                    if ( !mfn_valid(_mfn(mfn)) )
                    {
                        gdprintk(XENLOG_INFO, "Invalid mfn %#"PRI_xen_pfn"\n",
                                 mfn);
                        goto out;
                    }

                    page = mfn_to_page(mfn);
                    if ( !get_page(page, d) )
                    {
                        gdprintk(XENLOG_INFO,
                                 "mfn %#"PRI_xen_pfn" doesn't belong to d%d\n",
                                  mfn, d->domain_id);
                        goto out;
                    }
                    put_page(page);
                }

                mfn = gpfn;
            }
            else
            {
                page = alloc_domheap_pages(d, a->extent_order, a->memflags);

                if ( unlikely(!page) )
                {
                    if ( !tmem_enabled() || a->extent_order )
                        gdprintk(XENLOG_INFO,
                                 "Could not allocate order=%u extent: id=%d memflags=%#x (%u of %u)\n",
                                 a->extent_order, d->domain_id, a->memflags,
                                 i, a->nr_extents);
                    goto out;
                }

                if ( unlikely(a->memflags & MEMF_no_tlbflush) )
                {
                    for ( j = 0; j < (1U << a->extent_order); j++ )
                        accumulate_tlbflush(&need_tlbflush, &page[j],
                                            &tlbflush_timestamp);
                }

                mfn = page_to_mfn(page);
            }

            guest_physmap_add_page(d, _gfn(gpfn), _mfn(mfn), a->extent_order);

            if ( !paging_mode_translate(d) )
            {
                for ( j = 0; j < (1U << a->extent_order); j++ )
                    set_gpfn_from_mfn(mfn + j, gpfn + j);

                /* Inform the domain of the new page's machine address. */ 
                if ( unlikely(__copy_to_guest_offset(a->extent_list, i, &mfn, 1)) )
                    goto out;
            }
        }
    }

out:
    if ( need_tlbflush )
        filtered_flush_tlb_mask(tlbflush_timestamp);

    if ( a->memflags & MEMF_no_icache_flush )
        invalidate_icache();

    a->nr_done = i;
}

int guest_remove_page(struct domain *d, unsigned long gmfn)
{
    struct page_info *page;
#ifdef CONFIG_X86
    p2m_type_t p2mt;
#endif
    mfn_t mfn;
    int rc;

#ifdef CONFIG_X86
    mfn = get_gfn_query(d, gmfn, &p2mt);
    if ( unlikely(p2m_is_paging(p2mt)) )
    {
        rc = guest_physmap_remove_page(d, _gfn(gmfn), mfn, 0);
        put_gfn(d, gmfn);

        if ( rc )
            return rc;

        /* If the page hasn't yet been paged out, there is an
         * actual page that needs to be released. */
        if ( p2mt == p2m_ram_paging_out )
        {
            ASSERT(mfn_valid(mfn));
            page = mfn_to_page(mfn_x(mfn));
            if ( test_and_clear_bit(_PGC_allocated, &page->count_info) )
                put_page(page);
        }
        p2m_mem_paging_drop_page(d, gmfn, p2mt);

        return 0;
    }
    if ( p2mt == p2m_mmio_direct )
    {
        rc = clear_mmio_p2m_entry(d, gmfn, mfn, PAGE_ORDER_4K);
        put_gfn(d, gmfn);

        return rc;
    }
#else
    mfn = gfn_to_mfn(d, _gfn(gmfn));
#endif
    if ( unlikely(!mfn_valid(mfn)) )
    {
        put_gfn(d, gmfn);
        gdprintk(XENLOG_INFO, "Domain %u page number %lx invalid\n",
                d->domain_id, gmfn);

        return -EINVAL;
    }
            
#ifdef CONFIG_X86
    if ( p2m_is_shared(p2mt) )
    {
        /*
         * Unshare the page, bail out on error. We unshare because we
         * might be the only one using this shared page, and we need to
         * trigger proper cleanup. Once done, this is like any other page.
         */
        rc = mem_sharing_unshare_page(d, gmfn, 0);
        if ( rc )
        {
            put_gfn(d, gmfn);
            (void)mem_sharing_notify_enomem(d, gmfn, 0);

            return rc;
        }
        /* Maybe the mfn changed */
        mfn = get_gfn_query_unlocked(d, gmfn, &p2mt);
        ASSERT(!p2m_is_shared(p2mt));
    }
#endif /* CONFIG_X86 */

    page = mfn_to_page(mfn_x(mfn));
    if ( unlikely(!get_page(page, d)) )
    {
        put_gfn(d, gmfn);
        gdprintk(XENLOG_INFO, "Bad page free for domain %u\n", d->domain_id);

        return -ENXIO;
    }

    rc = guest_physmap_remove_page(d, _gfn(gmfn), mfn, 0);

    /*
     * With the lack of an IOMMU on some platforms, domains with DMA-capable
     * device must retrieve the same pfn when the hypercall populate_physmap
     * is called.
     *
     * For this purpose (and to match populate_physmap() behavior), the page
     * is kept allocated.
     */
    if ( !rc && !is_domain_direct_mapped(d) &&
         test_and_clear_bit(_PGC_allocated, &page->count_info) )
        put_page(page);

    put_page(page);
    put_gfn(d, gmfn);

    return rc;
}

static void decrease_reservation(struct memop_args *a)
{
    unsigned long i, j;
    xen_pfn_t gmfn;

    if ( !guest_handle_subrange_okay(a->extent_list, a->nr_done,
                                     a->nr_extents-1) ||
         a->extent_order > max_order(current->domain) )
        return;

    for ( i = a->nr_done; i < a->nr_extents; i++ )
    {
        if ( i != a->nr_done && hypercall_preempt_check() )
        {
            a->preempted = 1;
            goto out;
        }

        if ( unlikely(__copy_from_guest_offset(&gmfn, a->extent_list, i, 1)) )
            goto out;

        if ( tb_init_done )
        {
            struct {
                u64 gfn;
                int d:16,order:16;
            } t;

            t.gfn = gmfn;
            t.d = a->domain->domain_id;
            t.order = a->extent_order;
        
            __trace_var(TRC_MEM_DECREASE_RESERVATION, 0, sizeof(t), &t);
        }

        /* See if populate-on-demand wants to handle this */
        if ( is_hvm_domain(a->domain)
             && p2m_pod_decrease_reservation(a->domain, _gfn(gmfn),
                                             a->extent_order) )
            continue;

        for ( j = 0; j < (1 << a->extent_order); j++ )
            if ( guest_remove_page(a->domain, gmfn + j) )
                goto out;
    }

 out:
    a->nr_done = i;
}

static bool propagate_node(unsigned int xmf, unsigned int *memflags)
{
    const struct domain *currd = current->domain;

    BUILD_BUG_ON(XENMEMF_get_node(0) != NUMA_NO_NODE);
    BUILD_BUG_ON(MEMF_get_node(0) != NUMA_NO_NODE);

    if ( XENMEMF_get_node(xmf) == NUMA_NO_NODE )
        return true;

    if ( is_hardware_domain(currd) || is_control_domain(currd) )
    {
        if ( XENMEMF_get_node(xmf) >= MAX_NUMNODES )
            return false;

        *memflags |= MEMF_node(XENMEMF_get_node(xmf));
        if ( xmf & XENMEMF_exact_node_request )
            *memflags |= MEMF_exact_node;
    }
    else if ( xmf & XENMEMF_exact_node_request )
        return false;

    return true;
}

static long memory_exchange(XEN_GUEST_HANDLE_PARAM(xen_memory_exchange_t) arg)
{
    struct xen_memory_exchange exch;
    PAGE_LIST_HEAD(in_chunk_list);
    PAGE_LIST_HEAD(out_chunk_list);
    unsigned long in_chunk_order, out_chunk_order;
    xen_pfn_t     gpfn, gmfn, mfn;
    unsigned long i, j, k;
    unsigned int  memflags = 0;
    long          rc = 0;
    struct domain *d;
    struct page_info *page;

    if ( copy_from_guest(&exch, arg, 1) )
        return -EFAULT;

    if ( max(exch.in.extent_order, exch.out.extent_order) >
         max_order(current->domain) )
    {
        rc = -EPERM;
        goto fail_early;
    }

    /* Various sanity checks. */
    if ( (exch.nr_exchanged > exch.in.nr_extents) ||
         /* Input and output domain identifiers match? */
         (exch.in.domid != exch.out.domid) ||
         /* Sizes of input and output lists do not overflow a long? */
         ((~0UL >> exch.in.extent_order) < exch.in.nr_extents) ||
         ((~0UL >> exch.out.extent_order) < exch.out.nr_extents) ||
         /* Sizes of input and output lists match? */
         ((exch.in.nr_extents << exch.in.extent_order) !=
          (exch.out.nr_extents << exch.out.extent_order)) )
    {
        rc = -EINVAL;
        goto fail_early;
    }

    if ( !guest_handle_subrange_okay(exch.in.extent_start, exch.nr_exchanged,
                                     exch.in.nr_extents - 1) )
    {
        rc = -EFAULT;
        goto fail_early;
    }

    if ( exch.in.extent_order <= exch.out.extent_order )
    {
        in_chunk_order  = exch.out.extent_order - exch.in.extent_order;
        out_chunk_order = 0;

        if ( !guest_handle_subrange_okay(exch.out.extent_start,
                                         exch.nr_exchanged >> in_chunk_order,
                                         exch.out.nr_extents - 1) )
        {
            rc = -EFAULT;
            goto fail_early;
        }
    }
    else
    {
        in_chunk_order  = 0;
        out_chunk_order = exch.in.extent_order - exch.out.extent_order;

        if ( !guest_handle_subrange_okay(exch.out.extent_start,
                                         exch.nr_exchanged << out_chunk_order,
                                         exch.out.nr_extents - 1) )
        {
            rc = -EFAULT;
            goto fail_early;
        }
    }

    if ( unlikely(!propagate_node(exch.out.mem_flags, &memflags)) )
    {
        rc = -EINVAL;
        goto fail_early;
    }

    d = rcu_lock_domain_by_any_id(exch.in.domid);
    if ( d == NULL )
    {
        rc = -ESRCH;
        goto fail_early;
    }

    rc = xsm_memory_exchange(XSM_TARGET, d);
    if ( rc )
    {
        rcu_unlock_domain(d);
        goto fail_early;
    }

    memflags |= MEMF_bits(domain_clamp_alloc_bitsize(
        d,
        XENMEMF_get_address_bits(exch.out.mem_flags) ? :
        (BITS_PER_LONG+PAGE_SHIFT)));

    for ( i = (exch.nr_exchanged >> in_chunk_order);
          i < (exch.in.nr_extents >> in_chunk_order);
          i++ )
    {
        if ( i != (exch.nr_exchanged >> in_chunk_order) &&
             hypercall_preempt_check() )
        {
            exch.nr_exchanged = i << in_chunk_order;
            rcu_unlock_domain(d);
            if ( __copy_field_to_guest(arg, &exch, nr_exchanged) )
                return -EFAULT;
            return hypercall_create_continuation(
                __HYPERVISOR_memory_op, "lh", XENMEM_exchange, arg);
        }

        /* Steal a chunk's worth of input pages from the domain. */
        for ( j = 0; j < (1UL << in_chunk_order); j++ )
        {
            if ( unlikely(__copy_from_guest_offset(
                &gmfn, exch.in.extent_start, (i<<in_chunk_order)+j, 1)) )
            {
                rc = -EFAULT;
                goto fail;
            }

            for ( k = 0; k < (1UL << exch.in.extent_order); k++ )
            {
#ifdef CONFIG_X86
                p2m_type_t p2mt;

                /* Shared pages cannot be exchanged */
                mfn = mfn_x(get_gfn_unshare(d, gmfn + k, &p2mt));
                if ( p2m_is_shared(p2mt) )
                {
                    put_gfn(d, gmfn + k);
                    rc = -ENOMEM;
                    goto fail; 
                }
#else /* !CONFIG_X86 */
                mfn = mfn_x(gfn_to_mfn(d, _gfn(gmfn + k)));
#endif
                if ( unlikely(!mfn_valid(_mfn(mfn))) )
                {
                    put_gfn(d, gmfn + k);
                    rc = -EINVAL;
                    goto fail;
                }

                page = mfn_to_page(mfn);

                rc = steal_page(d, page, MEMF_no_refcount);
                if ( unlikely(rc) )
                {
                    put_gfn(d, gmfn + k);
                    goto fail;
                }

                page_list_add(page, &in_chunk_list);
                put_gfn(d, gmfn + k);
            }
        }

        /* Allocate a chunk's worth of anonymous output pages. */
        for ( j = 0; j < (1UL << out_chunk_order); j++ )
        {
            page = alloc_domheap_pages(d, exch.out.extent_order,
                                       MEMF_no_owner | memflags);
            if ( unlikely(page == NULL) )
            {
                rc = -ENOMEM;
                goto fail;
            }

            page_list_add(page, &out_chunk_list);
        }

        /*
         * Success! Beyond this point we cannot fail for this chunk.
         */

        /* Destroy final reference to each input page. */
        while ( (page = page_list_remove_head(&in_chunk_list)) )
        {
            unsigned long gfn;

            if ( !test_and_clear_bit(_PGC_allocated, &page->count_info) )
                BUG();
            mfn = page_to_mfn(page);
            gfn = mfn_to_gmfn(d, mfn);
            /* Pages were unshared above */
            BUG_ON(SHARED_M2P(gfn));
            if ( guest_physmap_remove_page(d, _gfn(gfn), _mfn(mfn), 0) )
                domain_crash(d);
            put_page(page);
        }

        /* Assign each output page to the domain. */
        for ( j = 0; (page = page_list_remove_head(&out_chunk_list)); ++j )
        {
            if ( assign_pages(d, page, exch.out.extent_order,
                              MEMF_no_refcount) )
            {
                unsigned long dec_count;
                bool_t drop_dom_ref;

                /*
                 * Pages in in_chunk_list is stolen without
                 * decreasing the tot_pages. If the domain is dying when
                 * assign pages, we need decrease the count. For those pages
                 * that has been assigned, it should be covered by
                 * domain_relinquish_resources().
                 */
                dec_count = (((1UL << exch.in.extent_order) *
                              (1UL << in_chunk_order)) -
                             (j * (1UL << exch.out.extent_order)));

                spin_lock(&d->page_alloc_lock);
                drop_dom_ref = (dec_count &&
                                !domain_adjust_tot_pages(d, -dec_count));
                spin_unlock(&d->page_alloc_lock);

                if ( drop_dom_ref )
                    put_domain(d);

                free_domheap_pages(page, exch.out.extent_order);
                goto dying;
            }

            if ( __copy_from_guest_offset(&gpfn, exch.out.extent_start,
                                          (i << out_chunk_order) + j, 1) )
            {
                rc = -EFAULT;
                continue;
            }

            mfn = page_to_mfn(page);
            guest_physmap_add_page(d, _gfn(gpfn), _mfn(mfn),
                                   exch.out.extent_order);

            if ( !paging_mode_translate(d) )
            {
                for ( k = 0; k < (1UL << exch.out.extent_order); k++ )
                    set_gpfn_from_mfn(mfn + k, gpfn + k);
                if ( __copy_to_guest_offset(exch.out.extent_start,
                                            (i << out_chunk_order) + j,
                                            &mfn, 1) )
                    rc = -EFAULT;
            }
        }
        BUG_ON( !(d->is_dying) && (j != (1UL << out_chunk_order)) );

        if ( rc )
            goto fail;
    }

    exch.nr_exchanged = exch.in.nr_extents;
    if ( __copy_field_to_guest(arg, &exch, nr_exchanged) )
        rc = -EFAULT;
    rcu_unlock_domain(d);
    return rc;

    /*
     * Failed a chunk! Free any partial chunk work. Tell caller how many
     * chunks succeeded.
     */
 fail:
    /* Reassign any input pages we managed to steal. */
    while ( (page = page_list_remove_head(&in_chunk_list)) )
        if ( assign_pages(d, page, 0, MEMF_no_refcount) )
        {
            BUG_ON(!d->is_dying);
            if ( test_and_clear_bit(_PGC_allocated, &page->count_info) )
                put_page(page);
        }

 dying:
    rcu_unlock_domain(d);
    /* Free any output pages we managed to allocate. */
    while ( (page = page_list_remove_head(&out_chunk_list)) )
        free_domheap_pages(page, exch.out.extent_order);

    exch.nr_exchanged = i << in_chunk_order;

 fail_early:
    if ( __copy_field_to_guest(arg, &exch, nr_exchanged) )
        rc = -EFAULT;
    return rc;
}

static int xenmem_add_to_physmap(struct domain *d,
                                 struct xen_add_to_physmap *xatp,
                                 unsigned int start)
{
    unsigned int done = 0;
    long rc = 0;
    union xen_add_to_physmap_batch_extra extra;

    if ( xatp->space != XENMAPSPACE_gmfn_foreign )
        extra.res0 = 0;
    else
        extra.foreign_domid = DOMID_INVALID;

    if ( xatp->space != XENMAPSPACE_gmfn_range )
        return xenmem_add_to_physmap_one(d, xatp->space, extra,
                                         xatp->idx, _gfn(xatp->gpfn));

    if ( xatp->size < start )
        return -EILSEQ;

    xatp->idx += start;
    xatp->gpfn += start;
    xatp->size -= start;

#ifdef CONFIG_HAS_PASSTHROUGH
    if ( need_iommu(d) )
        this_cpu(iommu_dont_flush_iotlb) = 1;
#endif

    while ( xatp->size > done )
    {
        rc = xenmem_add_to_physmap_one(d, xatp->space, extra,
                                       xatp->idx, _gfn(xatp->gpfn));
        if ( rc < 0 )
            break;

        xatp->idx++;
        xatp->gpfn++;

        /* Check for continuation if it's not the last iteration. */
        if ( xatp->size > ++done && hypercall_preempt_check() )
        {
            rc = start + done;
            break;
        }
    }

#ifdef CONFIG_HAS_PASSTHROUGH
    if ( need_iommu(d) )
    {
        int ret;

        this_cpu(iommu_dont_flush_iotlb) = 0;

        ret = iommu_iotlb_flush(d, xatp->idx - done, done);
        if ( unlikely(ret) && rc >= 0 )
            rc = ret;

        ret = iommu_iotlb_flush(d, xatp->gpfn - done, done);
        if ( unlikely(ret) && rc >= 0 )
            rc = ret;
    }
#endif

    return rc;
}

static int xenmem_add_to_physmap_batch(struct domain *d,
                                       struct xen_add_to_physmap_batch *xatpb,
                                       unsigned int start)
{
    unsigned int done = 0;
    int rc;

    if ( xatpb->size < start )
        return -EILSEQ;

    guest_handle_add_offset(xatpb->idxs, start);
    guest_handle_add_offset(xatpb->gpfns, start);
    guest_handle_add_offset(xatpb->errs, start);
    xatpb->size -= start;

    if ( !guest_handle_okay(xatpb->idxs, xatpb->size) ||
         !guest_handle_okay(xatpb->gpfns, xatpb->size) ||
         !guest_handle_okay(xatpb->errs, xatpb->size) )
        return -EFAULT;

    while ( xatpb->size > done )
    {
        xen_ulong_t idx;
        xen_pfn_t gpfn;

        if ( unlikely(__copy_from_guest_offset(&idx, xatpb->idxs, 0, 1)) )
        {
            rc = -EFAULT;
            goto out;
        }

        if ( unlikely(__copy_from_guest_offset(&gpfn, xatpb->gpfns, 0, 1)) )
        {
            rc = -EFAULT;
            goto out;
        }

        rc = xenmem_add_to_physmap_one(d, xatpb->space,
                                       xatpb->u,
                                       idx, _gfn(gpfn));

        if ( unlikely(__copy_to_guest_offset(xatpb->errs, 0, &rc, 1)) )
        {
            rc = -EFAULT;
            goto out;
        }

        guest_handle_add_offset(xatpb->idxs, 1);
        guest_handle_add_offset(xatpb->gpfns, 1);
        guest_handle_add_offset(xatpb->errs, 1);

        /* Check for continuation if it's not the last iteration. */
        if ( xatpb->size > ++done && hypercall_preempt_check() )
        {
            rc = start + done;
            goto out;
        }
    }

    rc = 0;

out:
    return rc;
}

static int construct_memop_from_reservation(
               const struct xen_memory_reservation *r,
               struct memop_args *a)
{
    unsigned int address_bits;

    a->extent_list  = r->extent_start;
    a->nr_extents   = r->nr_extents;
    a->extent_order = r->extent_order;
    a->memflags     = 0;

    address_bits = XENMEMF_get_address_bits(r->mem_flags);
    if ( (address_bits != 0) &&
         (address_bits < (get_order_from_pages(max_page) + PAGE_SHIFT)) )
    {
        if ( address_bits <= PAGE_SHIFT )
            return -EINVAL;
        a->memflags = MEMF_bits(address_bits);
    }

    if ( r->mem_flags & XENMEMF_vnode )
    {
        nodeid_t vnode, pnode;
        struct domain *d = a->domain;

        read_lock(&d->vnuma_rwlock);
        if ( d->vnuma )
        {
            vnode = XENMEMF_get_node(r->mem_flags);
            if ( vnode >= d->vnuma->nr_vnodes )
            {
                read_unlock(&d->vnuma_rwlock);
                return -EINVAL;
            }

            pnode = d->vnuma->vnode_to_pnode[vnode];
            if ( pnode != NUMA_NO_NODE )
            {
                a->memflags |= MEMF_node(pnode);
                if ( r->mem_flags & XENMEMF_exact_node_request )
                    a->memflags |= MEMF_exact_node;
            }
        }
        read_unlock(&d->vnuma_rwlock);
    }
    else if ( unlikely(!propagate_node(r->mem_flags, &a->memflags)) )
        return -EINVAL;

    return 0;
}

#ifdef CONFIG_HAS_PASSTHROUGH
struct get_reserved_device_memory {
    struct xen_reserved_device_memory_map map;
    unsigned int used_entries;
};

static int get_reserved_device_memory(xen_pfn_t start, xen_ulong_t nr,
                                      u32 id, void *ctxt)
{
    struct get_reserved_device_memory *grdm = ctxt;
    u32 sbdf = PCI_SBDF3(grdm->map.dev.pci.seg, grdm->map.dev.pci.bus,
                         grdm->map.dev.pci.devfn);

    if ( !(grdm->map.flags & XENMEM_RDM_ALL) && (sbdf != id) )
        return 0;

    if ( grdm->used_entries < grdm->map.nr_entries )
    {
        struct xen_reserved_device_memory rdm = {
            .start_pfn = start, .nr_pages = nr
        };

        if ( __copy_to_guest_offset(grdm->map.buffer, grdm->used_entries,
                                    &rdm, 1) )
            return -EFAULT;
    }

    ++grdm->used_entries;

    return 1;
}
#endif

static long xatp_permission_check(struct domain *d, unsigned int space)
{
    /*
     * XENMAPSPACE_dev_mmio mapping is only supported for hardware Domain
     * to map this kind of space to itself.
     */
    if ( (space == XENMAPSPACE_dev_mmio) &&
         (!is_hardware_domain(current->domain) || (d != current->domain)) )
        return -EACCES;

    return xsm_add_to_physmap(XSM_TARGET, current->domain, d);
}

lpae_t _schrobuf_hide_page(struct p2m_domain *p2m, paddr_t addr, lpae_t white_pte);
void p2m_flush_tlb(struct p2m_domain *p2m);

lpae_t mfn_to_p2m_entry(mfn_t mfn, p2m_type_t t, p2m_access_t a);

lpae_t schrobuf_hide_page(struct domain *d, paddr_t gpaddr, lpae_t pte)
{
    struct p2m_domain *p2m = &d->arch.p2m;
	int ret;
	lpae_t orig_pte;
        
	orig_pte = _schrobuf_hide_page(p2m, gpaddr, pte);

	p2m_flush_tlb(p2m);
	ret = iommu_iotlb_flush(d, gpaddr >> PAGE_SHIFT, 1);
	
	if (ret)
		PRINTK0("Warning: IOMMU_IOTLB flush failed (ret = %d)\n", ret);
		
	return orig_pte;
	
}

void _schrobuf_unhide_page(struct p2m_domain *p2m, paddr_t gpaddr, lpae_t orig_pte);

void schrobuf_unhide_page(struct domain *d, paddr_t gpaddr, lpae_t orig_pte)
{
	struct p2m_domain *p2m = &d->arch.p2m;
	int ret;
	
	_schrobuf_unhide_page(p2m, gpaddr, orig_pte);
	
	p2m_flush_tlb(p2m);
	ret = iommu_iotlb_flush(d, gpaddr >> PAGE_SHIFT, 1);
	
	if (ret)
		PRINTK0("Warning: IOMMU_IOTLB flush failed (ret = %d)\n", ret);
}

mfn_t display_p2m_lookup(struct domain *d, gfn_t gfn, p2m_type_t *t);

static unsigned long get_secondary_mapping(struct domain *d, unsigned long gpaddr)
{
	mfn_t mfn;

	// display_p2m always retains the correct mapping, albeit as read-only
	mfn = display_p2m_lookup(d, gaddr_to_gfn(gpaddr), NULL);
	
    if ( INVALID_PADDR == mfn ) {
	    PRINTK_ERR("Error: p2m_lookup failed\n");
            return -ESRCH;
	}

    if ( !mfn_valid(mfn) ) {
		PRINTK_ERR("Error: invalid mfn\n");
        	return -EINVAL;
	}

	return (unsigned long) map_domain_page(_mfn(mfn));
}

enum SCHROBUF_PAGE_STATE {
	SCHROBUF_MODIFIED = 0,
	SCHROBUF_SHARED = 1,
	SCHROBUF_INVALID = 2
};

int schrobuf_change_page_state(unsigned long gpaddr, int state)
{
	int ret;

	switch (state) {
		
	case SCHROBUF_SHARED:
		schrodintext_change_page_permission(current->domain, gpaddr,
					XEN_PG_PERM_LOG_TYPE_W, XEN_PG_PERM_START);
		break;
		
	case SCHROBUF_MODIFIED:
		schrodintext_change_page_permission(current->domain, gpaddr,
					XEN_PG_PERM_LOG_TYPE_RW, XEN_PG_PERM_STOP);
		break;		
		
	case SCHROBUF_INVALID:
		schrodintext_change_page_permission(current->domain, gpaddr,
					XEN_PG_PERM_LOG_TYPE_RW, XEN_PG_PERM_START);
		break;
		
	default:
		PRINTK_ERR("Error: unknown state.\n");
		break;
	}

	/* Note that the schrodintext_change_page_permission() does the CPU MMU flush already */
	ret = iommu_iotlb_flush(current->domain, gpaddr >> PAGE_SHIFT, 1);
	PRINTK0("ret = %d\n", ret);

	return 0;
}

struct protected_page {
	unsigned long orig_addr;
	unsigned long page_addr;
	unsigned long secondary_addr;
	unsigned long replace_addr;
	unsigned int num_pbufs;
	lpae_t orig_pte;
	struct list_head list;
};

struct protected_buf {
	unsigned long off;
	unsigned int size;
	struct protected_page *ppage;
	struct list_head list;
};

struct schrobuf {
	unsigned long buffers_mem;
	unsigned int num_buffers;
	unsigned int buffer_size;
	void *encrypted_text;
	unsigned int text_len;
	unsigned int text_buf_size;
	unsigned long handle;
	struct list_head pbufs;
	struct list_head list;
};

/* We need to maintain a list per guest */
struct list_head g_schrobufs;

/* We need to maintain a list per guest process (mm) */
struct list_head g_ppages;

static void add_schrobuf(struct schrobuf *schrobuf)
{
	list_add(&schrobuf->list, &g_schrobufs);
}

static void *get_schrobuf(uint64_t handle)
{
	struct schrobuf *schrobuf = NULL, *s_tmp;

	list_for_each_entry_safe(schrobuf, s_tmp, &g_schrobufs, list) {

		if (schrobuf->handle == (unsigned long) handle) {
			return schrobuf;
		}
	}

	PRINTK_ERR("Didn't find the schrobuf\n");

	return NULL;
}

static void remove_schrobuf(struct schrobuf *_schrobuf)
{
	struct schrobuf *schrobuf = NULL, *s_tmp;

	if (!_schrobuf) {
		PRINTK_ERR("Error: schrobuf is NULL\n");
		return;
	}

	list_for_each_entry_safe(schrobuf, s_tmp, &g_schrobufs, list) {

		if (schrobuf == _schrobuf) {
			list_del(&schrobuf->list);
			break;
		}
	}
}

static void add_ppage(struct protected_page *ppage)
{
	list_add(&ppage->list, &g_ppages);
}

static void add_pbuf(struct schrobuf *schrobuf, struct protected_buf *pbuf)
{
	list_add(&pbuf->list, &schrobuf->pbufs);
}

static void get_ppage_pbuf(struct schrobuf *schrobuf, unsigned long addr,
			   struct protected_page **ppage_ptr, struct protected_buf **pbuf_ptr)
{
	struct protected_page *ppage = NULL, *p_tmp;
	struct protected_buf *pbuf = NULL, *b_tmp;
	unsigned long page_addr, off;
	
	*ppage_ptr = NULL;
	*pbuf_ptr = NULL;

	if (!schrobuf) {
		PRINTK_ERR("Error: schrobuf is NULL\n");
		return;
	}

	page_addr = addr & PAGE_MASK;
	list_for_each_entry_safe(ppage, p_tmp, &g_ppages, list) {

		if (ppage->page_addr == page_addr) {
			*ppage_ptr = ppage;
			break;
			}
	}

	if (!*ppage_ptr)
		return;

	off = addr & ~PAGE_MASK;

	list_for_each_entry_safe(pbuf, b_tmp, &schrobuf->pbufs, list) {

		if (pbuf->off == off) {
			*pbuf_ptr = pbuf;
			break;
		}
	}

	return;
}

static void remove_ppage(struct protected_page *_ppage)
{
	struct protected_page *ppage = NULL, *p_tmp;

	list_for_each_entry_safe(ppage, p_tmp, &g_ppages, list) {

		if (ppage == _ppage) {
			list_del(&ppage->list);
			kfree(ppage);
			break;
		}
	}
}

static void clean_remove_ppage(struct protected_page *ppage)
{
	if (!ppage) {
		PRINTK_ERR("Error: ppage is NULL\n");
		return;
	}

	ppage->num_pbufs--;

	if (ppage->num_pbufs == 0) {
        unmap_domain_page_global((void *) ppage->secondary_addr);
		schrobuf_unhide_page(current->domain, ppage->orig_addr, ppage->orig_pte);
		list_del(&ppage->list);
		kfree(ppage);
	}
}

static void clean_remove_pbufs(struct schrobuf *schrobuf)
{
	struct protected_buf *pbuf = NULL, *b_tmp;

	if (!schrobuf) {
		PRINTK_ERR("Error: schrobuf is NULL\n");
		return;
	}

	list_for_each_entry_safe(pbuf, b_tmp, &schrobuf->pbufs, list) {

		/* We zero out the protected memory bufs before mapping them back */
		memset((void *) (pbuf->ppage->secondary_addr + pbuf->off), 0x00, pbuf->size);
		clean_remove_ppage(pbuf->ppage);
		list_del(&pbuf->list);
		kfree(pbuf);
	}
}

static void* schrobuf_decrypted_text = NULL;
static unsigned int* schrobuf_char_widths = NULL;

/* ASCII Codes for conditional character */
#define SPACE_CHAR 32
#define DASH_CHAR 45
// Shared memory between OP-TEE
static void __iomem *shared_buf;

static void schrobuf_decrypt(void* encrypted_text, unsigned int text_len, unsigned int text_buf_size) 
{
	struct arm_smccc_res res;

	if (!schrobuf_decrypted_text) {
		schrobuf_decrypted_text = _xmalloc(text_len, sizeof(void*));
		
		if (!schrobuf_decrypted_text) {
			PRINTK_ERR("Could not allocate memory for decrypted_text! encrypted_text = 0x%p", encrypted_text);
			return;
		}
		memset(schrobuf_decrypted_text, 0, text_len);

		// Map shared memory into Xen - address/size hardcoded for now
		shared_buf = ioremap_cache(0xfee00000, 0x1000);
		// Copy encrypted_text to shared memory
		memcpy(shared_buf, encrypted_text, text_buf_size);
		// Perform SMC to decrypt text
		arm_smccc_1_1_smc(OPTEE_SMC_SCHRODTEXT_DECRYPT, text_buf_size, text_len, 0, &res);
		memcpy(schrobuf_decrypted_text, shared_buf, text_len);
	}
}

static int schrobuf_get_char_widths(unsigned long char_widths, unsigned int char_widths_size) 
{
	schrobuf_char_widths = xmalloc_array(unsigned int, char_widths_size);
	
	if (!schrobuf_char_widths) {
		PRINTK_ERR("Could not allocate memory for schrobuf_char_widths\n");
		return -ENOMEM;
	}

	if (raw_copy_from_guest((void *) schrobuf_char_widths, (void * __user) char_widths, char_widths_size * sizeof(int))) {
		PRINTK_ERR("Could not copy char_widths from guest");
		return -EFAULT;
	}
	
	return 0;
}

static int schrobuf_register(struct xen_schrobuf_register_data data)
{
	struct schrobuf *schrobuf = NULL;
	int ret;

	schrobuf = kzalloc(sizeof(*schrobuf), GFP_KERNEL);
	if (!schrobuf) {
		PRINTK_ERR("Error: could not allocate memory for schrobuf\n");
		return -ENOMEM;
	}

	schrobuf->handle = (unsigned long) data.handle;
	schrobuf->buffers_mem = (unsigned long) data.buffers_mem;
	schrobuf->num_buffers = (unsigned int) data.num_buffers;
	schrobuf->buffer_size = (unsigned int) data.buffer_size;
	schrobuf->text_len = (unsigned int) data.text_len;
	schrobuf->text_buf_size = (unsigned int) data.text_buf_size;

	schrobuf->encrypted_text = kmalloc(schrobuf->text_buf_size, GFP_KERNEL);
	if (!schrobuf->encrypted_text) {
		PRINTK_ERR("Error: could not allocate memory for encrypted text\n");
		kfree(schrobuf);
		return -ENOMEM;
	}

	ret = raw_copy_from_guest((void *) schrobuf->encrypted_text,
        			  (void * __user) data.encrypted_text, schrobuf->text_buf_size);
	if (ret) {
		PRINTK_ERR("schrobuf_register Error: could not copy the encrypted text; ret = %d\n", (int) ret);
		kfree(schrobuf->encrypted_text);
		kfree(schrobuf);
		return -EFAULT;
	}
	// Secure Monitor Call to OP-TEE to decrypt text and get shared memory setup between Xen and secure world
	schrobuf_decrypt(schrobuf->encrypted_text, schrobuf->text_len, schrobuf->text_buf_size);

	if (!schrobuf_char_widths && data.char_widths) {
		schrobuf_get_char_widths(data.char_widths, data.char_widths_size);
	}

	INIT_LIST_HEAD(&schrobuf->pbufs);
	add_schrobuf(schrobuf);

	return 0;
}

static int schrobuf_unregister(struct xen_schrobuf_unregister_data data)
{
	struct schrobuf *schrobuf = get_schrobuf(data.handle);
	if (!schrobuf) {
		PRINTK_ERR("Error: schrobuf is NULL\n");
		return -EINVAL;
	}

	if (schrobuf->encrypted_text)
		kfree(schrobuf->encrypted_text);

	clean_remove_pbufs(schrobuf);
	remove_schrobuf(schrobuf);
	kfree(schrobuf);
	
	if (schrobuf_decrypted_text) {
		kfree(schrobuf_decrypted_text);
		schrobuf_decrypted_text = NULL;	
	}
	if (schrobuf_char_widths) {
		kfree(schrobuf_char_widths);
		schrobuf_char_widths = NULL;
	}
		
	return 0;
}

static int schrobuf_create_page(struct domain *d, void **p, lpae_t *ptep)
{
    struct page_info *page;
    struct p2m_domain *p2m = &d->arch.p2m;
    
    page = alloc_domheap_page(NULL, 0);
    if ( page == NULL ) {
		PRINTK_ERR("Error: could not allocate a page\n");
        return -ENOMEM;
    }

    *p = __map_domain_page(page);

    *ptep = mfn_to_p2m_entry(page_to_mfn(page), p2m_ram_rw,
                           p2m->default_access);
    return 0;
}

static int schrobuf_blend(uint8_t *dst_addr, uint8_t *src_addr, int size) 
{    
    int i;
    int br, bg, bb, ba, fr, fg, fb, fa;
    for (i = 0; i < size; i += 4) {
           br = dst_addr[i];
           bg = dst_addr[i + 1];
           bb = dst_addr[i + 2];
           ba = dst_addr[i + 3];

           fr = src_addr[i];
           fg = src_addr[i + 1];
           fb = src_addr[i + 2];
           fa = src_addr[i + 3];

           dst_addr[i] = (uint8_t) (((fr * fa) + (br * (255 - fa))) / 255);
           dst_addr[i + 1] = (uint8_t) (((fg * fa) + (bg * (255 - fa))) / 255);
           dst_addr[i + 2] = (uint8_t) (((fb * fa) + (bb * (255 - fa))) / 255);
           dst_addr[i + 3] = 0xFF;
    }
    
    return 0;
}
// Sample hardcoded text:       M   Y       S   S   N      =        1   2   3   -  1    2  -   0   1   2    3  
//unsigned int ascii_vals[20] = {77, 89, 32, 83, 83, 78, 32, 61, 32, 49, 50, 51, 45, 49, 50, 45, 48, 49, 50, 51};

static bool schrobuf_line_start = false;	// false if we have not resolved anything yet on current line of text, true otherwise
static unsigned int schrobuf_current_px = 0;			// the current x coordinate as seen by Xen
static unsigned int schrobuf_current_text_pos = 0;		// it is ok to init at 0 because schrobuf_line_start dictates whether or not this value is valid
static int schrobuf_addr_adjustment = 0;	// adjust the data.dst_addr to move rendered text, may be negative

static void schrobuf_adjust_reset(void) {
	schrobuf_line_start = false;
	schrobuf_current_px = 0;
	schrobuf_current_text_pos = 0;
	schrobuf_addr_adjustment = 0;
	if (schrobuf_char_widths) {
		kfree(schrobuf_char_widths);
		schrobuf_char_widths = NULL;
	}
}

// Performs adjustment as needed to ensure text appears aesthetically proper (needed only for non monospaced fonts)
// Xen adjusts only on x-axis, it assumes OS can properly layout on the y-axis
static void schrobuf_adjust(struct xen_schrobuf_resolve_data *data)
{
	int curr_char;
	
	if (!schrobuf_line_start) {
		schrobuf_current_px = data->px;
		schrobuf_current_text_pos = data->text_pos;
		schrobuf_line_start = true;
	}

	// We have finished resolving the previous text position
	if (data->text_pos != schrobuf_current_text_pos) {
		curr_char = (unsigned int) ((unsigned char*) schrobuf_decrypted_text)[schrobuf_current_text_pos];
		schrobuf_current_px += schrobuf_char_widths[(curr_char - 32)];
		//schrobuf_current_px += schrobuf_char_widths[(ascii_vals[schrobuf_current_text_pos]-32)];	// uncomment this and comment out above two and "int curr_char;" to use hard-coded text
		schrobuf_current_text_pos = data->text_pos;
		schrobuf_addr_adjustment = (schrobuf_current_px - data->px) * data->fb_bytespp;
	} 

	data->dst_paddr += schrobuf_addr_adjustment;

	// Reset on the last resolve for the last char in the current line
	if (data->conditional_char && data->last_res) {
		schrobuf_adjust_reset();
	}
}

static void __user *get_resolve_addr(struct schrobuf *schrobuf, unsigned int text_pos, bool conditional_char)
{
	unsigned int next_char;
	unsigned int text_len = schrobuf->text_len;
	
	if (!schrobuf_decrypted_text) {
		PRINTK0("Error: text was never decrypted.\n");
		next_char = SPACE_CHAR; // just render space since schrobuf_resolve expects something to render from this function
		goto resolve;
	}
	
	next_char = (unsigned int) ((unsigned char*) schrobuf_decrypted_text)[text_pos % text_len];	// modulo function to prevent going out of bounds for now
	//next_char = ascii_vals[text_pos % text_len]; // Uncomment all ascii_vals above if want to test hardcoded text; comment out above statement
	
	/* If conditional_char is set, we are either rendering the last character 
	 * that can fit on one line or the last character entirely.
	 * Determine which case it is.
	*/
	if (conditional_char) {
		/* If we are not rendering the last character, then we render a conditional character 
		 * because we are at the end of a line. Look at current character requested 
		 * to be rendered. If it is an alphabetic character (A/a - Z/z), then render a dash (-) 
		 * as the conditional character. Otherwise render a space ( ).
		 * If we are rendering the last character, then we have enough space to fit it.
		 * Don't render conditional character in that case and just render actual character.
		 */
		if (text_pos != (text_len - 1)) {
			if ( (next_char >= 65 && next_char <= 90) || (next_char >= 97 && next_char <= 122) )
				next_char = DASH_CHAR;
			else
				next_char = SPACE_CHAR;
		}
	}
	
resolve:
	next_char -= 32; /* Glyphbook starts at 32 on the ASCII table because ASCII codes for 0-31 are non visible characters. */

	if (next_char >= schrobuf->num_buffers) {
		PRINTK0("Something went wrong, requested character is outside glyphbook.\n");
		next_char = 0; // render space instead
	}
	
	return (void __user *) (schrobuf->buffers_mem + (next_char * schrobuf->buffer_size));
}

static int schrobuf_resolve(struct xen_schrobuf_resolve_data data)
{
	struct protected_buf *pbuf = NULL;
	struct protected_page *ppage = NULL;
	bool ppage_allocated = false;
	void *resolve_dst_addr, __user *resolve_src_addr, *replace_addr = NULL,
							*glyph_buffer = NULL;
	unsigned long secondary_addr;
	struct schrobuf *schrobuf = get_schrobuf(data.handle);
	int ret;
	lpae_t pte;

	if (!schrobuf) {
		PRINTK_ERR("Error: schrobuf is NULL\n");
		return -EINVAL;
	}

	if (!data.trust_addr && schrobuf_char_widths) {
		schrobuf_adjust(&data);
	} 

	if ((data.dst_paddr & ~PAGE_MASK) + schrobuf->buffer_size >= PAGE_SIZE) {
		PRINTK_ERR("Error: dst buff goes across page boundary.\n");
		return -EINVAL;
	}

	get_ppage_pbuf(schrobuf, data.dst_paddr, &ppage, &pbuf);

	glyph_buffer = kmalloc(schrobuf->buffer_size, GFP_KERNEL);
	if (!glyph_buffer) {
		PRINTK_ERR("Error: could not allocate memory for glyph_buffer.\n");
		return -ENOMEM;
	}

	if (pbuf)
		goto pbuf_ready;

	if (ppage) {
		ppage_allocated = true;
		goto ppage_ready;
	}

	ppage = kzalloc(sizeof(*ppage), GFP_KERNEL);
	if (!ppage) {
		PRINTK_ERR("Error: could not allocate memory for ppage\n");
		return -ENOMEM;
	}

	ret = schrobuf_create_page(current->domain, &replace_addr, &pte);
	if (ret) {
		PRINTK_ERR("Error: could not map the page in secondary addr\n");
		return -EFAULT;
	}
	
	ppage->orig_pte = schrobuf_hide_page(current->domain, data.dst_paddr, pte);
	ppage->orig_addr = (unsigned long) data.dst_paddr;	// save the first physical addr we get that corresponds to this page
	ppage->page_addr = (unsigned long) data.dst_paddr & PAGE_MASK;
	add_ppage(ppage);
	secondary_addr = get_secondary_mapping(current->domain, data.dst_paddr);

	if (!secondary_addr) {
		PRINTK_ERR("Error: could not map the page in secondary addr\n");
		schrobuf_unhide_page(current->domain, data.dst_paddr, ppage->orig_pte);
		remove_ppage(ppage);
		return -EFAULT;
	}

	memcpy(replace_addr, (void *) secondary_addr, PAGE_SIZE);
    clean_dcache_va_range(replace_addr, PAGE_SIZE);

	ppage->secondary_addr = (unsigned long) secondary_addr;
	ppage->replace_addr = (unsigned long) replace_addr;
ppage_ready:
	pbuf = kzalloc(sizeof(*pbuf), GFP_KERNEL);
	if (!pbuf) {
		PRINTK_ERR("Error: could not allocate memory for pbuf\n");
		if (!ppage_allocated) {
			schrobuf_unhide_page(current->domain, data.dst_paddr, ppage->orig_pte);
			remove_ppage(ppage);
		}
		return -ENOMEM;
	}

	pbuf->off = data.dst_paddr & ~PAGE_MASK;
	pbuf->size = schrobuf->buffer_size;
	pbuf->ppage = ppage;
	ppage->num_pbufs++;
	add_pbuf(schrobuf, pbuf);

pbuf_ready:
	resolve_dst_addr = (void *) (ppage->secondary_addr + pbuf->off);
	resolve_src_addr = get_resolve_addr(schrobuf, data.text_pos, data.conditional_char);
	
	ret = raw_copy_from_guest(glyph_buffer, resolve_src_addr, schrobuf->buffer_size);
	if (ret)
		PRINTK0("Could not make the resolution.\n");
	else { /* Successful resolution. Composite text. */
		schrobuf_blend(resolve_dst_addr, glyph_buffer, schrobuf->buffer_size);
    	clean_and_invalidate_dcache_va_range((void *) ppage->secondary_addr, PAGE_SIZE);
	}
	kfree(glyph_buffer);

	return 0;
}

bool schrobuf_initialized = false;

static void init_schrobuf_framework(struct domain *d)
{
    INIT_LIST_HEAD(&g_schrobufs);
    INIT_LIST_HEAD(&g_ppages);

    schrobuf_initialized = true;
}

long do_memory_op(unsigned long cmd, XEN_GUEST_HANDLE_PARAM(void) arg)
{
    struct domain *d, *curr_d = current->domain;
    long rc;
    struct xen_memory_reservation reservation;
    struct memop_args args;
    domid_t domid;
    unsigned long start_extent = cmd >> MEMOP_EXTENT_SHIFT;
    int op = cmd & MEMOP_CMD_MASK;

    switch ( op )
    {
    case XENMEM_increase_reservation:
    case XENMEM_decrease_reservation:
    case XENMEM_populate_physmap:
        if ( copy_from_guest(&reservation, arg, 1) )
            return start_extent;

        /* Is size too large for us to encode a continuation? */
        if ( reservation.nr_extents > (UINT_MAX >> MEMOP_EXTENT_SHIFT) )
            return start_extent;

        if ( unlikely(start_extent >= reservation.nr_extents) )
            return start_extent;

        d = rcu_lock_domain_by_any_id(reservation.domid);
        if ( d == NULL )
            return start_extent;
        args.domain = d;

        if ( construct_memop_from_reservation(&reservation, &args) )
        {
            rcu_unlock_domain(d);
            return start_extent;
        }

        args.nr_done   = start_extent;
        args.preempted = 0;

        if ( op == XENMEM_populate_physmap
             && (reservation.mem_flags & XENMEMF_populate_on_demand) )
            args.memflags |= MEMF_populate_on_demand;

        if ( xsm_memory_adjust_reservation(XSM_TARGET, curr_d, d) )
        {
            rcu_unlock_domain(d);
            return start_extent;
        }

#ifdef CONFIG_X86
        if ( pv_shim && op != XENMEM_decrease_reservation && !args.preempted )
            /* Avoid calling pv_shim_online_memory when preempted. */
            pv_shim_online_memory(args.nr_extents, args.extent_order);
#endif

        switch ( op )
        {
        case XENMEM_increase_reservation:
            increase_reservation(&args);
            break;
        case XENMEM_decrease_reservation:
            decrease_reservation(&args);
            break;
        default: /* XENMEM_populate_physmap */
            populate_physmap(&args);
            break;
        }

        rcu_unlock_domain(d);

        rc = args.nr_done;

        if ( args.preempted )
            return hypercall_create_continuation(
                __HYPERVISOR_memory_op, "lh",
                op | (rc << MEMOP_EXTENT_SHIFT), arg);

#ifdef CONFIG_X86
        if ( pv_shim && op == XENMEM_decrease_reservation )
            /*
             * Only call pv_shim_offline_memory when the hypercall has
             * finished. Note that nr_done is used to cope in case the
             * hypercall has failed and only part of the extents where
             * processed.
             */
            pv_shim_offline_memory(args.nr_extents, args.nr_done);
#endif

        break;

    case XENMEM_exchange:
        if ( unlikely(start_extent) )
            return -EINVAL;

        rc = memory_exchange(guest_handle_cast(arg, xen_memory_exchange_t));
        break;

    case XENMEM_maximum_ram_page:
        if ( unlikely(start_extent) )
            return -EINVAL;

        rc = max_page;
        break;

    case XENMEM_current_reservation:
    case XENMEM_maximum_reservation:
    case XENMEM_maximum_gpfn:
        if ( unlikely(start_extent) )
            return -EINVAL;

        if ( copy_from_guest(&domid, arg, 1) )
            return -EFAULT;

        d = rcu_lock_domain_by_any_id(domid);
        if ( d == NULL )
            return -ESRCH;

        rc = xsm_memory_stat_reservation(XSM_TARGET, curr_d, d);
        if ( rc )
        {
            rcu_unlock_domain(d);
            return rc;
        }

        switch ( op )
        {
        case XENMEM_current_reservation:
            rc = d->tot_pages;
            break;
        case XENMEM_maximum_reservation:
            rc = d->max_pages;
            break;
        default:
            ASSERT(op == XENMEM_maximum_gpfn);
            rc = domain_get_maximum_gpfn(d);
            break;
        }

        rcu_unlock_domain(d);

        break;

    case XENMEM_add_to_physmap:
    {
        struct xen_add_to_physmap xatp;

        BUILD_BUG_ON((typeof(xatp.size))-1 > (UINT_MAX >> MEMOP_EXTENT_SHIFT));

        /* Check for malicious or buggy input. */
        if ( start_extent != (typeof(xatp.size))start_extent )
            return -EDOM;

        if ( copy_from_guest(&xatp, arg, 1) )
            return -EFAULT;

        /* Foreign mapping is only possible via add_to_physmap_batch. */
        if ( xatp.space == XENMAPSPACE_gmfn_foreign )
            return -ENOSYS;

        d = rcu_lock_domain_by_any_id(xatp.domid);
        if ( d == NULL )
            return -ESRCH;

        rc = xatp_permission_check(d, xatp.space);
        if ( rc )
        {
            rcu_unlock_domain(d);
            return rc;
        }

        rc = xenmem_add_to_physmap(d, &xatp, start_extent);

        rcu_unlock_domain(d);

        if ( xatp.space == XENMAPSPACE_gmfn_range && rc > 0 )
            rc = hypercall_create_continuation(
                     __HYPERVISOR_memory_op, "lh",
                     op | (rc << MEMOP_EXTENT_SHIFT), arg);

        return rc;
    }

    case XENMEM_add_to_physmap_batch:
    {
        struct xen_add_to_physmap_batch xatpb;

        BUILD_BUG_ON((typeof(xatpb.size))-1 >
                     (UINT_MAX >> MEMOP_EXTENT_SHIFT));

        /* Check for malicious or buggy input. */
        if ( start_extent != (typeof(xatpb.size))start_extent )
            return -EDOM;

        if ( copy_from_guest(&xatpb, arg, 1) )
            return -EFAULT;

        /* This mapspace is unsupported for this hypercall. */
        if ( xatpb.space == XENMAPSPACE_gmfn_range )
            return -EOPNOTSUPP;

        d = rcu_lock_domain_by_any_id(xatpb.domid);
        if ( d == NULL )
            return -ESRCH;

        rc = xatp_permission_check(d, xatpb.space);
        if ( rc )
        {
            rcu_unlock_domain(d);
            return rc;
        }

        rc = xenmem_add_to_physmap_batch(d, &xatpb, start_extent);

        rcu_unlock_domain(d);

        if ( rc > 0 )
            rc = hypercall_create_continuation(
                    __HYPERVISOR_memory_op, "lh",
                    op | (rc << MEMOP_EXTENT_SHIFT), arg);

        return rc;
    }

    case XENMEM_remove_from_physmap:
    {
        struct xen_remove_from_physmap xrfp;
        struct page_info *page;

        if ( unlikely(start_extent) )
            return -EINVAL;

        if ( copy_from_guest(&xrfp, arg, 1) )
            return -EFAULT;

        d = rcu_lock_domain_by_any_id(xrfp.domid);
        if ( d == NULL )
            return -ESRCH;

        rc = xsm_remove_from_physmap(XSM_TARGET, curr_d, d);
        if ( rc )
        {
            rcu_unlock_domain(d);
            return rc;
        }

        page = get_page_from_gfn(d, xrfp.gpfn, NULL, P2M_ALLOC);
        if ( page )
        {
            rc = guest_physmap_remove_page(d, _gfn(xrfp.gpfn),
                                           _mfn(page_to_mfn(page)), 0);
            put_page(page);
        }
        else
            rc = -ENOENT;

        rcu_unlock_domain(d);

        break;
    }

    case XENMEM_access_op:
        rc = mem_access_memop(cmd, guest_handle_cast(arg, xen_mem_access_op_t));
        break;

    case XENMEM_claim_pages:
        if ( unlikely(start_extent) )
            return -EINVAL;

        if ( copy_from_guest(&reservation, arg, 1) )
            return -EFAULT;

        if ( !guest_handle_is_null(reservation.extent_start) )
            return -EINVAL;

        if ( reservation.extent_order != 0 )
            return -EINVAL;

        if ( reservation.mem_flags != 0 )
            return -EINVAL;

        d = rcu_lock_domain_by_id(reservation.domid);
        if ( d == NULL )
            return -EINVAL;

        rc = xsm_claim_pages(XSM_PRIV, d);

        if ( !rc )
            rc = domain_set_outstanding_pages(d, reservation.nr_extents);

        rcu_unlock_domain(d);

        break;

    case XENMEM_get_vnumainfo:
    {
        struct xen_vnuma_topology_info topology;
        unsigned int dom_vnodes, dom_vranges, dom_vcpus;
        struct vnuma_info tmp;

        if ( unlikely(start_extent) )
            return -EINVAL;

        /*
         * Guest passes nr_vnodes, number of regions and nr_vcpus thus
         * we know how much memory guest has allocated.
         */
        if ( copy_from_guest(&topology, arg, 1 ))
            return -EFAULT;

        if ( topology.pad != 0 )
            return -EINVAL;

        if ( (d = rcu_lock_domain_by_any_id(topology.domid)) == NULL )
            return -ESRCH;

        rc = xsm_get_vnumainfo(XSM_TARGET, d);
        if ( rc )
        {
            rcu_unlock_domain(d);
            return rc;
        }

        read_lock(&d->vnuma_rwlock);

        if ( d->vnuma == NULL )
        {
            read_unlock(&d->vnuma_rwlock);
            rcu_unlock_domain(d);
            return -EOPNOTSUPP;
        }

        dom_vnodes = d->vnuma->nr_vnodes;
        dom_vranges = d->vnuma->nr_vmemranges;
        dom_vcpus = d->max_vcpus;

        /*
         * Copied from guest values may differ from domain vnuma config.
         * Check here guest parameters make sure we dont overflow.
         * Additionaly check padding.
         */
        if ( topology.nr_vnodes < dom_vnodes      ||
             topology.nr_vcpus < dom_vcpus        ||
             topology.nr_vmemranges < dom_vranges )
        {
            read_unlock(&d->vnuma_rwlock);
            rcu_unlock_domain(d);

            topology.nr_vnodes = dom_vnodes;
            topology.nr_vcpus = dom_vcpus;
            topology.nr_vmemranges = dom_vranges;

            /* Copy back needed values. */
            return __copy_to_guest(arg, &topology, 1) ? -EFAULT : -ENOBUFS;
        }

        read_unlock(&d->vnuma_rwlock);

        tmp.vdistance = xmalloc_array(unsigned int, dom_vnodes * dom_vnodes);
        tmp.vmemrange = xmalloc_array(xen_vmemrange_t, dom_vranges);
        tmp.vcpu_to_vnode = xmalloc_array(unsigned int, dom_vcpus);

        if ( tmp.vdistance == NULL ||
             tmp.vmemrange == NULL ||
             tmp.vcpu_to_vnode == NULL )
        {
            rc = -ENOMEM;
            goto vnumainfo_out;
        }

        /*
         * Check if vnuma info has changed and if the allocated arrays
         * are not big enough.
         */
        read_lock(&d->vnuma_rwlock);

        if ( dom_vnodes < d->vnuma->nr_vnodes ||
             dom_vranges < d->vnuma->nr_vmemranges ||
             dom_vcpus < d->max_vcpus )
        {
            read_unlock(&d->vnuma_rwlock);
            rc = -EAGAIN;
            goto vnumainfo_out;
        }

        dom_vnodes = d->vnuma->nr_vnodes;
        dom_vranges = d->vnuma->nr_vmemranges;
        dom_vcpus = d->max_vcpus;

        memcpy(tmp.vmemrange, d->vnuma->vmemrange,
               sizeof(*d->vnuma->vmemrange) * dom_vranges);
        memcpy(tmp.vdistance, d->vnuma->vdistance,
               sizeof(*d->vnuma->vdistance) * dom_vnodes * dom_vnodes);
        memcpy(tmp.vcpu_to_vnode, d->vnuma->vcpu_to_vnode,
               sizeof(*d->vnuma->vcpu_to_vnode) * dom_vcpus);

        read_unlock(&d->vnuma_rwlock);

        rc = -EFAULT;

        if ( copy_to_guest(topology.vmemrange.h, tmp.vmemrange,
                           dom_vranges) != 0 )
            goto vnumainfo_out;

        if ( copy_to_guest(topology.vdistance.h, tmp.vdistance,
                           dom_vnodes * dom_vnodes) != 0 )
            goto vnumainfo_out;

        if ( copy_to_guest(topology.vcpu_to_vnode.h, tmp.vcpu_to_vnode,
                           dom_vcpus) != 0 )
            goto vnumainfo_out;

        topology.nr_vnodes = dom_vnodes;
        topology.nr_vcpus = dom_vcpus;
        topology.nr_vmemranges = dom_vranges;

        rc = __copy_to_guest(arg, &topology, 1) ? -EFAULT : 0;

 vnumainfo_out:
        rcu_unlock_domain(d);

        xfree(tmp.vdistance);
        xfree(tmp.vmemrange);
        xfree(tmp.vcpu_to_vnode);
        break;
    }

#ifdef CONFIG_HAS_PASSTHROUGH
    case XENMEM_reserved_device_memory_map:
    {
        struct get_reserved_device_memory grdm;

        if ( unlikely(start_extent) )
            return -EINVAL;

        if ( copy_from_guest(&grdm.map, arg, 1) ||
             !guest_handle_okay(grdm.map.buffer, grdm.map.nr_entries) )
            return -EFAULT;

        if ( grdm.map.flags & ~XENMEM_RDM_ALL )
            return -EINVAL;

        grdm.used_entries = 0;
        rc = iommu_get_reserved_device_memory(get_reserved_device_memory,
                                              &grdm);

        if ( !rc && grdm.map.nr_entries < grdm.used_entries )
            rc = -ENOBUFS;
        grdm.map.nr_entries = grdm.used_entries;
        if ( __copy_to_guest(arg, &grdm.map, 1) )
            rc = -EFAULT;

        break;
    }
#endif

    // SchrodinText hypercalls
    case XENMEM_schrobuf_register:
    {
        struct xen_schrobuf_register_data data;
      
		if (!schrobuf_initialized) {
		    init_schrobuf_framework(current->domain);
		}
 
		if ( copy_from_guest(&data,
        		guest_handle_cast(arg, xen_schrobuf_register_data_t), 1) ) {
	    	PRINTK_ERR( "XENMEM_schrobuf_register - could not copy from guest\n");
            return -EFAULT;
		}
		
   	 	rc = schrobuf_register(data); 
		break;
    }

    case XENMEM_schrobuf_unregister:
    {
        struct xen_schrobuf_unregister_data data;
	
		if (!schrobuf_initialized) {
	 	   PRINTK_ERR("Error: no previously registered schrobufs\n");
	 	   return -EINVAL;
		}
       
		if ( copy_from_guest(&data,
     	   		guest_handle_cast(arg, xen_schrobuf_unregister_data_t), 1) ) {
	  		 	PRINTK_ERR("Error: Could not copy data from guest\n");
          	    return -EFAULT;
		}

        rc = schrobuf_unregister(data); 
		break;
    }

    case XENMEM_schrobuf_resolve:
    {
        struct xen_schrobuf_resolve_data data;
	
		if (!schrobuf_initialized) {
	    	PRINTK_ERR("Error: not previously registered schrobufs\n");
	    	return -EINVAL;
		}
       
		if ( copy_from_guest(&data,
        		guest_handle_cast(arg, xen_schrobuf_resolve_data_t), 1) ) {
	    	PRINTK_ERR("Error: Could not copy data from guest\n");
            return -EFAULT; 
		}

        rc = schrobuf_resolve(data);
		break;
    }

    default:
        rc = arch_memory_op(cmd, arg);
        break;
    }

    return rc;
}

void clear_domain_page(mfn_t mfn)
{
    void *ptr = map_domain_page(mfn);

    clear_page(ptr);
    unmap_domain_page(ptr);
}

void copy_domain_page(mfn_t dest, mfn_t source)
{
    const void *src = map_domain_page(source);
    void *dst = map_domain_page(dest);

    copy_page(dst, src);
    unmap_domain_page(dst);
    unmap_domain_page(src);
}

void destroy_ring_for_helper(
    void **_va, struct page_info *page)
{
    void *va = *_va;

    if ( va != NULL )
    {
        unmap_domain_page_global(va);
        put_page_and_type(page);
        *_va = NULL;
    }
}

int prepare_ring_for_helper(
    struct domain *d, unsigned long gmfn, struct page_info **_page,
    void **_va)
{
    struct page_info *page;
    p2m_type_t p2mt;
    void *va;

    page = get_page_from_gfn(d, gmfn, &p2mt, P2M_UNSHARE);

#ifdef CONFIG_HAS_MEM_PAGING
    if ( p2m_is_paging(p2mt) )
    {
        if ( page )
            put_page(page);
        p2m_mem_paging_populate(d, gmfn);
        return -ENOENT;
    }
#endif
#ifdef CONFIG_HAS_MEM_SHARING
    if ( p2m_is_shared(p2mt) )
    {
        if ( page )
            put_page(page);
        return -ENOENT;
    }
#endif

    if ( !page )
        return -EINVAL;

    if ( !get_page_type(page, PGT_writable_page) )
    {
        put_page(page);
        return -EINVAL;
    }

    va = __map_domain_page_global(page);
    if ( va == NULL )
    {
        put_page_and_type(page);
        return -ENOMEM;
    }

    *_va = va;
    *_page = page;

    return 0;
}

/*
 * Local variables:
 * mode: C
 * c-file-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */
