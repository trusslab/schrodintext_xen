XEN_ROOT = $(CURDIR)/../../..
include $(XEN_ROOT)/tools/Rules.mk

# Xen script dir and scripts to go there.
XEN_SCRIPTS =
XEN_SCRIPTS += block
XEN_SCRIPTS += vif-bridge
XEN_SCRIPTS += vif-ip

XEN_SCRIPT_DATA =
XEN_RCD_PROG = rc.d/xencommons rc.d/xendomains rc.d/xen-watchdog rc.d/xendriverdomain

.PHONY: all
all:

.PHONY: build
build:

.PHONY: install
install: install-scripts install-rcd

.PHONY: uninstall
uninstall: uninstall-scripts uninstall-rcd

.PHONY: install-scripts
install-scripts:
	$(INSTALL_DIR) $(DESTDIR)$(XEN_SCRIPT_DIR)
	set -e; for i in $(XEN_SCRIPTS); \
	   do \
	   $(INSTALL_PROG) $$i $(DESTDIR)$(XEN_SCRIPT_DIR); \
	done
	set -e; for i in $(XEN_SCRIPT_DATA); \
	   do \
	   $(INSTALL_DATA) $$i $(DESTDIR)$(XEN_SCRIPT_DIR); \
	done

.PHONY: uninstall-scripts
uninstall-scripts:
	rm -f $(addprefix $(DESTDIR)$(XEN_SCRIPT_DIR)/, $(XEN_SCRIPTS))
	rm -f $(addprefix $(DESTDIR)$(XEN_SCRIPT_DIR)/, $(XEN_SCRIPT_DATA))

.PHONY: install-rcd
install-rcd:
	$(INSTALL_DIR) $(DESTDIR)$(INITD_DIR)
	set -e; for i in $(XEN_RCD_PROG); \
	   do \
	   $(INSTALL_PROG) $$i $(DESTDIR)$(INITD_DIR); \
	done
	$(INSTALL_DATA) ../common/hotplugpath.sh $(DESTDIR)$(INITD_DIR)/xen-hotplugpath.sh

.PHONY: uninstall-rcd
uninstall-rcd:
	rm -f $(subst rc.d,$(DESTDIR)$(INITD_DIR),$(XEN_RCD_PROG))
	rm -f $(DESTDIR)$(INITD_DIR)/xen-hotplugpath.sh

.PHONY: clean
clean:

.PHONY: distclean
distclean: clean
