CAP ?= 256
SCHED ?= sched-fifo
VSCHED ?= vsched-axtask/vsched
ifneq ($(findstring sched,$(FEATURES) $(APP_FEATURES)),)
	SCHED := $(shell echo $(FEATURES) $(APP_FEATURES) | sed -n 's/.*\(sched-[^,]*\).*/\1/p')
endif


build_vsched:
ifeq ($(wildcard $(VSCHED)),)
	@git clone https://github.com/AsyncModules/vsched.git $(VSCHED)
else
	@cd vsched-axtask/vsched && git pull
endif
	make -C $(VSCHED) ARCH=$(ARCH) RQ_CAP=$(CAP) SMP=$(SMP) SCHED=$(SCHED) all
	mv $(VSCHED)/libvsched.so vsched-axtask/.