CAP ?= 256
SCHED ?= sched-fifo
ifneq ($(findstring sched,$(FEATURES) $(APP_FEATURES)),)
	SCHED := $(shell echo $(FEATURES) $(APP_FEATURES) | sed -n 's/.*\(sched-[^,]*\).*/\1/p')
endif

build_vsched:
	make -C ../vsched ARCH=$(ARCH) RQ_CAP=$(CAP) SMP=$(SMP) SCHED=$(SCHED) all
	mv ../vsched/libvsched.so vsched-axtask/.