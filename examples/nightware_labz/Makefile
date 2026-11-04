ROOT_DIR ?= ../..
KRELLC   ?= $(ROOT_DIR)/krellc
CC       ?= cc
CFLAGS   ?= -O3 -Wall -Wextra

all: nightware_labz nightware_labz.s nightware_labz.krel

$(KRELLC):
	$(MAKE) -C $(ROOT_DIR) krellc

nightware_labz.ll: nightware_labz.krell $(KRELLC)
	$(KRELLC) build nightware_labz.krell --target llvm -o $@

nightware_labz.s: nightware_labz.krell $(KRELLC)
	$(KRELLC) build nightware_labz.krell --target x86_64 -o $@

nightware_labz.krel: nightware_labz.krell $(KRELLC)
	$(KRELLC) parse nightware_labz.krell -o $@

nightware_labz: nightware_labz.ll kc_shim.c
	$(CC) $(CFLAGS) nightware_labz.ll kc_shim.c -lm -o $@

demo: nightware_labz
	./run_demo.sh

clean:
	rm -f nightware_labz nightware_labz.ll nightware_labz.s nightware_labz.krel

.PHONY: all demo clean
