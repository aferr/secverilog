mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir := $(dir $(mkfile_path))

VDIR=$(mkfile_dir)/verilog-0.9.6
TDIR=$(mkfile_dir)/test
INSTALLDIR?=$(mkfile_dir)

build: $(VDIR)/conf.done
	@$(MAKE) -C $(VDIR)

$(VDIR)/configure:
	@cd $(VDIR) && autoconf

$(VDIR)/conf.done: $(VDIR)/configure
	@cd $(VDIR) && ./configure --prefix=$(INSTALLDIR) && touch conf.done

install: build
	@$(MAKE) -C $(VDIR) install

test: install
	@$(MAKE) -C $(TDIR)

clean:
	@$(MAKE) -C $(VDIR) clean

