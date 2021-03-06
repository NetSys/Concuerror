###----------------------------------------------------------------------
### Copyright (c) 2011-2013, Alkis Gotovos <el3ctrologos@hotmail.com>,
###                          Maria Christakis <mchrista@softlab.ntua.gr>
###                      and Kostis Sagonas <kostis@cs.ntua.gr>.
### All rights reserved.
###
### This file is distributed under the Simplified BSD License.
### Details can be found in the LICENSE file.
###----------------------------------------------------------------------
### Authors     : Alkis Gotovos <el3ctrologos@hotmail.com>
###               Maria Christakis <mchrista@softlab.ntua.gr>
### Description : Main Makefile
###----------------------------------------------------------------------

all: compile

###----------------------------------------------------------------------
### Application info
###----------------------------------------------------------------------

VSN ?= 0.10

###----------------------------------------------------------------------
### Flags
###----------------------------------------------------------------------

ERL_COMPILE_FLAGS ?= \
	+debug_info \
	+warn_export_vars \
	+warn_unused_import \
	+warn_missing_spec \
	+warn_untyped_record

DIALYZER_FLAGS = -Wunmatched_returns

###----------------------------------------------------------------------
### Targets
###----------------------------------------------------------------------

MODULES = \
	concuerror_callback \
	concuerror_dependencies \
	concuerror_inspect \
	concuerror_instrumenter \
	concuerror_loader \
	concuerror_logger \
	concuerror_options \
	concuerror_printer \
	concuerror_scheduler \
	concuerror

vpath %.erl src

.PHONY: clean compile cover dialyze submodules tests tests-all tests-long

compile: $(MODULES:%=ebin/%.beam) getopt concuerror

dev:
	$(MAKE) VSN="$(VSN)d" \
	ERL_COMPILE_FLAGS="$(ERL_COMPILE_FLAGS) -DDEV=true +nowarn_deprecated_type +warnings_as_errors"

ifneq ($(MAKECMDGOALS),clean)
-include $(MODULES:%=ebin/%.Pbeam)
endif

ebin/%.Pbeam: %.erl | ebin
	erlc -o ebin -I include -MD $<

ebin/%.beam: %.erl Makefile | ebin
	erlc $(ERL_COMPILE_FLAGS) -I include -DVSN="\"$(VSN)\"" -o ebin $<

concuerror:
	ln -s src/concuerror $@

getopt: submodules
	$(MAKE) -C deps/getopt

submodules:
	git submodule update --init

clean:
	rm -f concuerror
	rm -rf ebin cover-data
	rm -f tests*/scenarios.beam

dialyze: all .concuerror_plt
	dialyzer --plt .concuerror_plt $(DIALYZER_FLAGS) ebin/*.beam

.concuerror_plt: | getopt
	dialyzer --build_plt --output_plt $@ --apps erts kernel stdlib compiler \
	deps/*/ebin/*.beam

###----------------------------------------------------------------------
### Testing
###----------------------------------------------------------------------

%/scenarios.beam: %/scenarios.erl
	erlc -o $(@D) $<

SUITES = {advanced_tests,dpor_tests,basic_tests}

tests: all tests/scenarios.beam
	@(cd tests; bash -c "./runtests.py suites/$(SUITES)/src/*")

tests-long:
	$(MAKE) -C tests-long CONCUERROR=$(abspath concuerror) DIFFER=$(abspath tests/differ)

tests-all: tests tests-long

###----------------------------------------------------------------------

cover: cover-data
	export COVER=true; $(MAKE) tests-all
	tests/cover-report

###----------------------------------------------------------------------

ebin cover-data:
	mkdir $@

