include ../../Makefile

include ../Makefile.include  # Sets necessary variables to use send layer

APP_FILES=BA.Messages BA.Sessions BA.Preds BA.Labeled.SerializingParsing BA.Protocol BA.Debug
APP_FST_FILES=$(addsuffix .fst,$(APP_FILES))
APP_CMX_FILES=$(addprefix ocaml-symbolic/,$(addsuffix .cmx,$(subst .,_,$(APP_FILES))))

ALL_FST_FILES=$(LIB_BASE_FST_FILES) $(APP_BASE_FST_FILES) $(LIB_FST_FILES) $(APP_FST_FILES)
ALL_CMX_FILES=$(LIB_BASE_CMX_FILES) $(APP_BASE_CMX_FILES) $(LIB_CMX_FILES) $(APP_CMX_FILES)

extract: $(ALL_FST_FILES) $(ALL_CMX_FILES)
test: $(ALL_FST_FILES) $(ALL_CMX_FILES) ocaml-symbolic/test.exe

ocaml-symbolic/test.exe: $(ALL_CMX_FILES)
	$(OCAMLOPT) $^ -o $@
