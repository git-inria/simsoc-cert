# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ..

FILES := Bitvec Util Semantics Simul Extraction TypInfer Cnotations

VFILES := $(FILES:%=%.v)

include $(DIR)/Makefile.coq

extraction.v: default
