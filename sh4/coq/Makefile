# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

FILES := Config Functions Proc State

VFILES := Sh4.v $(FILES:%=Sh4_%.v)

INCLUDES := -I $(DIR)/compcert/lib -I $(DIR)/coq

include $(DIR)/Makefile.coq
