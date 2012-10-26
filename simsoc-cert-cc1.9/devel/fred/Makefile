# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

FILES := add

VFILES := $(FILES:%=%.v)

COQ_INCLUDES := -I $(DIR)/coq

include $(DIR)/Makefile.common

default: add.vo

add.vo: libcoq
