# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

DIR := ../..

FILES := adc_compcert bl_compcert ldrb_compcert mrs_compcert setend_compcert type_slv6_proc projection my_inversion my_tactic common_functions correctness_ADC correctness_BL correctness_LDRB correctness_MRS correctness_SETEND

VFILES := $(FILES:%=%.v)

COQ_INCLUDES := -I $(DIR)/coq -I $(DIR)/compcert/lib -I $(DIR)/compcert/common -I $(DIR)/compcert/cfrontend -I $(DIR)/arm6/coq

include $(DIR)/Makefile.common

default: all.vo

all.vo: libcoq
