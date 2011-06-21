#!/bin/bash
tar czvfh simsoc-cert.tar.gz --exclude-vcs simsoc-cert

# cd simsoc-cert
# less INSTALL
# ./configure /path/to/compcert 

# make -C arm6/coq
# less arm6/coq/Arm6_Inst.v

# make -C arm6/simlight all.vo
# less arm6/simlight/all.v

# cd equiv_proof_adc && ./make.sh && echo 'The equivalence proof has been typed.'
