#!/bin/sh

# SimSoC-Cert, a Coq library on processor architectures for embedded systems.
# See the COPYRIGHTS and LICENSE files.

# 2010-06-29 Frederic Blanqui

prog=`basename $0`

usage () { echo "usage: $prog [-h] file.v"; }

help () {
  cat <<EOF
Generate file.ml from file.v by using Coq extraction mechanism,
assuming that file.vo exists.

Options:
-h Provide this help and exit
EOF
}

args () { echo 'error: wrong number of arguments'; usage; exit 1; }

case "$1" in
-h) usage; echo; help; exit 0;;
esac

if test $# -ne 1; then args; fi

case $1 in
*.v) ;;
*) echo 'error: wrong file extension'; exit 1;;
esac

base=`basename $1 .v`
tmp=/tmp/extract_$base.v
echo "Require Extraction $base. Extraction Library $base." > $tmp
coqc -q -I ../compcert/lib -R ../coq SimSoCCert -I ../arm6 $tmp
