#!/bin/sh

# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

set -e

VERSION=2014
test -d simsoc-cert.$VERSION && echo "Remove manually the directory simsoc-cert.$VERSION" && exit 1
test -f simsoc-cert.$VERSION.tar.gz && echo "Remove manually the file simsoc-cert.$VERSION.tar.gz" && exit 1
test -z $1 && echo "usage : $0 <svn username to checkout>" && exit 1
USER=$1

set -x

#############################################
# we clone

svn checkout svn+ssh://$USER@scm.gforge.inria.fr/svnroot/simsoc-cert -r $VERSION simsoc-cert.$VERSION

#############################################
# we enter

cd simsoc-cert.$VERSION

#############################################
# we remove

rm arm6/arm6.pdf
rm sh4/sh4.pdf
rm -rf arm7
rm -rf coq/coq-bugs 

mv devel/tuong . && rm -rf devel/* && mv tuong devel
rm devel/tuong/* || true

rm -rf papers
rm $(find . -name TODO)
rm README.devel

#############################################
# we exit

cd ..

#############################################
# we back up

tar czvfh simsoc-cert.$VERSION.tar.gz --exclude-vcs simsoc-cert.$VERSION

#############################################
