#!/bin/sh
sed -e 's/  */ /g' -e '/^ [A-Z]/s/ \([^ ]*\) / \1	/'
