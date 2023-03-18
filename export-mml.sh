#!/bin/sh
# This is only needed for cross-checking exports against Mizar's output
MIZFILES=miz/mizshare
if [ "$1" = "" ]; then
  if command -v parallel; then
    parallel --progress -a miz/mizshare/mml.lar ./export-mml.sh
  else
    for base in `cat miz/mizshare/mml.lar`; do
      ./export-mml.sh $base
    done
  fi
else
  miz/mizbin/exporter miz/mizshare/mml/$1.miz > /dev/null
fi
