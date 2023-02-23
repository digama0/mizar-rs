#!/bin/sh
MIZFILES=miz/mizshare
if [ "$1" = "" ]; then
  if command -v parallel; then
    parallel --progress -a miz/mizshare/mml.lar ./analyze-mml.sh
  else
    for base in `cat miz/mizshare/mml.lar`; do
      ./analyze-mml.sh $base
    done
  fi
else
  miz/mizbin/accom miz/mizshare/mml/$1.miz > /dev/null
  miz/mizbin/verifier -a miz/mizshare/mml/$1.miz > /dev/null
fi
