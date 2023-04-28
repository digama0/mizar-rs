#!/bin/bash
# This is only needed for cross-checking exports against Mizar's output
if [ "$1" = "" ]; then
  if command -v parallel; then
    parallel --progress -a miz/mizshare/mml.lar ./transfer-mml.sh
  else
    for base in `cat miz/mizshare/mml.lar`; do
      ./transfer-mml.sh $base
    done
  fi
  for file in arithm.dre boole.dre hidden.dco hidden.dno \
    hidden.dre numerals.dre real.dre subset.dre \
    tarski_0.sch tarski_0.the tarski_a.the
  do
    cp miz/mizshare/prel/${file:0:1}/$file miz/prel/${file:0:1}/$file
  done
else
  cd miz
  MIZFILES=mizshare
  ../../src/kernel/transfer mizshare/mml/$1.miz -p > /dev/null
fi
