#!/bin/bash
for file in arithm.dre boole.dre hidden.dco hidden.dno \
  hidden.dre numerals.dre real.dre subset.dre \
  tarski_0.sch tarski_0.the tarski_a.the
do
  mkdir -p prel-orig/${file:0:1}
  cp miz/mizshare/prel/${file:0:1}/$file prel-orig/${file:0:1}/$file
done
