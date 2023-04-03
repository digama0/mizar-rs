#!/bin/sh
MIZFILES=miz/mizshare
if [ "$1" = "" ]; then
  # use original mizar to parse everything
  if command -v parallel; then
    parallel --progress -a miz/mizshare/mml.lar ./analyze-mml.sh
  else
    for base in `cat miz/mizshare/mml.lar`; do
      ./analyze-mml.sh $base
    done
  fi
  # use mizar-rs to generate prel files
  DEP_ORDER=1 XML_EXPORT=1 NO_ANALYZER=1 NO_CHECKER=1 cargo run --release
  cp -r miz/prel/* miz/mizshare/prel/
  rm -rf miz/prel
else
  miz/mizbin/accom miz/mizshare/mml/$1.miz > /dev/null || exit 1
  miz/mizbin/verifier -p miz/mizshare/mml/$1.miz > /dev/null || exit 1
fi
