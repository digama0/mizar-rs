#!/bin/sh
DEP_ORDER=1 XML_EXPORT=1 NO_ANALYZER=1 NO_CHECKER=1 cargo run --release
echo 'copying prel/ files to mizshare/prel/'
cp -r miz/prel/* miz/mizshare/prel/
rm -rf miz/prel
