#!/bin/sh
# disable the multi progress bar because it goes too fast and looks noisy
cargo run --release -- -dex --no-multi-progress
echo 'copying prel/ files to mizshare/prel/'
cp -r miz/prel/* miz/mizshare/prel/
rm -rf miz/prel
