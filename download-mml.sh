#!/bin/sh
mkdir -p miz/zip
cd miz/zip
wget https://mizar.uwb.edu.pl/~softadm/pub/system/i386-win32/mizar-8.1.14_5.78.1462-i386-win32.exe -O mizar.exe
unzip mizar.exe
mkdir -p ../mizshare/mml ../mizshare/prel
cd ../mizshare/mml
unzip ../../zip/mmlfull.zip
cd ../prel
unzip ../../zip/prel.zip
cd ..
unzip ../zip/mizdb1.zip
rm -rf zip
patch -p0 < ../../mml.patch
