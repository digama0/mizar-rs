#!/bin/sh
cp mml-orig/*.miz miz/mizshare/mml/
cd miz/mizshare
patch -p0 < ../../mml.patch

