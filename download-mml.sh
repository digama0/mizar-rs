#!/bin/sh
mkdir -p miz
cd miz
wget http://mizar.uwb.edu.pl/~softadm/current/mizar-8.1.11_5.68.1412-i386-linux.tar -O - \
  | tar -x
for i in mizbin mizdoc mizshare; do
  mkdir -p $i
  cd $i && tar -xzf ../$i.tar.gz && cd ..
  rm $i.tar.gz
done
cd mizshare/mml
patch < ../../../mml.patch
# for i in \
#   realset1 seqfunc limfunc4 sin_cos6 fdiff_4 fdiff_6 fdiff_7 fdiff_8 \
#   fdiff_9 fdiff_10 sin_cos9 integr12 integr13 integr14 complsp1 decomp_1 \
#   jordan1d fdiff_11 tops_4 ltlaxio2 lagra4sq hilb10_5 complex1 binari_2 \
#   l_hospit comptrig complex2 prgcor_1 gobrd12 gobrd13 matrixc1 pdiff_3 funct_9 \
#   euclid_8 pdiff_5 menelaus scmfsa_x scmfsa8b scmfsa8c scmfsa_9 sfmastr3 \
#   scmpds_6 scmpds_7 diophan2 hilb10_4 fuzzy_5
# do
#   echo patching $i
#   sed -i "s/requirements /requirements BOOLE, /g" $i.miz
# done
