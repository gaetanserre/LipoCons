set -x

rm -rf doc _out
lake exe manual
mkdir doc
mv _out/html-multi/* doc/
rm -rf _out
mkdir -p doc/static
cp verso_manual/static_files/* doc/static