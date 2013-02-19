#!/bin/sh

# Run a single test in given at commandline, compare to results 
# in ./ref_output/ and report differences. 
# We expect to be run in tests/ subdirectory of aspreify

set -e # stop on error 
metagrounder="../../../metaeval/metaground_3.lp"
aspreify="../../../aspreify"
smres="../../../smodelsres.py"

reified_src=$1
mgname=$(basename "$metagrounder")
iname=$(basename "$reified_src")
aname=$(basename "$aspreify")

basefilename=${iname%%.*}
currdate=`date +%m%d%Y_%H%M%S`
dname="$basefilename$currdate" 

# Create a directory to work in 
mkdir "$dname" 
mkdir "$dname/output"

cp $reified_src "$dname/output/"

mgcmd="../../$metagrounder"
ifile="$iname.reified"
ofile1="$iname.wrk" 
aspcmd="../../$aname"

cd "$dname/output/"

# Do the actual grounding 

# Reify the source 
$aspreify $iname 

# Combine with metagrounder
cat $metagrounder $ifile > $ofile1

# Calculate the groundings
gringo $ofile1 | clasp --project -n 0 | python $smres 
# Read them back in to produce the ground rules 
$aspreify -b $ifile smres*.lp 
# Combine the individual ground rules 
for f in *.ground; do echo "% $f" >> $ifile.res; cat $f >> $ifile.res; done

r1=`diff -q $ifile.res ../../ref_ground_output/$ifile.res`
# r2=`diff -s $ifile.res ../../ref_ground_output/$ifile.res`

if [ -n "$r1" ]; then 
  # It is an error 
  echo
  echo "FAIL $reified_src, files in $dname"
  exit 1
else
  # This is a pass 
  cd ../..
  rm -fr $dname 
  echo
  echo "PASS $reified_src"
  exit 0
fi

