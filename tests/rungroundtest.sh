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

# If they diff, we'd stop with set -e 
set +e
r1=`diff -q $ifile.res ../../ref_ground_output/$ifile.res`
`sort $ifile.res > $ifile.res.srt`
`sort ../../ref_ground_output/$ifile.res > $ifile.res.ref.srt`
r2=`diff -q $ifile.res.srt $ifile.res.ref.srt`
set -e

# r2=`diff -s $ifile.res ../../ref_ground_output/$ifile.res`

if [ -n "$r2" ]; then 
  # It is an error 
  echo
  echo >&2 "FAIL $reified_src, files in $dname/output"
  echo >&2 "diff $dname/output/$ifile.res ref_ground_output/$ifile.res"
  echo >&2 "diff $dname/output/$ifile.res.srt $dname/output/$ifile.res.ref.srt"
  echo 
  #exit 1
else
  # This is a pass 
  cd ../..
  rm -fr $dname 
  echo
  if [ -n "$r1" ]; then 
      echo "PASS $reified_src (order differs)"
  else
      echo "PASS $reified_src"
  fi
  echo 
  #exit 0
fi

