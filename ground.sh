#!/bin/sh

# Perform metagrounding. 
# We expect to be run in same directory as the aspreify itself

set -e # stop on error 

deb=""

while [ $# -gt 0 ]
do
    case "$1" in
        -d) deb="yes";;
        -*) echo >&2 \
            "usage: $0 [-d] rulefile.lp"
            exit 1;;
        *)  break;;     # terminate while loop
    esac
    shift
done

if [ $# -gt 0 ]; then 
    reified_src=$1
else 
    echo >&2 "Must have an input file"
    echo >&2 "usage: $0 [-d] rulefile.lp"
    exit 1
fi 



metagrounder="../../metaeval/metaground_3.lp"
aspreify="../../aspreify"
smres="../../smodelsres.py"

# reified_src=$1
mgname=$(basename "$metagrounder")
iname=$(basename "$reified_src")
aname=$(basename "$aspreify")

basefilename=${iname%%.*}
currdate=`date +%m%d%Y_%H%M%S`
dname="$basefilename$currdate" 

echo "Working in $dname"
# Create a directory to work in 
mkdir "$dname" 
mkdir "$dname/output"

cp $reified_src "$dname/output/"

ifile="$iname.reified"
ofile1="$iname.wrk" 

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

cp $ifile.res ../..

cd ../..
if [ "$deb" == "" ] 
then 
  rm -fr $dname 
  echo "Result in $ifile.res"
else 
  echo "Results in $dname/output"
fi

