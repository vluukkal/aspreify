#!/bin/sh 

set -e # stop on error 
START=$(date +%s)
STARTnano=$(date +%N)

metagrounder="/Users/vluukkal/src/aspreify/metaeval/metaground_aggregate.lp"
aspreify="/Users/vluukkal/src/aspreify/aspreify" 


while [ $# -gt 0 ]
do
    case "$1" in
	-m) metagrounder="$2"; shift;;
	-a) aspreify="$2"; shift;;
	-*) echo >&2 \
	    "usage: $0 [-m metagrounderfile] [file ...]"
	    exit 1;;
	*)  break;;	# terminate while loop
    esac
    shift
done

if [ $# -gt 0 ]; then 
    reified=$1
else 
    echo "Must have an input file"
    echo "usage: $0 [-m metagrounderfile] [file ...]"
    exit 1
fi 

mgname=$(basename "$metagrounder")
iname=$(basename "$reified")
aname=$(basename "$aspreify")

basefilename=${iname%%.*}

# Keep everything backed up in a directory named by the second 
# dname=`date +%m%d%Y_%H%M%S`
currdate=`date +%m%d%Y_%H%M%S`
dname="$basefilename$currdate" 

# Syntax check 
# gringo timedgrnd.lp > /dev/null
gringo provgrnd.lp > /dev/null

mkdir "$dname" 

echo "Processing in $dname"

mkdir "$dname/input"
mkdir "$dname/output"

mkdir "$dname/input/mg"
mkdir "$dname/input/ifile"
mkdir "$dname/input/ar"

mgcmd="$dname/input/mg/$mgname"
ifile="$dname/input/ifile/$iname"
ofile1="$iname"
aspcmd="$dname/input/ar/$aname"


# echo "cat metaground_basic_3.lp metaground_prop_3.lp metaground_fact_3.lp metaground_common_3.lp > $mgname"
# cat metaground_basic_3.lp metaground_prop_3.lp metaground_fact_3.lp metaground_common_3.lp > $mgname
# cat timedgrnd.lp > $mgname 
cat provgrnd.lp > $mgname 

cp $mgname $mgcmd
cp $reified $ifile
cp $aspreify $aspcmd

echo 

echo "cat $mgcmd $ifile > $dname/output/$ofile1"
cat $mgcmd $ifile > "$dname/output/$ofile1"
cd "$dname/output/"

#echo "time gringo $ofile1 | clasp --project -n 0 | python /Users/vluukkal/src/aspreify/smodelsres.py "
#time gringo $ofile1 | clasp --project -n 0 | python /Users/vluukkal/src/aspreify/smodelsres.py 
echo "time gringo $ofile1 | clasp --project | python /Users/vluukkal/src/aspreify/smodelsres.py "
time gringo $ofile1 | clasp --project | python /Users/vluukkal/src/aspreify/smodelsres.py 


#echo "time $aspreify +RTS -K128M -RTS -b $reified smres*.lp "
#time $aspreify +RTS -K128M -RTS -b $reified smres*.lp 

ofile1=smres1.lp
echo
echo "Intermediate results will appear in"
echo "less $dname/output/$ofile1"
echo 


# We can only hav one result for the current metagrounder. 
echo "time $aspreify +RTS -K128M -RTS -g smres1.lp "
time $aspreify +RTS -K128M -RTS -g smres1.lp


#echo "time for f in *.ground; do cat $f >> $ofile1.res;  echo $f; done"
#time for f in *.ground; do echo "% $f" >> $ofile1.res; cat $f >> $ofile1.res;  echo $f; done

END=$(date +%s)
ENDnano=$(date +%N)

DIFF=$(( (10#$END - 10#$START) * 1000000000 ))

#DIFFnano=$(( (10#$ENDnano - 10#$STARTnano)  ))

#DIFF=$(( 10#$DIFF + 10#$DIFFnano ))

DIFFu=$(( 10#$DIFF / 1000000000 )) # Get correct units
#DIFFd=$(( 10#$DIFF - 10#$DIFFu ))  # Get figures after decimal place

# echo "took ${DIFFu}.${DIFFd} seconds to finish." > TIMING
echo "took ${DIFFu} seconds to finish." > TIMING
echo "It took ${DIFFu} seconds to finish."
sz=$(du -h .)
echo "size $sz" > SIZE
echo "size $sz" 
echo "Results in $dname/output/$ofile1.ground"
echo "Results in $dname/output/$ofile1"
cp "$ofile1.ground" ../..
#EOF