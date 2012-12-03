#
# Parse smodels result lines and output them 
# line by line as facts.
# Outputs files named smresX.lp, e.g smres1.lp, smres2.lp
# 
# python smodelsres.py res.txt 
# lparse foo.lp | smodels | python smodelsres.py 
#
import sys

def handleline(i,nm):
    global nodehash 
    outf = open('smres'+ nm +'.lp', 'w')

    atoms = i.split(' ')
    for z in atoms:
        if not (z == 'Stable' or z == 'Model:'):
            if z.strip() != '':
                outf.write(z + '.\n')

    outf.close()
    # raw_input()

if len(sys.argv) == 2:
    f = open(sys.argv[1])
else:
    f = sys.stdin

line = f.readline()
parsenext = None
while line != '':
    res = line.split('Answer: ')
    if len(res) == 2:
        parsenext = res[1].strip()
    elif parsenext != None:
        print 'parsing answer ' + parsenext + ' to file smres' + parsenext + '.lp'
        handleline(line,parsenext)
        parsenext = None
    line = f.readline()

f.close()

#EOF

