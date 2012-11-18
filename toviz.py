#
# Parse reified stuff and produce a Grphviz graph out of that 
# 
# python toviz.py foo.lp.reified > res.dot
#
import sys

squares = {}
diamonds = {}

ctr = 0

def handle(nm,rest):
    global ctr
    if nm == 'alist' or nm == 'tlist' or nm == 'altlist':
        print rest[0] + ' -> ' + rest[2] + ' [label = "' + nm + '_' + rest[1] + '"];'
    elif nm == 'var' or nm == 'pred' or nm == 'cnst':
        newnm = nm+str(ctr)
        print rest[0] + ' -> ' + newnm + ' [label = "' + nm + '"];'
        squares[newnm] = rest[1]
        ctr = ctr + 1
    elif nm == 'optimize' or nm == 'op' or nm == 'bop':
        newnm = nm+str(ctr)
        print rest[0] + ' -> ' + newnm + ' [label = "' + nm + '"];'
        diamonds[newnm] = rest[1]
        ctr = ctr + 1
    elif nm == 'pos' or nm == 'neg':
        print rest[0] + ' -> ' + rest[0] + ' [label = "' + nm + '"];'
    elif len(rest) > 2:
        print '# Urgh bad stuff', nm, rest 
    else:
        print rest[0] + ' -> ' + rest[1] + ' [label = "' + nm + '"];'

def handleline(i,nm):
    # print 'Handling', i
    try: 
        b = i.split('(')
        c = b[1].split(')')
        args = c[0].split(',')
        handle(b[0], args)
    except:
        # print 'Urgh'
        pass
    

if len(sys.argv) == 2:
    f = open(sys.argv[1])
    fname = sys.argv[1]
else:
    f = sys.stdin
    fname = 'stdin'

prefix = 'digraph reified_rules {\n label = "' + fname + '";\n node [shape=circle];\n'
postfix = "}"

print prefix

line = f.readline()
parsenext = None
while line != '':
    if line[0] == '%':
        pass
    elif line[0] == '#':
        pass
    else:
        handleline(line,parsenext)
    line = f.readline()

f.close()

for i in squares.keys():
    print i + ' [shape = box, label= ' + squares[i] + ' ];'

for i in diamonds.keys():
    print i + ' [shape = diamond, label= ' + diamonds[i] + ' ];'

print postfix

#EOF

