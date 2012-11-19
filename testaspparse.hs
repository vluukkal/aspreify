--
-- HUnit tests for the parser 
-- 
-- Create an executable
-- > ghc -o runparsertests testaspparse.hs aspparse.hs
-- > ./runparsertests 
-- 
-- Or in the interpreter:
-- ghci> :l testaspparse.hs 
-- ghci> runTestTT tests
-- 
-- 
-- Copyright 2012 Vesa Luukkala
-- 
-- Permission is hereby granted, free of charge, to any person obtaining
-- a copy of this software and associated documentation files (the
-- "Software"), to deal in the Software without restriction, including
-- without limitation the rights to use, copy, modify, merge, publish,
-- distribute, sublicense, and/or sell copies of the Software, and to
-- permit persons to whom the Software is furnished to do so, subject to
-- the following conditions:
-- 
-- The above copyright notice and this permission notice shall be
-- included in all copies or substantial portions of the Software.
-- 
-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
-- EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
-- MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
-- NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
-- LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
-- OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
-- WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-- 

import qualified Data.List as List
import qualified Data.Map as Map
import System.IO.Unsafe
import Data.IORef 
import Text.ParserCombinators.Parsec

import AspParse

import Test.HUnit


{--
parse ruleorfact "" "k { in(X) : vtx(X) }.\n"
Right (Fact [Card (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "in") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "X")] True]] True])
--}

-- We'd like to do this, but we get 
-- No instance for (Eq ParseError)
-- See http://www.haskell.org/pipermail/libraries/2008-September/010655.html
-- for one solution to add the Eqs to parsec types
--truleorfact1 = TestCase $ assertEqual "ruleorfact 1" (Right (Fact [Card (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "in") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "X")] True]] True]))
-- (parse ruleorfact "" "k { in(X) : vtx(X) }.\n")

-- We cheat a bit and unwrap the error as a valid, but in practice neverseen value 
-- of right type. 
wrapparser p a1 a2 = 
    case (parse p a1 a2) of 
    Right r -> r 
    Left l -> (Fact [])

-- The return type should be [Rules], rather than above. 
-- Is this a problem in the types?
wrapparser' p a1 a2 = 
    case (parse p a1 a2) of 
    Right r -> r 
    Left l -> ([Fact []])

-- The return type should be [Body], rather than above. 
wrapparser_bl p a1 a2 = 
    case (parse p a1 a2) of 
    Right r -> r 
    Left l -> ([Empty])

-- The return type should be [Body], rather than above. 
wrapparser_bl' p a1 a2 = 
    case (parse p a1 a2) of 
    Right r -> r 
    Left l -> Empty

wrapparser_exp p a1 a2 = 
    case (parse p a1 a2) of 
    Right r -> r 
    Left l -> Sym (Const "Erroneous MyExpr")

wrapparser_exp' p a1 a2 = 
    case (parse p a1 a2) of 
    Right r -> r 
    Left l -> [Sym (Const "Erroneous MyExpr")]

wrapparser_atom p a1 a2 = 
    case (parse p a1 a2) of 
    Right r -> r 
    Left l -> (Const "Erroneous Atom")


truleorfact1 = TestCase $ assertEqual "ruleorfact 1" (Fact [Card (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "in") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "X")] True]] True]) (wrapparser ruleorfact "" "k { in(X) : vtx(X) }.\n")

truleorfact2 = TestCase $ assertEqual "ruleorfact 2" (Rule (Plain (Const "a") [Sym (Var "X"),Sym (Var "Y")] True) [Plain (Const "in") [Sym (Var "X")] True,Plain (Const "in") [Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y")] False,Plain (Const "vtx") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "Y")] True]) (wrapparser ruleorfact "" "a(X,Y) :- in(X), in(Y), not arc(X, Y), vtx(X), vtx(Y).\n")

trulebase1 = TestCase $ assertEqual "rulebase 1" [Deny [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True]] (wrapparser' rulebase "" ":-  blab(Baa),\n bii.")

trulebase2 = TestCase $ assertEqual "rulebase 2" [Fact [Card (Sym (Const "any")) (Sym (Const "any")) [Typed [Plain (Const "true") [Sym (Var "A")] True,Plain (Const "atom") [Sym (Var "A")] True]] True]] (wrapparser' rulebase "" "{ true(A) : atom(A) }.")

trulebase3 = TestCase $ assertEqual "rulebase 3" [Rule (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True]] (wrapparser' rulebase "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.")

trulebase4 = TestCase $ assertEqual "rulebase 4" [Rule (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True],Deny [Plain (Const "zuu") [Sym (Var "Zaa")] True,Plain (Const "zii") [] True]] (wrapparser' rulebase "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.\n\n:-  zuu(Zaa),\n zii.")

trulebase5 = TestCase $ assertEqual "rulebase 5" [Rule (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True],Deny [Plain (Const "zuu") [Sym (Var "Zaa")] True,Plain (Const "zii") [] True]] (wrapparser' rulebase "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.:-  zuu(Zaa),\n zii.")

trulebase6 = TestCase $ assertEqual "rulebase 6" [Deny [Plain (Const "zuu") [Sym (Var "Zaa")] True,Plain (Const "zii") [] True],Rule (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True]] (wrapparser' rulebase "" "\n:-  zuu(Zaa),\n zii.blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.\n")

trulebase7 = TestCase $ assertEqual "rulebase 7" [Rule (Plain (Const "p") [Sym (Var "X")] True) [Plain (Const "q") [Sym (Var "X")] True,Plain (Const "d") [Sym (Var "X")] True]] (wrapparser' rulebase "" "p(X) :- q(X), d(X).\n")

trulebase8 = TestCase $ assertEqual "rulebase 8" [Rule (Plain (Const "ready") [Sym (Var "A")] True) [Plain (Const "rdftype") [Sym (Var "A"),Sym (Const "\"wp1:Activity\"")] True,Plain (Const "missing_commit") [Sym (Var "A")] False]] (wrapparser' rulebase "" "ready(A) :- rdftype(A,\"wp1:Activity\"), not missing_commit(A).")

trulebase9 = TestCase $ assertEqual "rulebase 9" [Rule (Plain (Const "ready") [Sym (Var "A")] True) [Plain (Const "rdftype") [Sym (Var "A"),Sym (Const "\"wp1:Activity\"")] True,Plain (Const "missing_commit") [Sym (Var "A")] False],Rule (Plain (Const "missing_commit") [Sym (Var "A")] True) [Plain (Const "\"rdf:type\"") [Sym (Var "A"),Sym (Const "\"wp1:Activity\"")] True,Plain (Const "\"wp1:uses\"") [Sym (Var "A"),Sym (Var "Cap")] True,Plain (Const "\"wp1:commits\"") [Sym (Var "Cap"),Sym (Var "A")] False]] (wrapparser' rulebase "" "ready(A) :- rdftype(A,\"wp1:Activity\"), not missing_commit(A).\n\nmissing_commit(A) :- \n    \"rdf:type\"(A,\"wp1:Activity\"),\n    \"wp1:uses\"(A,Cap),\n    not \"wp1:commits\"(Cap,A).\n ")

trulebase10 = TestCase $ assertEqual "rulebase 10" [Show [Plain (Const "deadlock") [Sym (Var "_")] True],Show [Plain (Const "conflict") [Sym (Var "_"),Sym (Var "_"),Sym (Var "_")] True],Show [Plain (Const "banish") [Sym (Var "_")] True]] (wrapparser' rulebase "" "show deadlock(_).\nshow conflict(_,_,_).\nshow banish(_).")

trulebase11 = TestCase $ assertEqual "rulebase 11" [Rule (Plain (Const "ready") [Sym (Var "A")] True) [Plain (Const "rdftype") [Sym (Var "A"),Sym (Const "\"wp1:Activity\"")] True,Plain (Const "missing_commit") [Sym (Var "A")] False],Rule (Plain (Const "missing_commit") [Sym (Var "A")] True) [Plain (Const "\"rdf:type\"") [Sym (Var "A"),Sym (Const "\"wp1:Activity\"")] True,Plain (Const "\"wp1:uses\"") [Sym (Var "A"),Sym (Var "Cap")] True,Plain (Const "\"wp1:commits\"") [Sym (Var "Cap"),Sym (Var "A")] False],Show [Plain (Const "deadlock") [Sym (Var "_")] True],Show [Plain (Const "conflict") [Sym (Var "_"),Sym (Var "_"),Sym (Var "_")] True],Show [Plain (Const "banish") [Sym (Var "_")] True]] (wrapparser' rulebase "" "ready(A) :- rdftype(A,\"wp1:Activity\"), not missing_commit(A).\n\nmissing_commit(A) :- \n    \"rdf:type\"(A,\"wp1:Activity\"),\n    \"wp1:uses\"(A,Cap),\n    not \"wp1:commits\"(Cap,A).\nshow deadlock(_).\nshow conflict(_,_,_).\nshow banish(_).")

-- Here we lose information, the actual error message is not passed. 
-- Could wrap it as a string inside a fact, but yuk ...
trulebase12 = TestCase $ assertEqual "rulebase 12" ([Fact []]) (wrapparser' rulebase "" "ready(A :- \"rdf:type\"(A,\"wp1:Activity\"), not missing_commit(A).")

trulebase13 = TestCase $ assertEqual "rulebase 13" ([Fact []]) (wrapparser' rulebase "" "ready(A) :- \"rdf:type\" A,\"wp1:Activity\"), not missing_commit(A).")

trulebase14 = TestCase $ assertEqual "rulebase 14" [Fact [Card (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "in") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "X")] True]] True],Deny [Plain (Const "in") [Sym (Var "X")] True,Plain (Const "in") [Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y")] False,Plain (Const "vtx") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "Y")] True]] (wrapparser' rulebase "" "k { in(X) : vtx(X) }.\n:- in(X), in(Y), not arc(X, Y), vtx(X), vtx(Y).\n")

trulebase15 = TestCase $ assertEqual "rulebase 15" [Consts [Assign (Const "k") (Number (Const "10"))]]
 (wrapparser' rulebase "" "const k = 10.")

tconstdef1 = TestCase $ assertEqual "constdef 1" (Consts [Assign (Const "k") (Number (Const "10"))]) (wrapparser constdef "" "const k = 10.")

tfact1 = TestCase $ assertEqual "fact 1" (Fact [Plain (Const "waitingfor") [Sym (Var "_"),Sym (Var "_")] True]) (wrapparser fact "" "waitingfor(_,_).")

tfact2 = TestCase $ assertEqual "fact 2"  (Fact [Plain (Const "waitingfor") [Sym (Var "X"),Sym (Var "Y")] True]) (wrapparser fact "" "waitingfor(X,Y).")


tdeny1 = TestCase $ assertEqual "deny 1" (Deny [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True]) (wrapparser deny "" ":-  blab(Baa), bii.")

tdeny2 = TestCase $ assertEqual "deny 2" (Deny [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True])  (wrapparser deny "" ":-  blab(Baa),\n bii.")

tdeny3 = TestCase $ assertEqual "deny 3" (Deny [Card (Sym (Const "any")) (Arith Minus (Sym (Const "k")) (Number (Const "1"))) [Typed [Plain (Const "sat") [Sym (Var "C")] True,Plain (Const "clause") [Sym (Var "C")] True]] True]) (wrapparser deny "" ":- {  sat(C) : clause(C) } k-1.")

tdeny4 = TestCase $ assertEqual "deny 4" (Deny [Plain (Const "vtx") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "Y")] True,BExpr Lt (Sym (Var "X")) (Sym (Var "Y")),Plain (Const "r") [Sym (Var "X"),Sym (Var "Y")] False]) (wrapparser deny "" ":- vtx(X), vtx(Y), X < Y, not r(X, Y).")

tdeny5 = TestCase $ assertEqual "deny 5" (Deny [Plain (Const "ok") [] False]) (wrapparser deny "" ":- not ok.")

tdeny6 = TestCase $ assertEqual "deny 6" (Deny [Plain (Const "vtx") [Sym (Var "X")] True,Plain (Const "occurs") [Sym (Var "X")] True,Plain (Const "r") [Sym (Var "X")] False]) (wrapparser deny "" ":- vtx(X), occurs(X), not r(X).")

trule1 = TestCase $ assertEqual "rule 1" (Rule (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True]) (wrapparser rule "" "blub(Foo,Bar,Goo) :-  blab(Baa), bii.")

trule2 = TestCase $ assertEqual "rule 2" (Rule (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True]) (wrapparser rule "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.")

-- trule3 = TestCase $ assertEqual "rule 3" (Rule (Plain (Const "ok") [] True) [Count (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)]] True]) (wrapparser rule "" "ok :- k [ lc(X, Y) : arc(X, Y, L) = L ] .")
trule3 = TestCase $ assertEqual "rule 3" (Rule (Plain (Const "ok") [] True) [Count (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True]] True]) (wrapparser rule "" "ok :- k [ lc(X, Y) : arc(X, Y, L) = L ] .")

trule4 = TestCase $ assertEqual "rule 4" (Rule (Plain (Const "initial") [Sym (Var "X")] True) [Plain (Const "occurs") [Sym (Var "X")] True,Typed [Plain (Const "occurs") [Sym (Var "Y")] False,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))],Plain (Const "vtx") [Sym (Var "X")] True]) (wrapparser rule "" "initial(X) :- occurs(X), not occurs(Y) : Y < X, vtx(X).")

trule5 = TestCase $ assertEqual "rule 5" (Rule (Card (Sym (Const "any")) (Number (Const "1")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True]] True) [Plain (Const "vtx") [Sym (Var "X")] True]) (wrapparser rule "" "{ lc(X, Y) : arc(X, Y, L) } 1 :- vtx(X)." )

trule6 = TestCase $ assertEqual "rule 6" (Rule (Plain (Const "occurs") [Sym (Var "X")] True) [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True]) (wrapparser rule "" "occurs(X) :- lc(X, Y), arc(X, Y, L).")

trule7 = TestCase $ assertEqual "rule 7" (Rule (Plain (Const "initial") [Sym (Var "X")] True) [Plain (Const "occurs") [Sym (Var "X")] True,Typed [Plain (Const "occurs") [Sym (Var "Y")] False,Plain (Const "vtx") [Sym (Var "X")] True,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))],Plain (Const "vtx") [Sym (Var "X")] True]) (wrapparser rule "" "initial(X) :- occurs(X), not occurs(Y) : vtx(X) : Y < X, vtx(X).")

trule8 = TestCase $ assertEqual "rule 8" (Rule (Plain (Const "r") [Sym (Var "Y")] True) [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Plain (Const "initial") [Sym (Var "X")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True]) (wrapparser rule "" "r(Y) :- lc(X, Y), initial(X), arc(X, Y, L).")

trule9 = TestCase $ assertEqual "rule 9" (Rule (Plain (Const "r") [Sym (Var "Y")] True) [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Plain (Const "r") [Sym (Var "X")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True]) (wrapparser rule "" "r(Y) :- lc(X, Y), r(X), arc(X, Y, L).")

trule10 = TestCase $ assertEqual "rule 10" (Fact []) (wrapparser rule "" "denied(X,Y).")

trule11 = TestCase $ assertEqual "rule 11" (Rule (Card (Number (Const "1")) (Sym (Const "any")) [Plain (Const "p") [Sym (Var "X")] True,Plain (Const "t") [Sym (Var "X")] True] True) [Card (Number (Const "1")) (Number (Const "2")) [Plain (Const "r") [Sym (Var "X")] True,Plain (Const "s") [Sym (Var "X")] True,Plain (Const "t") [Sym (Var "X")] False] True]) (wrapparser rule "" "1 { p(X), t(X) } :- 1 {r(X), s(X), not t(X)} 2.")

trule12 = TestCase $ assertEqual "rule 12"  (Rule (Card (Number (Const "1")) (Sym (Const "any")) [Plain (Const "p") [] True,Plain (Const "t") [] True] True) [Card (Number (Const "1")) (Number (Const "2")) [Plain (Const "r") [] True,Plain (Const "s") [] True,Plain (Const "t") [] False] True]) (wrapparser rule "" "1 { p, t } :- 1 {r, s, not t} 2.")

trule13 = TestCase $ assertEqual "rule 13" (Rule (Plain (Const "ready") [Sym (Var "A")] True) [Plain (Const "\"rdf:type\"") [Sym (Var "A"),Sym (Const "\"wp1:Activity\"")] True,Plain (Const "missing_commit") [Sym (Var "A")] False]) (wrapparser rule "" "ready(A) :- \"rdf:type\"(A,\"wp1:Activity\"), not missing_commit(A).")

trule14 = TestCase $ assertEqual "rule 14" (Fact [])  (wrapparser rule "" "ready(A :- \"rdf:type\"(A,\"wp1:Activity\"), not missing_commit(A).")
trule15 = TestCase $ assertEqual "rule 15" (Fact [])  (wrapparser rule "" "ready(A) :- \"rdf:type\" A,\"wp1:Activity\"), not missing_commit(A).")

trule16 = TestCase $ assertEqual "rule 16"  (Rule (Plain (Const "border") [Arith Plus (Arith Mult (Arith Minus (Sym (Var "N")) (Number (Const "1"))) (Sym (Var "R"))) (Number (Const "1"))] True) [Plain (Const "number") [Sym (Var "N")] True,Plain (Const "sqrt") [Sym (Var "R")] True,BExpr LtEq (Sym (Var "N")) (Sym (Var "R"))]) (wrapparser rule "" "border((N-1)*R+1) :- number(N), sqrt(R), N<=R.")

trule17 = TestCase $ assertEqual "rule 17" (Rule (Plain (Const "dist") [Func (Const "#abs") [Arith Minus (Sym (Var "RK1")) (Sym (Var "RK2"))] True] True) [Plain (Const "restaurant") [Sym (Var "RN1"),Sym (Var "RK1")] True,Plain (Const "restaurant") [Sym (Var "RN2"),Sym (Var "RK2")] True]) (wrapparser rule "" "dist(#abs(RK1-RK2)) :- restaurant(RN1,RK1), restaurant(RN2,RK2).")

-- trule = TestCase $ assertEqual "rule X"  (wrapparser rule "" "")
-- tdeny = TestCase $ assertEqual "deny X"  (wrapparser deny "" "")
-- trulebase = TestCase $ assertEqual "rulebase X"  (wrapparser' rulebase "" "")

tbody1 = TestCase $ assertEqual "body 1" [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True,Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True] (wrapparser_bl body "" "blub(Foo,Bar,Goo), blab(Baa), bii")

tbody2 = TestCase $ assertEqual "body 2" [Plain (Const "vtx") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "Y")] True,BExpr Lt (Sym (Var "X")) (Sym (Var "Y")),Plain (Const "r") [Sym (Var "X"),Sym (Var "Y")] False] (wrapparser_bl body "" "vtx(X), vtx(Y), X < Y, not r(X, Y)")

tbody3 = TestCase $ assertEqual "body 3" [Typed [Plain (Const "arc_S") [Sym (Var "X"),Sym (Var "Y")] False,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y")] True],Plain (Const "vtx") [Sym (Var "Y")] True] (wrapparser_bl body "" "not arc_S(X, Y) : arc(X, Y), vtx(Y)")

tbody4 = TestCase $ assertEqual "body 4" [Typed [Plain (Const "arc_S") [Sym (Var "X"),Sym (Var "Y")] False,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y")] True]]  (wrapparser_bl body "" "not arc_S(X, Y) : arc(X, Y)")

tbody5 = TestCase $ assertEqual "body 5" [Plain (Const "occurs") [Sym (Var "X")] True,Typed [Plain (Const "occurs") [Sym (Var "Y")] False,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))],Plain (Const "vtx") [Sym (Var "X")] True] (wrapparser_bl body "" "occurs(X), not occurs(Y) : Y < X, vtx(X)")

tbody6 = TestCase $ assertEqual "body 6" [Typed [Plain (Const "occurs") [Sym (Var "Y")] False,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))],Plain (Const "vtx") [Sym (Var "X")] True] (wrapparser_bl body "" "not occurs(Y) : Y < X, vtx(X)")

tbody7 = TestCase $ assertEqual "body 7" [Plain (Const "occurs") [Sym (Var "X")] True,Typed [Plain (Const "occurs") [Sym (Var "Y")] False,Plain (Const "vtx") [Sym (Var "X")] True,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))],Plain (Const "vtx") [Sym (Var "X")] True] (wrapparser_bl body "" "occurs(X), not occurs(Y) : vtx(X) : Y < X, vtx(X)")

tbody8 = TestCase $ assertEqual "body 8" [Plain (Const "waitingfor") [Sym (Var "_"),Sym (Var "_")] True] (wrapparser_bl body "" "waitingfor(_,_).")

tbody9 = TestCase $ assertEqual "body 9" [Assignment (Var "M") (Optimize False [Typed [Plain (Const "est") [Sym (Var "I"),Sym (Var "S")] True,Plain (Const "est") [Sym (Var "I"),Sym (Var "S")] True,Weighed (Sym (Var "S")) (Plain (Const "hasest") [Sym (Var "I")] True) True]] True) True,Assignment (Var "N") (Optimize True [Typed [Plain (Const "est") [Sym (Var "J"),Sym (Var "T")] True,Plain (Const "est") [Sym (Var "J"),Sym (Var "T")] True,Weighed (Sym (Var "T")) (Plain (Const "hasest") [Sym (Var "J")] True) True]] True) True,Plain (Const "sest") [Sym (Var "P")] True,Plain (Const "est") [] True] (wrapparser_bl body "" "M = #min [ est(I,S) : est(I,S) : hasest(I) = S ],\nN = #max [ est(J,T) : est(J,T) : hasest(J) = T ], sest(P), est.")

tbody10 = TestCase $ assertEqual "body 10" [Card (Sym (Const "any")) (Arith Mult (Sym (Const "k")) (Number (Const "1"))) [Typed [Plain (Const "sat") [Sym (Var "C")] True,Plain (Const "clause") [Sym (Var "C")] True]] True] (wrapparser_bl body "" "{  sat(C) : clause(C) } k*1.")

-- tbody = TestCase $ assertEqual "body X"  (wrapparser_bl body "" "")

tgenrel1 = TestCase $ assertEqual "genrel 1" (Plain (Const "blub") [] True) (wrapparser_bl' genrel "" "blub")

tgenrel2 = TestCase $ assertEqual "genrel 2" (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) (wrapparser_bl' genrel "" "blub(Foo,Bar,Goo)")

tgenrel3 = TestCase $ assertEqual "genrel 3" (Plain (Const "waitingfor") [Sym (Var "_"),Sym (Var "_")] True) (wrapparser_bl' genrel "" "waitingfor(_,_)")

tgenrel4 = TestCase $ assertEqual "genrel 4" (BExpr Gt (Sym (Var "X")) (Sym (Var "Y"))) (wrapparser_bl' genrel "" "X > Y")

tgenrel5 = TestCase $ assertEqual "genrel 5" (Card (Sym (Const "any")) (Sym (Const "any")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True] True)
 (wrapparser_bl' genrel "" "{blub(Foo,Bar,Goo)}")

tgenrel6 = TestCase $ assertEqual "genrel 6" (Card (Sym (Const "any")) (Sym (Const "any")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True,Plain (Const "blab") [Sym (Var "Zub"),Sym (Var "Zap"),Sym (Var "Zoo")] True] True) (wrapparser_bl' genrel "" "{blub(Foo,Bar,Goo),blab(Zub,Zap,Zoo)}")

tgenrel7 = TestCase $ assertEqual "genrel 7" (Card (Number (Const "1")) (Number (Const "2")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True] True)  (wrapparser_bl' genrel "" "1{blub(Foo,Bar,Goo)}2")

tgenrel8 = TestCase $ assertEqual "genrel 8" (Card (Number (Const "1")) (Number (Const "1")) [Plain (Const "maps_to") [Sym (Var "X"),Sym (Var "U")] True] True) (wrapparser_bl' genrel "" "1 { maps_to(X, U) } 1")

tgenrel9 = TestCase $ assertEqual "genrel 9" (Card (Sym (Const "any")) (Number (Const "1")) [Typed [Plain (Const "sat") [Sym (Var "C")] True,Plain (Const "clause") [Sym (Var "C")] True]] True)  (wrapparser_bl' genrel "" "{  sat(C) : clause(C) } 1")

tgenrel10 = TestCase $ assertEqual "genrel 10"  (Card (Sym (Const "any")) (Arith Minus (Sym (Const "k")) (Number (Const "1"))) [Typed [Plain (Const "sat") [Sym (Var "C")] True,Plain (Const "clause") [Sym (Var "C")] True]] True) (wrapparser_bl' genrel "" "{  sat(C) : clause(C) } k-1")

tgenrel11 = TestCase $ assertEqual "genrel 11"  (Card (Sym (Const "any")) (Sym (Const "any")) [Typed [Plain (Const "true") [Sym (Var "A")] True,Plain (Const "atom") [Sym (Var "A")] True]] True)
 (wrapparser_bl' genrel "" "{ true(A) : atom(A) }")

tgenrel12 = TestCase $ assertEqual "genrel 12" (Card (Number (Const "2")) (Number (Const "2")) [Plain (Const "i") [Sym (Var "A"),Sym (Const "\"wp1:active\""),Sym (Const "\"yes\"")] True,Plain (Const "d") [Sym (Var "A"),Sym (Const "\"wp1:active\""),Sym (Const "\"no\"")] True] True) (wrapparser_bl' genrel "" "2{i(A,\"wp1:active\",\"yes\"),d(A,\"wp1:active\",\"no\")}2")

tgenrel13 = TestCase $ assertEqual "genrel 13"  (Card (Sym (Var "M")) (Sym (Const "any")) [Typed [Plain (Const "\"wp1:commits\"") [Sym (Var "Cap"),Sym (Var "A3")] True,Plain (Const "\"rdf:type\"") [Sym (Var "A3"),Sym (Const "\"wp1:Activity\"")] True]] True) (wrapparser_bl' genrel "" "M{\"wp1:commits\"(Cap,A3):\"rdf:type\"(A3,\"wp1:Activity\")}")

tgenrel14 = TestCase $ assertEqual "genrel 14" (Card (Sym (Const "any")) (Number (Const "2")) [Plain (Const "i") [Sym (Var "A"),Sym (Const "\"wp1:active\""),Sym (Const "\"yes\"")] True,Plain (Const "d") [Sym (Var "A"),Sym (Const "\"wp1:active\""),Sym (Const "\"no\"")] True] True) (wrapparser_bl' genrel "" "{i(A,\"wp1:active\",\"yes\"),d(A,\"wp1:active\",\"no\")}2")

tgenrel15 = TestCase $ assertEqual "genrel 15" (Card (Sym (Const "any")) (Sym (Const "any")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Const "\"Bar\""),Sym (Var "Goo")] True] True) (wrapparser_bl' genrel "" "{blub(Foo,\"Bar\",Goo)}")

-- tgenrel16 = TestCase $ assertEqual "genrel 16"  (Count (Sym (Const "any")) (Sym (Const "any")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)]] True) (wrapparser_bl' genrel "" "[ lc(X, Y) : arc(X, Y, L) = L ]")
tgenrel16 = TestCase $ assertEqual "genrel 16"  (Count (Sym (Const "any")) (Sym (Const "any")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True]] True) (wrapparser_bl' genrel "" "[ lc(X, Y) : arc(X, Y, L) = L ]")

-- Note that the vtx should not be parsed
tgenrel17 = TestCase $ assertEqual "genrel 17" (Typed [Plain (Const "occurs") [Sym (Var "Y")] False,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))]) (wrapparser_bl' genrel "" "not occurs(Y) : Y < X, vtx(X)")

tgenrel18 = TestCase $ assertEqual "genrel 18" (Typed [Plain (Const "f") [] True,Plain (Const "vtx") [Sym (Var "Y")] True,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))]) (wrapparser_bl' genrel "" "f : vtx(Y) : Y < X")

tgenrel19 = TestCase $ assertEqual "genrel 19" (Plain (Const "person") [Alternative [Sym (Const "a"),Sym (Const "b"),Sym (Const "c")]] True)  (wrapparser_bl' genrel "" "person(a; b; c)")

tgenrel20 = TestCase $ assertEqual "genrel 20"  (Optimize True [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True]] True) (wrapparser_bl' genrel "" "#max [ lc(X, Y) : arc(X, Y, L) = L ]")

tgenrel21 = TestCase $ assertEqual "genrel 21" (Assignment (Var "M") (Optimize False [Typed [Plain (Const "est") [Sym (Var "I"),Sym (Var "S")] True,Plain (Const "est") [Sym (Var "I"),Sym (Var "S")] True,Weighed (Sym (Var "S")) (Plain (Const "hasest") [Sym (Var "I")] True) True]] True) True) (wrapparser_bl' genrel "" "M = #min [ est(I,S) : est(I,S) : hasest(I) = S ]")

tgenrel22 = TestCase $ assertEqual "genrel 22" (Plain (Const "dist") [Func (Const "#abs") [Arith Minus (Sym (Var "RK1")) (Sym (Var "RK2"))] True] True) (wrapparser_bl' genrel "" "dist(#abs(RK1-RK2))")

-- tgenrel = TestCase $ assertEqual "genrel X"  (wrapparser_bl' genrel "" "")

tnumericexpr1 = TestCase $ assertEqual "numericexpr 1" (Arith Plus (Sym (Const "k")) (Number (Const "2"))) (wrapparser_exp numericexpr "" "k + 2")

tnumericexpr2 = TestCase $ assertEqual "numericexpr 2" (Sym (Const "k")) (wrapparser_exp numericexpr "" "k")

tnumericexpr3 = TestCase $ assertEqual "numericexpr 3" (Number (Const "1")) (wrapparser_exp numericexpr "" "1")

tnumericexpr4 = TestCase $ assertEqual "numericexpr 4" (Arith Mult (Arith Plus (Sym (Const "k")) (Number (Const "2"))) (Sym (Var "Z"))) (wrapparser_exp numericexpr "" "(k + 2) * Z")

tnumericexpr5 = TestCase $ assertEqual "numericexpr 5" (Arith Plus (Sym (Const "k")) (Arith Mult (Number (Const "2")) (Sym (Var "Z")))) (wrapparser_exp numericexpr "" "k + 2 * Z")

tnumericexpr6 = TestCase $ assertEqual "numericexpr 6" (Arith Div (Arith Mod (Sym (Const "k")) (Sym (Const "\"jopi\""))) (Sym (Var "Z"))) (wrapparser_exp numericexpr "" "(k mod \"jopi\") / (Z)")

tnumericexpr7 = TestCase $ assertEqual "numericexpr 7" (Alternative [Sym (Var "X"),Sym (Var "Y"),Sym (Const "k"),Number (Const "1")]) (wrapparser_exp numericexpr "" "X;Y;k;1")

tnumericexpr8 = TestCase $ assertEqual "numericexpr 8" (Arith Range (Number (Const "1")) (Sym (Var "X"))) (wrapparser_exp numericexpr "" "1..X")

tnumericexpr9 = TestCase $ assertEqual "numericexpr 9" (Arith Div (Arith Range (Number (Const "1")) (Sym (Var "X"))) (Number (Const "2")))  (wrapparser_exp numericexpr "" "1..X/2")

tnumericexpr10 = TestCase $ assertEqual "numericexpr 10" (Arith Plus (Arith Mult (Arith Minus (Sym (Var "N")) (Number (Const "1"))) (Sym (Var "R"))) (Number (Const "1"))) (wrapparser_exp numericexpr "" "(N-1)*R+1")

tnumericexpr11 = TestCase $ assertEqual "numericexpr 11" (Func (Const "#abs") [Arith Minus (Sym (Var "N")) (Number (Const "1")),Sym (Var "X"),Number (Const "1")] True) (wrapparser_exp numericexpr "" "#abs(N-1, X, 1)")

-- tnumericexpr = TestCase $ assertEqual "numericexpr X"  (wrapparser_exp numericexpr "" "")

-- Note that "+ 2" are not parsed 
tnumeric1 = TestCase $ assertEqual "numeric 1" (Number (Const "1")) (wrapparser_exp numeric "" "1 + 2")

tnumeric2 = TestCase $ assertEqual "numeric 2" (Sym (Const "k")) (wrapparser_exp numeric "" "k + 2")

tnumeric3 = TestCase $ assertEqual "numeric 3" (Sym (Const "k")) (wrapparser_exp numeric "" "k")

tnumeric4 = TestCase $ assertEqual "numeric 4" (Number (Const "1")) (wrapparser_exp numeric "" "1")

tnumeric5 = TestCase $ assertEqual "numeric 5" (Sym (Var "X")) (wrapparser_exp numeric "" "X")

-- tnumeric = TestCase $ assertEqual "numeric X"  (wrapparser_exp numeric "" "")

tnexpr1 = TestCase $ assertEqual "nexpr 1" (Arith Plus (Sym (Const "k")) (Number (Const "2"))) (wrapparser_exp nexpr "" "k + 2")

tnexpr2 = TestCase $ assertEqual "nexpr 2" (Arith Plus (Sym (Const "k")) (Number (Const "2"))) (wrapparser_exp nexpr "" "k + 2 + Z")

tnexpr3 = TestCase $ assertEqual "nexpr 3" (Arith Plus (Sym (Const "k")) (Sym (Var "Z"))) (wrapparser_exp nexpr "" "k + Z")

tnexpr4 = TestCase $ assertEqual "nexpr 4" (Sym (Const "Erroneous MyExpr")) (wrapparser_exp nexpr "" "k + + Z")

-- tnexpr = TestCase $ assertEqual "nexpr X"  (wrapparser_exp nexpr "" "")


tbexpr1 = TestCase $ assertEqual "bexpr 1" (BExpr Gt (Sym (Const "k")) (Number (Const "2"))) (wrapparser_bl' bexpr "" "k > 2")

tbexpr2 = TestCase $ assertEqual "bexpr 2" (BExpr Lt (Sym (Var "X")) (Sym (Var "Y"))) (wrapparser_bl' bexpr "" "X < Y")

-- tbexpr = TestCase $ assertEqual "bexpr X"  (wrapparser_bl' bexpr "" "")

tmycount1 = TestCase $ assertEqual "mycount 1" (Count (Number (Const "1")) (Number (Const "2")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True] True)  (wrapparser_bl' mycount "" "1 [blub(Foo,Bar,Goo)] 2")

tmycount2 = TestCase $ assertEqual "mycount 2" (Count (Sym (Var "M")) (Sym (Const "any")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True] True)  (wrapparser_bl' mycount "" "M[blub(Foo,Bar,Goo)]")

tmycount3 = TestCase $ assertEqual "mycount 3" (Count (Sym (Const "any")) (Sym (Const "any")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True] True) (wrapparser_bl' mycount "" "[blub(Foo,Bar,Goo)]")

tmycount4 = TestCase $ assertEqual "mycount 4" (Count (Sym (Const "any")) (Arith Minus (Sym (Const "k")) (Number (Const "1"))) [Typed [Plain (Const "sat") [Sym (Var "C")] True,Plain (Const "clause") [Sym (Var "C")] True]] True) (wrapparser_bl' mycount "" "[  sat(C) : clause(C) ] k-1")

-- tmycount5 = TestCase $ assertEqual "mycount 5" (Count (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)]] True) (wrapparser_bl' mycount "" "k [ lc(X, Y) : arc(X, Y, L) = L ]")
tmycount5 = TestCase $ assertEqual "mycount 5" (Count (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True]] True) (wrapparser_bl' mycount "" "k [ lc(X, Y) : arc(X, Y, L) = L ]")

tmycount6 = TestCase $ assertEqual "mycount 6" (Count (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) False]] True) (wrapparser_bl' mycount "" "k [ lc(X, Y) : not arc(X, Y, L) = L]")

-- tmycount = TestCase $ assertEqual "mycount X"  (wrapparser_bl' mycount "" "")

tmychoice1 = TestCase $ assertEqual "mychoice 1" (Card (Number (Const "1")) (Number (Const "2")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True] True) (wrapparser_bl' mychoice "" "1 {blub(Foo,Bar,Goo)} 2")

tmychoice2 = TestCase $ assertEqual "mychoice 2" (Card (Sym (Var "M")) (Sym (Const "any")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True] True) (wrapparser_bl' mychoice "" "M{blub(Foo,Bar,Goo)}")

tmychoice3 = TestCase $ assertEqual "mychoice 3" (Card (Sym (Const "any")) (Sym (Const "any")) [Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True] True) (wrapparser_bl' mychoice "" "{blub(Foo,Bar,Goo)}")

tmychoice4 = TestCase $ assertEqual "mychoice 4" (Card (Sym (Const "any")) (Arith Minus (Sym (Const "k")) (Number (Const "1"))) [Typed [Plain (Const "sat") [Sym (Var "C")] True,Plain (Const "clause") [Sym (Var "C")] True]] True) (wrapparser_bl' mychoice "" "{  sat(C) : clause(C) } k-1")

tmychoice5 = TestCase $ assertEqual "mychoice 5" (Card (Sym (Const "any")) (Number (Const "1")) [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True,Plain (Const "mooh") [Sym (Var "Z")] True]] True) (wrapparser_bl' mychoice "" "{ lc(X, Y) : arc(X, Y, L) : mooh(Z) } 1")

tmychoice6 = TestCase $ assertEqual "mychoice 6" (Card (Number (Const "1")) (Sym (Const "any")) [Plain (Const "p") [] True,Plain (Const "t") [] True] True) (wrapparser_bl' mychoice "" "1 { p, t }")

tmychoice7 = TestCase $ assertEqual "mychoice 7" (Card (Sym (Const "any")) (Sym (Const "any")) [Plain (Const "p") [] True,Plain (Const "t") [] True,Plain (Const "x") [] False] True) (wrapparser_bl' mychoice "" "{ p, t, not x}")

tmychoice8 = TestCase $ assertEqual "mychoice 8" (Card (Sym (Const "any")) (Sym (Const "any")) [Plain (Const "p") [] True,Plain (Const "t") [] True,Plain (Const "x") [] False] True) (wrapparser_bl' mychoice "" "{ p, t, not x }")

tmychoice9 = TestCase $ assertEqual "mychoice 9" Empty (wrapparser_bl' mychoice "" "1 { p, not t t}")

-- tmychoice = TestCase $ assertEqual "mychoice X"  (wrapparser_bl' mychoice "" "")

-- Note that the latter "no" is not parsed 
trel1 = TestCase $ assertEqual "rel 1" (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) (wrapparser_bl' rel "" "blub(Foo,Bar,Goo),\"no\"")

-- trel2 = TestCase $ assertEqual "rel 2" (Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)) (wrapparser_bl' rel "" "arc(X, Y, L) = L")
trel2 = TestCase $ assertEqual "rel 2" (Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True) (wrapparser_bl' rel "" "arc(X, Y, L) = L")

trel3 = TestCase $ assertEqual "rel 3" (Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True]) (wrapparser_bl' rel "" "lc(X,Y) : arc(X, Y, L)")

-- trel4 = TestCase $ assertEqual "rel 4" (Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)]) (wrapparser_bl' rel "" "lc(X,Y) : arc(X, Y, L) = L")
trel4 = TestCase $ assertEqual "rel 4" (Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True]) (wrapparser_bl' rel "" "lc(X,Y) : arc(X, Y, L) = L")

trel5 = TestCase $ assertEqual "rel 5" (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) (wrapparser_bl' rel "" "blub(Foo,Bar,Goo)")

-- Only the first atom is parsed in the following three
trel6 = TestCase $ assertEqual "rel 6" (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) (wrapparser_bl' rel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)")

trel7 = TestCase $ assertEqual "rel 7" (Plain (Const "r") [] True) (wrapparser_bl' rel "" "r, s, not t")

trel8 = TestCase $ assertEqual "rel 8" (Plain (Const "r") [] False) (wrapparser_bl' rel "" "not r, s, not t")

trel9 = TestCase $ assertEqual "rel 9" (Typed [Plain (Const "ttask") [Sym (Var "I"),Sym (Var "D")] True,Plain (Const "ttask") [Sym (Var "I"),Sym (Var "D")] True,Plain (Const "haslet") [Sym (Var "I")] False,Weighed (Sym (Var "D")) (Plain (Const "tsklet") [Sym (Var "I")] True) False]) (wrapparser_bl' rel "" "ttask(I,D) : ttask(I,D) : not haslet(I) : not tsklet(I) = D")

trel10 = TestCase $ assertEqual "rel 10" (Typed [Plain (Const "f") [] True,Plain (Const "vtx") [Sym (Var "Y")] True,BExpr Lt (Sym (Var "Y")) (Sym (Var "X")),Assign (Var "L") (Arith Range (Sym (Var "X")) (Sym (Var "Y")))]) (wrapparser_bl' rel "" "f : vtx(Y) : Y < X : L = X..Y.")

-- trel = TestCase $ assertEqual "rel X"  (wrapparser_bl' rel "" "")

ttrel1 = TestCase $ assertEqual "trel 1" (Typed [Plain (Const "arc_S") [Sym (Var "X"),Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y")] True]) (wrapparser_bl' trel "" "arc_S(X, Y) : arc(X, Y)")

ttrel2 = TestCase $ assertEqual "trel 2" (Typed [Plain (Const "arc_S") [Sym (Var "X"),Sym (Var "Y")] False,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Yo")] True]) (wrapparser_bl' trel "" "not arc_S(X, Y) : arc(X, Yo)")

-- ttrel3 = TestCase $ assertEqual "trel 3" (Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)]) (wrapparser_bl' trel "" "lc(X, Y) : arc(X, Y, L) = L")
ttrel3 = TestCase $ assertEqual "trel 3" (Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True]) (wrapparser_bl' trel "" "lc(X, Y) : arc(X, Y, L) = L")

ttrel4 = TestCase $ assertEqual "trel 4" (Typed [Plain (Const "occurs") [Sym (Var "Y")] False,Plain (Const "vtx") [Sym (Var "X")] True,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))]) (wrapparser_bl' trel "" "not occurs(Y) : vtx(X) : Y < X")

-- Not typed, fails
ttrel5 = TestCase $ assertEqual "trel 5" Empty (wrapparser_bl' trel "" "blub(Foo,Bar,Goo)")

ttrel6 = TestCase $ assertEqual "trel 6" (Typed [Plain (Const "f") [] True,Plain (Const "vtx") [Sym (Var "Y")] True,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))]) (wrapparser_bl' trel "" "f : vtx(Y) : Y < X.")

-- Make sure we do not parse too far
ttrel7 = TestCase $ assertEqual "trel 7" Empty (wrapparser_bl' trel "" "forth(J,NI+1,S-M) :")

ttrel8 = TestCase $ assertEqual "trel 8" Empty (wrapparser_bl' trel "" "forth(J,NI+1,S-M) :-")

-- ttrel = TestCase $ assertEqual "trel X"  (wrapparser_bl' trel "" "")

tatomrel1 = TestCase $ assertEqual "atomrel 1" (Plain (Const "blub") [] True) (wrapparser_bl' atomrel "" "blub(Foo,Bar,Goo)")

-- Only 1st atom is parsed
tatomrel2 = TestCase $ assertEqual "atomrel 2" (Plain (Const "blub") [] True) (wrapparser_bl' atomrel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)")

tatomrel3 = TestCase $ assertEqual "atomrel 3" (Plain (Const "r") [] True) (wrapparser_bl' atomrel "" "r, s, not t")

-- tatomrel = TestCase $ assertEqual "atomrel X"  (wrapparser_bl' atomrel "" "")

tsrel1 = TestCase $ assertEqual "srel 1" (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) (wrapparser_bl' srel "" "blub(Foo,Bar,Goo)")

-- Only the first one handled
tsrel2 = TestCase $ assertEqual "srel 2" (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) (wrapparser_bl' srel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)")

-- Dies on first comma 
tsrel3 = TestCase $ assertEqual "srel 3" Empty (wrapparser_bl' srel "" "r, s, not t")

tsrel4 = TestCase $ assertEqual "srel 4"  (Plain (Const "blub") [Sym (Var "Foo"),Sym (Const "\"Bar\""),Sym (Var "Goo")] True) (wrapparser_bl' srel "" "blub(Foo,\"Bar\",Goo)")

tsrel5 = TestCase $ assertEqual "srel 5" (Plain (Const "border") [Arith Plus (Arith Mult (Arith Minus (Sym (Var "N")) (Number (Const "1"))) (Sym (Var "R"))) (Number (Const "1")),Sym (Var "N")] True)
 (wrapparser_bl' srel "" "border((N-1)*R+1,N).")

-- tsrel = TestCase $ assertEqual "srel X"  (wrapparser_bl' srel "" "")

-- twrel1 = TestCase $ assertEqual "wrel 1" (Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)) (wrapparser_bl' wrel "" "arc(X, Y, L) = L")
twrel1 = TestCase $ assertEqual "wrel 1" (Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True) (wrapparser_bl' wrel "" "arc(X, Y, L) = L")

twrel2 = TestCase $ assertEqual "wrel 2" (Weighed (Arith Range (Number (Const "1")) (Sym (Var "L"))) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True) (wrapparser_bl' wrel "" "arc(X, Y, L) = 1..L")

twrel3 = TestCase $ assertEqual "wrel 3" (Assign (Var "L") (Arith Range (Number (Const "1")) (Sym (Var "X")))) (wrapparser_bl' wrel "" "L = 1..X")

-- twrel = TestCase $ assertEqual "wrel X"  (wrapparser_bl' wrel "" "")

tnegrel1 = TestCase $ assertEqual "negrel 1" (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] False) (wrapparser_bl' negrel "" "not blub(Foo,Bar,Goo)")

-- tnegrel = TestCase $ assertEqual "negrel X"  (wrapparser_bl' negrel "" "")

-- tarel1 = TestCase $ assertEqual "arel X"  (Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)) (wrapparser_bl' arel "" "arc(X, Y, L) = L")
tarel1 = TestCase $ assertEqual "arel 1" (Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True)  (wrapparser_bl' arel "" "arc(X, Y, L) = L")

tarel2 = TestCase $ assertEqual "arel 2" (Plain (Const "border") [Arith Plus (Arith Mult (Arith Minus (Sym (Var "N")) (Number (Const "1"))) (Sym (Var "R"))) (Number (Const "1")),Sym (Var "N")] True) (wrapparser_bl' arel "" "border((N-1)*R+1,N).")

-- tarel = TestCase $ assertEqual "arel X"  (wrapparser_bl' arel "" "")

tarel''1 = TestCase $ assertEqual "arel'' 1" (Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) False)  (wrapparser_bl' arel'' "" "not arc(X, Y, L) = L")

tarel''2 = TestCase $ assertEqual "arel'' 2" Empty  (wrapparser_bl' arel'' "" "not M = [ est(I,S) : est(I,S) : hasest(I) = S ]")

-- tarel'' = TestCase $ assertEqual "arel'' X"  (wrapparser_bl' arel'' "" "")

targs1 = TestCase $ assertEqual "args 1" [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")]  (wrapparser_exp' args "" "(Foo, Bar, Goo)")

targs2 = TestCase $ assertEqual "args 2" [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")]  (wrapparser_exp' args "" "(Foo,Bar, Goo)")

targs3 = TestCase $ assertEqual "args 3" [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")]  (wrapparser_exp' args "" "(Foo,Bar,Goo)")

targs4 = TestCase $ assertEqual "args 4" [Sym (Var "Foo")] (wrapparser_exp' args "" "(Foo)")

targs5 = TestCase $ assertEqual "args 5" [Sym (Var "Foo")] (wrapparser_exp' args "" "( Foo)")

targs6 = TestCase $ assertEqual "args 6" [Sym (Const "foo")] (wrapparser_exp' args "" "(foo)")

targs7 = TestCase $ assertEqual "args 7" [Sym (Const "foo"),Sym (Var "Bar"),Sym (Const "goo")] (wrapparser_exp' args "" "(foo,Bar,goo)")

targs8 = TestCase $ assertEqual "args 8" [Sym (Var "Foo"),Sym (Var "Bar")] (wrapparser_exp' args "" " ( Foo,Bar )")

-- fails
targs9 = TestCase $ assertEqual "args 9" [Sym (Const "Erroneous MyExpr")] (wrapparser_exp' args "" "")

targs10 = TestCase $ assertEqual "args 10" [Arith Range (Number (Const "1")) (Sym (Const "k"))] (wrapparser_exp' args "" "(1 .. k)")

targs11 = TestCase $ assertEqual "args 11" [Sym (Const "foo"),Sym (Var "Bar"),Number (Const "5")] (wrapparser_exp' args "" "(foo,Bar,5)")

targs12 = TestCase $ assertEqual "args 12" [Sym (Const "foo"),Sym (Const "\"Bar\""),Number (Const "5")] (wrapparser_exp' args "" "(foo,\"Bar\",5)")

targs13 = TestCase $ assertEqual "args 13" [Alternative [Sym (Var "X"),Arith Plus (Sym (Var "X")) (Number (Const "1"))],Sym (Var "Y")] (wrapparser_exp' args "" "(X;X+1,Y)")

targs14 = TestCase $ assertEqual "args 14" [Arith Plus (Arith Mult (Arith Minus (Sym (Var "N")) (Number (Const "1"))) (Sym (Var "R"))) (Number (Const "1")),Sym (Var "N")] (wrapparser_exp' args "" "((N-1)*R+1,N)")

targs15 = TestCase $ assertEqual "args 15" [Func (Const "#abs") [Arith Minus (Sym (Var "RK1")) (Sym (Var "RK2"))] True,Sym (Var "Z")] (wrapparser_exp' args "" "(#abs(RK1-RK2),Z)")

-- This does not work, but it really should, have a look at farg!
-- Or does it work still???
targs16 = TestCase $ assertEqual "args 16" [Func (Const "#abs") [Arith Minus (Sym (Var "RK1")) (Sym (Var "RK2"))] True] (wrapparser_exp' args "" "(#abs(RK1-RK2))")

-- targs = TestCase $ assertEqual "args X"  (wrapparser_exp' args "" "")

tfargs1 = TestCase $ assertEqual "fargs 1" [Func (Const "#abs") [Arith Minus (Sym (Var "RK1")) (Sym (Var "RK2"))] True] (wrapparser_exp' fargs "" "(#abs(RK1-RK2))")

tfargs2 = TestCase $ assertEqual "fargs 2" [Func (Const "#abs") [Arith Minus (Sym (Var "RK1")) (Sym (Var "RK2"))] True,Sym (Var "Z")] (wrapparser_exp' fargs "" "(#abs(RK1-RK2),Z)")


tmyelem1 = TestCase $ assertEqual "myelem 1" (Sym (Var "Foo")) (wrapparser_exp myelem "" "Foo")

tmyelem2 = TestCase $ assertEqual "myelem 2" (Sym (Const "foo")) (wrapparser_exp myelem "" "foo")

tmyelem3 = TestCase $ assertEqual "myelem 3" (Sym (Var "_")) (wrapparser_exp myelem "" "_")

tmyelem4 = TestCase $ assertEqual "myelem 4" (Sym (Const "\"foo\"")) (wrapparser_exp myelem "" "\"foo\"")

-- tmyelem = TestCase $ assertEqual "myelem X"  (wrapparser_exp myelem "" "")

tatom1 = TestCase $ assertEqual "atom 1" (Const "Erroneous Atom") (wrapparser_atom atom "" "Foo")

tatom2 = TestCase $ assertEqual "atom 2" (Const "foo") (wrapparser_atom atom "" "foo")

tatom3 = TestCase $ assertEqual "atom 3" (Const "\"Foo\"") (wrapparser_atom atom "" "\"Foo\"")

tatom4 = TestCase $ assertEqual "atom 4" (Const "\"wp1:Person\"")  (wrapparser_atom atom "" "\"wp1:Person\"")

-- Should this fail?
tatom5 = TestCase $ assertEqual "atom 5" (Const "Erroneous Atom") (wrapparser_atom atom "" "1")

tatom6 = TestCase $ assertEqual "atom 6" (Const "m") (wrapparser_atom atom "" "m")

-- tatom = TestCase $ assertEqual "atom X"  (wrapparser_atom atom "" "")

tnvariable1 = TestCase $ assertEqual "nvariable 1" (Var "Foo") (wrapparser_atom nvariable "" "Foo")

tnvariable2 = TestCase $ assertEqual "nvariable 2" (Var "F") (wrapparser_atom nvariable "" "F")

-- Only parses the first token, X
tnvariable3 = TestCase $ assertEqual "nvariable 3" (Var "X") (wrapparser_atom nvariable "" "X > Y")

-- tnvariable = TestCase $ assertEqual "nvariable X"  (wrapparser_atom nvariable "" "")

{--
taltrel1 = TestCase $ assertEqual "altrel 1" (Alternative [Plain (Const "arc_S") [Sym (Var "X"),Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y")] True]) (wrapparser_bl' altrel "" "arc_S(X, Y) ; arc(X, Y)")

taltrel2 = TestCase $ assertEqual "altrel 2" (Alternative [Plain (Const "arc_S") [Sym (Var "X"),Sym (Var "Y")] False,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Yo")] True])  (wrapparser_bl' altrel "" "not arc_S(X, Y) ; arc(X, Yo)")

taltrel3 = TestCase $ assertEqual "altrel 3" (Alternative [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True)])  (wrapparser_bl' altrel "" "lc(X, Y) ; arc(X, Y, L) = L")

taltrel4 = TestCase $ assertEqual "altrel 4" (Alternative [Plain (Const "occurs") [Sym (Var "Y")] False,Plain (Const "vtx") [Sym (Var "X")] True,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))]) (wrapparser_bl' altrel "" "not occurs(Y) ; vtx(X) ; Y < X")

taltrel5 = TestCase $ assertEqual "altrel 5" Empty (wrapparser_bl' altrel "" "blub(Foo;Bar,Bar;Foo,Goo;Moo)")

taltrel6 = TestCase $ assertEqual "altrel 6" (Alternative [Plain (Const "f") [] True,Plain (Const "g") [] True]) (wrapparser_bl' altrel "" "f;g")

taltrel7 = TestCase $ assertEqual "altrel 7" (Alternative [Plain (Const "f") [] True,Plain (Const "g") [] True]) (wrapparser_bl' altrel "" "f; g")

taltrel8 = TestCase $ assertEqual "altrel 8" (Alternative [Plain (Const "f") [] True,Plain (Const "g") [] True]) (wrapparser_bl' altrel "" "f ; g")

taltrel9 = TestCase $ assertEqual "altrel 9" (Alternative [Plain (Const "f") [] True,Plain (Const "g") [] True]) (wrapparser_bl' altrel "" "f ;g")

taltrel10 = TestCase $ assertEqual "altrel 10" (Alternative [Plain (Const "f") [] True,Plain (Const "g") [] True,Plain (Const "x") [] True,Plain (Const "y") [] True,Plain (Const "z") [] True]) (wrapparser_bl' altrel "" "f ;g;x;y;z")

taltrel11 = TestCase $ assertEqual "altrel 11" (Alternative [Plain (Const "f") [] True,Plain (Const "vtx") [Sym (Var "Y")] True,BExpr Lt (Sym (Var "Y")) (Sym (Var "X"))]) (wrapparser_bl' altrel "" "f ; vtx(Y) ; Y < X.")

-- taltrel = TestCase $ assertEqual "altrel X"  (wrapparser_bl' altrel "" "")
--}

taltexpr1 = TestCase $ assertEqual "altexpr 1" (Alternative [Sym (Const "f"),Sym (Const "g")]) (wrapparser_exp altexpr "" "f;g")

taltexpr2 = TestCase $ assertEqual "altexpr 2" (Alternative [Sym (Const "f"),Sym (Const "g")]) (wrapparser_exp altexpr "" "f; g")

taltexpr3 = TestCase $ assertEqual "altexpr 3"  (Alternative [Sym (Const "f"),Sym (Const "g"),Sym (Const "x"),Sym (Const "y"),Sym (Const "z")]) (wrapparser_exp altexpr "" "f ;g;x;y;z")

taltexpr4 = TestCase $ assertEqual "altexpr 4"  (Alternative [Sym (Const "f"),Sym (Const "g"),Sym (Const "x"),Sym (Const "y"),Sym (Var "Z")]) (wrapparser_exp altexpr "" "f ;g;x;y;Z")

taltexpr5 = TestCase $ assertEqual "altexpr 5" (Alternative [Sym (Var "Foo"),Sym (Var "Bar")]) (wrapparser_exp altexpr "" "Foo;Bar")
 
-- taltexpr = TestCase $ assertEqual "altexpr X"  (wrapparser_expr altexpr "" "")

tfunc1 = TestCase $ assertEqual "func 1" (Func (Const "#abs") [Sym (Var "N"),Arith Plus (Sym (Var "N")) (Number (Const "1"))] True) (wrapparser_exp func "" "#abs(N,N+1)")

-- tfunc = TestCase $ assertEqual "func X"  (wrapparser_expr func "" "")


tshoworhide1 = TestCase $ assertEqual "showorhide 1" (Show [Plain (Const "waitingfor") [Sym (Var "_"),Sym (Var "_")] True]) (wrapparser showorhide "" "show waitingfor(_,_).")

tshoworhide2 = TestCase $ assertEqual "showorhide 2" (GShow [Plain (Const "waitingfor") [Sym (Var "_"),Sym (Var "_")] True]) (wrapparser showorhide "" "#show waitingfor(_,_).")

tshoworhide3 = TestCase $ assertEqual "showorhide 3" (GHide [Plain (Const "waitingfor") [Sym (Var "_"),Sym (Var "_")] True]) (wrapparser showorhide "" "#hide waitingfor(_,_).")

tshoworhide4 = TestCase $ assertEqual "showorhide 4" (GHide [Empty]) (wrapparser showorhide "" "#hide.")

tshoworhide5 = TestCase $ assertEqual "showorhide 5" (GHide [Arity (Const "pos") "3"]) (wrapparser showorhide "" "#hide pos/3.")
tshoworhide6 = TestCase $ assertEqual "showorhide 6" (GShow [Arity (Const "pos") "3"]) (wrapparser showorhide "" "#show pos/3.")

-- tshoworhide = TestCase $ assertEqual "showorhide X"  (wrapparser showorhide "" "")

tmyassign1 = TestCase $ assertEqual "myassign 1"  (Assignment (Var "M") (Optimize False [Typed [Plain (Const "est") [Sym (Var "I"),Sym (Var "S")] True,Plain (Const "est") [Sym (Var "I"),Sym (Var "S")] True,Weighed (Sym (Var "S")) (Plain (Const "hasest") [Sym (Var "I")] True) True]] True) True) (wrapparser_bl' myassign "" "M = #min [ est(I,S) : est(I,S) : hasest(I) = S ]")

tmyassign2 = TestCase $ assertEqual "myassign 2" (Assignment (Var "M") (Count (Sym (Const "any")) (Sym (Const "any")) [Typed [Plain (Const "est") [Sym (Var "I"),Sym (Var "S")] True,Plain (Const "est") [Sym (Var "I"),Sym (Var "S")] True,Weighed (Sym (Var "S")) (Plain (Const "hasest") [Sym (Var "I")] True) True]] True) True) (wrapparser_bl' myassign "" "M = [ est(I,S) : est(I,S) : hasest(I) = S ]")

-- tmyassign = TestCase $ assertEqual "myassign X"  (wrapparser_bl' myassign "" "")

tmyoptimize1 = TestCase $ assertEqual "myoptimize 1" (Optimize True [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True]] True)  (wrapparser_bl' myoptimize "" "#max [ lc(X, Y) : arc(X, Y, L) = L ]")

tmyoptimize2 = TestCase $ assertEqual "myoptimize 2" (Optimize True [Typed [Plain (Const "lc") [Sym (Var "X"),Sym (Var "Y")] True,Weighed (Sym (Var "L")) (Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y"),Sym (Var "L")] True) True]] True)  (wrapparser_bl' myoptimize "" "max [ lc(X, Y) : arc(X, Y, L) = L ]")

-- tmyoptimize = TestCase $ assertEqual "myoptimize X"  (wrapparser_bl' myoptimize "" "")


tests = TestList [ truleorfact1, truleorfact2, trulebase1, trulebase2, trulebase3, trulebase4,
                    trulebase5, trulebase6, trulebase7, trulebase8, trulebase9, trulebase10, 
                    trulebase11, trulebase12, trulebase13, trulebase14, trulebase15, tconstdef1,
                    tfact1, tfact2,tdeny1, tdeny2, tdeny3, tdeny4, tdeny5, tdeny6,
                    trule1, trule2, trule3, trule4, trule5, trule6, trule7, trule8, trule9, 
                    trule10, trule11, trule12, trule13, trule14, trule15,trule16,trule17, 
                    tbody1,tbody2, tbody3, tbody4, tbody5, tbody6, tbody7, tbody8,tbody9,tbody10,
                    tgenrel1, tgenrel2, tgenrel3, tgenrel4, tgenrel5, tgenrel6, tgenrel7, tgenrel8,
                    tgenrel9, tgenrel10, tgenrel11, tgenrel12, tgenrel13, tgenrel14, tgenrel15, 
                    tgenrel16, tgenrel17, tgenrel18, tgenrel19, tgenrel20, tgenrel21,tgenrel22,
                    tarel1, tarel2, 
                    tarel''1, tarel''2,
                    tnumericexpr1, tnumericexpr2, tnumericexpr3,tnumericexpr4,tnumericexpr5,
                    tnumericexpr6, tnumericexpr7,tnumericexpr8,tnumericexpr9,tnumericexpr10, 
                    tnumericexpr11, 
                    tnumeric1 , tnumeric2, tnumeric3, tnumeric4, tnumeric5,
                    tnexpr1 , tnexpr2, tnexpr3, tnexpr4,
                    tbexpr1, tbexpr2,
                    tmycount1, tmycount2, tmycount3, tmycount4, tmycount5, tmycount6,
                    tmychoice1, tmychoice2, tmychoice3, tmychoice4, tmychoice5, tmychoice6,
                    tmychoice7, tmychoice8,tmychoice9,
                    trel1, trel2,trel3,trel4,trel5,trel6,trel7,trel8,trel9, trel10, 
                    ttrel1, ttrel2,ttrel3,ttrel4,ttrel5,ttrel6,ttrel7,ttrel8,
                    tatomrel1, tatomrel2, tatomrel3,
                    tsrel1, tsrel2, tsrel3, tsrel4,tsrel5, 
                    twrel1, twrel2, twrel3, tnegrel1, tarel1,
                    targs1,targs2,targs3,targs4,targs5,targs6,targs7,targs8,targs9,
                    targs10,targs11,targs12,targs13, targs14, targs15, targs16,
                    tfargs1, tfargs2, 
                    tmyelem1, tmyelem2, tmyelem3, tmyelem4,
                    tatom1,tatom2,tatom3,tatom4,tatom5,tatom6,
                    tnvariable1, tnvariable2, tnvariable3,
                    taltexpr1,taltexpr2,taltexpr3,taltexpr4,taltexpr5,
                    --taltrel1,taltrel2,taltrel3,taltrel4,taltrel5,taltrel6,taltrel7,
                    -- taltrel8,taltrel9,taltrel10,taltrel11
                    tshoworhide1, tshoworhide2, tshoworhide3, tshoworhide4, tshoworhide5, tshoworhide6,
                    tmyassign1, tmyassign2, tmyoptimize1, tmyoptimize2
                    ]

-- runTestTT tests

main = 
     do runTestTT tests 