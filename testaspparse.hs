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


truleorfact1 = TestCase $ assertEqual "ruleorfact 1" (Fact [Card (Sym (Const "k")) (Sym (Const "any")) [Typed [Plain (Const "in") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "X")] True]] True]) (wrapparser ruleorfact "" "k { in(X) : vtx(X) }.\n")

truleorfact2 = TestCase $ assertEqual "ruleorfact 2" (Rule (Plain (Const "a") [Sym (Var "X"),Sym (Var "Y")] True) [Plain (Const "in") [Sym (Var "X")] True,Plain (Const "in") [Sym (Var "Y")] True,Plain (Const "arc") [Sym (Var "X"),Sym (Var "Y")] False,Plain (Const "vtx") [Sym (Var "X")] True,Plain (Const "vtx") [Sym (Var "Y")] True]) (wrapparser ruleorfact "" "a(X,Y) :- in(X), in(Y), not arc(X, Y), vtx(X), vtx(Y).\n")

trulebase1 = TestCase $ assertEqual "rulebase 1" [Deny [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True]] (wrapparser' rulebase "" ":-  blab(Baa),\n bii.")

trulebase2 = TestCase $ assertEqual "rulebase 2" [Fact [Card (Sym (Const "any")) (Sym (Const "any")) [Typed [Plain (Const "true") [Sym (Var "A")] True,Plain (Const "atom") [Sym (Var "A")] True]] True]] (wrapparser' rulebase "" "{ true(A) : atom(A) }.")

trulebase3 = TestCase $ assertEqual "rulebase 3" [Rule (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True]] (wrapparser' rulebase "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.")

trulebase4 = TestCase $ assertEqual "rulebase 4" [Rule (Plain (Const "blub") [Sym (Var "Foo"),Sym (Var "Bar"),Sym (Var "Goo")] True) [Plain (Const "blab") [Sym (Var "Baa")] True,Plain (Const "bii") [] True],Deny [Plain (Const "zuu") [Sym (Var "Zaa")] True,Plain (Const "zii") [] True]] (wrapparser' rulebase "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.\n\n:-  zuu(Zaa),\n zii.")

-- trulebase = TestCase $ assertEqual "rulebase X"  (wrapparser' rulebase "" "")


tests = TestList [ truleorfact1, truleorfact2, trulebase1, trulebase2, trulebase3, trulebase4 ]

-- runTestTT tests

main = 
     do runTestTT tests 