--
-- Quickcheck tests to generate random rules in the internal format. 
--
-- Copyright 2014 Vesa Luukkala
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
-- Use at interpreter:
-- :l Qcaspparse.hs 
-- Commandlines in comments at instance Arbitrary.  
-- 
-- Render rules back to text:
-- let rls = unGen (arbitrary :: Gen [Rules]) (System.Random.mkStdGen 2) 10
-- let txt = TxtRender.txtrender (Right rls)


module Qcaspparse where 

import System.IO
import System.Random
import Test.QuickCheck.Function
import Test.QuickCheck.Gen
import Test.QuickCheck

import Data.Char 

-- for liftM, fmap
import Control.Monad  
-- for <$> 
import Control.Applicative 

-- This module to test 
import AspParse
-- import TxtRender

nmchar c = 
  c `elem` ['A'..'Z'] ++ ['a' .. 'z'] ++ ['_','-'] ++ ['0' .. '9']

nmstr s = 
  all nmchar s && (s /= "")

varstr s = 
  nmstr s && (head s) `elem` ['A'..'Z']

otherstr s = 
  nmstr s && (head s) `elem` ['a'..'z']

-- unGen  (arbitrary :: Gen [Atom]) (System.Random.mkStdGen 4) 20
instance Arbitrary Atom where 
  arbitrary = 
    oneof [liftM AspParse.Const (suchThat (arbitrary :: Gen String) otherstr), liftM AspParse.Var (suchThat (arbitrary :: Gen String) varstr)]

-- unGen  (arbitrary :: Gen [MyOp]) (System.Random.mkStdGen 1) 10
instance Arbitrary MyOp where 
  arbitrary =
    elements [AspParse.Plus,AspParse.Minus,AspParse.Mult,AspParse.Div,AspParse.Mod,AspParse.Range]

-- unGen  (arbitrary :: Gen [BOp]) (System.Random.mkStdGen 1) 10
instance Arbitrary BOp where 
  arbitrary =
    elements [AspParse.Gt, AspParse.Lt,AspParse.GtEq,AspParse.LtEq,AspParse.Eq,AspParse.Neq,AspParse.Eqeq]

-- Now MyExpr, we need to control the size to avoid 
-- unchecked recursion. 
-- Check this as well:
-- http://stackoverflow.com/questions/15959357/quickcheck-arbitrary-instances-of-nested-data-structures-that-generate-balanced?rq=1

-- unGen (arbitrary :: Gen [MyExpr]) (System.Random.mkStdGen 2) 10

instance Arbitrary MyExpr where 
  arbitrary = sized arbMyExpr 

-- At depth 0 we force the result to be a leaf, that is, Number or Sym.  
arbMyExpr :: Int -> Gen MyExpr
arbMyExpr 0 = oneof [Number <$> arbitrary, Sym <$> arbitrary] 

arbMyExpr n | n > 0 = do
  m <- choose (1,4) :: Gen Int 
  case m of 
       -- Here we cover both Number and Sym, hence we choose only 1-4 
       1 -> oneof [Number <$> arbitrary, Sym <$> arbitrary]  
       2 -> do 
               -- limit the size of the list to 20 
               repeat <- choose(1,20) 
               let n' = n `div` (repeat + 1)
               exprs <- replicateM repeat (arbMyExpr n')
               return $ Alternative exprs
       3 -> do 
               myop <- arbitrary
               repeat <- choose(1,10) 
               let n' = n `div` (repeat + 1)
               larg <- (arbMyExpr n')
               rarg <- (arbMyExpr n')
               return $ Arith myop larg rarg 
       4 -> do 
               fname <- (arbitrary :: Gen Atom)
               repeat <- choose(1,20) 
               let n' = n `div` (repeat + 1)
               exprs <- replicateM repeat (arbMyExpr n')
               flag <- elements [True, False]
               return $ Func fname exprs flag  
               

-- unGen (arbitrary :: Gen Body) (System.Random.mkStdGen 2) 10
-- Empty 
-- unGen (arbitrary :: Gen Body) (System.Random.mkStdGen 3) 10
-- not empty ...

instance Arbitrary Body where 
  arbitrary = sized arbBody 

-- At depth 0 we force the result to be a leaf. 
arbBody :: Int -> Gen Body
arbBody 0 = oneof [liftM3 Plain  (arbitrary :: Gen Atom) (arbitrary :: Gen [MyExpr]) arbitrary, 
                   liftM3 BExpr arbitrary arbitrary arbitrary,                    
                   liftM2 Assign arbitrary arbitrary, 
                   liftM2 Arity arbitrary arbitrary, 
                   Comment <$> arbitrary,
                   return Empty
                   ] 

arbBody n | n > 0 = do 
  m <- choose (1,12) :: Gen Int 
  case m of 
       -- leaf
       1 -> liftM3 Plain  (arbitrary :: Gen Atom) (arbitrary :: Gen [MyExpr]) arbitrary
       2 -> do -- Card MyExpr MyExpr [Body] Bool
               myexprbot <- arbitrary 
               myexprtop <- arbitrary 
               -- limit the size of the list to 20 
               repeat <- choose(1,20) 
               let n' = n `div` (repeat + 1)
               bodies <- replicateM repeat (arbBody n')
               flag <- arbitrary 
               return $ Card myexprbot myexprtop bodies flag 
       3 -> do -- Count MyExpr MyExpr [Body] Bool
               myexprbot <- arbitrary 
               myexprtop <- arbitrary 
               -- limit the size of the list to 20 
               repeat <- choose(1,20) 
               let n' = n `div` (repeat + 1)
               bodies <- replicateM repeat (arbBody n')
               flag <- arbitrary 
               return $ Count myexprbot myexprtop bodies flag 
       4 -> do -- Optimize Bool [Body] Bool
               -- limit the size of the list to 20 
               fst <- arbitrary 
               repeat <- choose(1,20) 
               let n' = n `div` (repeat + 1)
               bodies <- replicateM repeat (arbBody n')
               snd <- arbitrary 
               return $ Optimize fst bodies snd
       5 -> do -- Typed [Body] 
               -- limit the size of the list to 20 
               repeat <- choose(1,20) 
               let n' = n `div` (repeat + 1)
               bodies <- replicateM repeat (arbBody n')
               return $ Typed bodies 
       6 -> do -- Weighed MyExpr Body Bool
               -- limit the size of the list to 20 
               myexpr <- arbitrary 
               body <- arbitrary 
               flag <- arbitrary 
               return $ Weighed myexpr body flag 
       -- leaf
       7 -> liftM3 BExpr arbitrary arbitrary arbitrary
       -- leaf
       8 -> liftM2 Assign arbitrary arbitrary
       9 -> do -- Assignment Atom Body Bool
               myatom <- arbitrary 
               body <- arbitrary 
               flag <- arbitrary 
               return $ Assignment myatom body flag 
       -- leaf
       10 -> liftM2 Arity arbitrary arbitrary
       -- leaf
       11 -> Comment <$> arbitrary
       -- leaf
       12 -> return Empty
        

-- unGen (arbitrary :: Gen Rules) (System.Random.mkStdGen 2) 10
-- unGen (arbitrary :: Gen [Rules]) (System.Random.mkStdGen 2) 10

instance Arbitrary Rules where 
  arbitrary = sized arbRules 

arbRules :: Int -> Gen Rules 
arbRules 0 = oneof [
                   RComment <$> arbitrary,
                   return Emptyset
                   ] 

arbRules n | n > 0 = do 
  m <- choose (1,15) :: Gen Int 
  case m of 
       -- leaf
       1 -> do 
               bodies <- mkbodies n
               return $ Deny bodies 
       2 -> do 
               mkbodies2 Deny n
       3 -> do 
               mkbodies2 Fact n
       4 -> do 
               mkbodies2 Show n
       5 -> do 
               mkbodies2 GShow n
       6 -> do 
               mkbodies2 Hide n
       7 -> do 
               mkbodies2 GHide n
       8 -> do 
               mkbodies2 External n
       9 -> do 
               mkbodies2 Function n
       10 -> do 
               mkbodies2 Minimize n 
       11 -> do 
               mkbodies2 Maximize n 
       12 -> do 
               mkbodies2 Consts n
       13 -> do 
               atom <- arbitrary 
               bodies <- mkbodies n
               return $ Computes atom bodies 
       14 -> RComment <$> arbitrary
       15 -> return Emptyset
         
mkbodies n = do 
       repeat <- choose(1,n) 
       let n' = n `div` (repeat + 1)
       replicateM repeat (arbBody n')

mkbodies2 cnst n = do 
       repeat <- choose(1,n) 
       let n' = n `div` (repeat + 1)
       bds <- replicateM repeat (arbBody n')
       return $ cnst bds 
    
-- This will return a randomly generated parsetree 
mkrls seed len = 
  unGen (arbitrary :: Gen [Rules]) (System.Random.mkStdGen seed) len