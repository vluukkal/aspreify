--
-- Renderer which renders the pasre tree without reification. 
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

module TxtRender where

import qualified Data.List as L
import Data.Text

-- import System.IO.Unsafe
-- import Data.IORef 


import AspParse

txtargs a = 
    if L.length a == 0 
    then ""
    else 
        "(" ++ L.unwords(L.intersperse "," (L.map unmyexpr a))  ++ ")"
        
-- 'r' is a single Rule
-- 'nl' is a flag whether to add an nl 
-- 'accu' is needed by fold 
{--
txtbody nl r accu = 
    case r of
      Plain n a nonneg -> accu ++ 
                          (if nonneg then "" else "not ") ++ 
                          n ++ txtargs a ++ (if nl then ",\n" else "")
      Card min max b nonneg -> accu ++ 
                               (if min == "any" then "" else (min ++ " ")) ++ 
                               "{" ++ txtbody False b "" ++ "}" ++
                              (if max == "any" then "" else (" " ++ max)) ++
                              (if nl then ",\n" else "")
      Typed b1 b2 -> accu ++ txtbody False b1 "" ++ " : " ++ 
                     txtbody False b2 ""
      Empty -> accu ++ " NONE "
--}

-- 'r' is a single Rule
-- 'nl' is a flag whether to add an nl 
-- 'accu' is a list needed by fold 
txtbody' r accu = 
  case r of
    Plain n a nonneg -> accu ++ 
                        [(if nonneg then "" else "not ") ++ 
                       unatom(n) ++ txtargs a]
    Card min max b nonneg -> accu ++ 
                             [(if min == (Sym (Const "any")) then "" else (unmyexpr(min) ++ " ")) ++ 
                             "{" ++ 
                              -- (head(txtbody' b [])) ++ 
                              L.unwords((L.intersperse "," (L.foldr txtbody' [] b))) ++ 
                              "}" ++
                            (if max == (Sym (Const "any")) then "" else (" " ++ unmyexpr(max)))]
    Count min max b nonneg -> accu ++ 
                             [(if min == (Sym (Const "any")) then "" else (unmyexpr(min) ++ " ")) ++ 
                             "[" ++ 
                              -- (head(txtbody' b [])) ++ 
                              L.unwords((L.intersperse "," (L.foldr txtbody' [] b))) ++ 
                              "]" ++
                            (if max == (Sym (Const "any")) then "" else (" " ++ unmyexpr(max)))]
    Typed bl -> accu ++
                [L.unwords((L.intersperse " : " (L.foldr txtbody' [] (L.reverse bl) )))]
    Weighed e1 b1 -> accu ++ [(L.head(txtbody' b1 [])) ++ " = " ++ 
                   (unmyexpr e1) ]
    BExpr op b1 b2 -> accu ++ [(unmyexpr b1) ++ " " ++ (unbop op) ++ " " ++ 
                   (unmyexpr b2)]
    Assign nm e -> accu ++ [(unatom nm) ++ " = " ++ (unmyexpr e)]
    Empty -> accu ++ [" NONE "]

txtitem i accu =
    case i of
      Rule b l -> accu ++ L.head(txtbody' b []) ++ " :- \n\t " ++ 
                  L.unwords(L.intersperse ",\n\t" (L.foldr txtbody' [] (l))) ++ 
                 ".\n\n"
      Deny l -> accu  ++ ":- \n\t " ++ 
                L.unwords(L.intersperse ",\n\t" (L.foldr txtbody' [] (l))) ++ ".\n\n"
      Fact l -> accu  ++ 
                L.unwords(L.intersperse ",\n\t" (L.foldr txtbody' [] (l))) ++ ".\n\n"
      Hide l -> accu ++ L.unwords(L.intersperse ",\n" 
                                (L.foldr (\x a -> ("hide " ++ x):a) [] 
                                 (L.foldr txtbody' [] (l)))) ++ ".\n\n"
      Show l -> accu ++ L.unwords(L.intersperse ",\n" 
                                (L.foldr (\x a -> ("show " ++ x):a) [] 
                                 (L.foldr txtbody' [] (l)))) ++ ".\n\n"
      Consts l -> accu ++ L.unwords(L.intersperse ",\n" 
                                (L.foldr (\x a -> ("const " ++ x):a) [] 
                                 (L.foldr txtbody' [] (l)))) ++ ".\n\n"


txtrender rb = 
    case rb of 
      Left l -> "error:" ++ show(l)
      Right r -> L.foldr txtitem "" (L.reverse r)
