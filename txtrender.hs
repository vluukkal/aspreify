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

import qualified Data.List as List
-- import System.IO.Unsafe
-- import Data.IORef 


import AspParse

txtargs a = 
    if length a == 0 
    then ""
    else 
--        "(" ++ unwords(intersperse "," (map unatom a))  ++ ")"
        "(" ++ unwords(List.intersperse "," (List.map unmyexpr a))  ++ ")"
        
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
                              unwords((List.intersperse "," (List.foldr txtbody' [] b))) ++ 
                              "}" ++
                            (if max == (Sym (Const "any")) then "" else (" " ++ unmyexpr(max)))]
    Count min max b nonneg -> accu ++ 
                             [(if min == (Sym (Const "any")) then "" else (unmyexpr(min) ++ " ")) ++ 
                             "[" ++ 
                              -- (head(txtbody' b [])) ++ 
                              unwords((List.intersperse "," (List.foldr txtbody' [] b))) ++ 
                              "]" ++
                            (if max == (Sym (Const "any")) then "" else (" " ++ unmyexpr(max)))]
    Typed bl -> accu ++
                [unwords((List.intersperse " : " (List.foldr txtbody' [] (reverse bl) )))]
    Weighed e1 b1 -> accu ++ [(head(txtbody' b1 [])) ++ " = " ++ 
                   (unmyexpr e1) ]
    BExpr op b1 b2 -> accu ++ [(unmyexpr b1) ++ " " ++ (unbop op) ++ " " ++ 
                   (unmyexpr b2)]
    Empty -> accu ++ [" NONE "]

txtitem i accu =
    case i of
      Rule b l -> accu ++ head(txtbody' b []) ++ " :- \n\t " ++ 
                  unwords(List.intersperse ",\n\t" (List.foldr txtbody' [] (reverse l))) ++ 
                 ".\n\n"
      Deny l -> accu  ++ ":- \n\t " ++ 
                unwords(List.intersperse ",\n\t" (List.foldr txtbody' [] (reverse l))) ++ ".\n\n"
      Fact l -> accu  ++ 
                unwords(List.intersperse ",\n\t" (List.foldr txtbody' [] (reverse l))) ++ ".\n\n"


txtrender rb = 
    case rb of 
      Left l -> "error:" ++ show(l)
      Right r -> List.foldr txtitem "" r
