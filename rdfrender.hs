--
-- Renderer to reified rules in an RDF/N3-like format. 
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

module RdfRender where

import qualified Data.List as List
import System.IO.Unsafe
import Data.IORef 


import AspParse
import TxtRender 

atomt a = 
    case a of 
      Var s -> "http://m3.org/rls#var"
      Const s -> "http://m3.org/rls#const"

unrdfarith op a1 a2 exprid = 
    let lid = (myrand())::Int in
    let rid = (myrand())::Int in
    show(exprid) ++ "\n" ++ 
    show (exprid) ++ ",rdf:type,http://m3.org/rls#arithexpr\n" ++ 
    show (exprid) ++ ",http://m3.org/rls#op,\"" ++ (unop op) ++ "\"\n" ++ 
    show (exprid) ++ ",http://m3.org/rls#left," ++ (unrdfmyexpr a1 lid ) ++ 
    show (exprid) ++ ",http://m3.org/rls#right," ++ (unrdfmyexpr a2 rid )

unrdfatom v id = 
    case v of 
      Const a -> show (id) ++ "\n" ++ 
                 show (id) ++ ",rdf:type,http://m3.org/rls#const\n" ++ 
                 show (id) ++ ",http://m3.org/rls#name," ++ show(a) ++ "\n"
      Var a -> show (id) ++ "\n" ++ 
               show (id) ++ ",rdf:type,http://m3.org/rls#var\n" ++ 
               show (id) ++ ",http://m3.org/rls#name," ++ show(a) ++ "\n"

unrdfcatom v id = 
    case v of 
      Const a -> show (id) ++ "\n" ++ 
                 show (id) ++ ",rdf:type,http://m3.org/rls#cconst\n" ++ 
                 show (id) ++ ",http://m3.org/rls#name," ++ show(a) ++ "\n"
      Var a -> show (id) ++ "\n" ++ 
               show (id) ++ ",rdf:type,http://m3.org/rls#cvar\n" ++ 
               show (id) ++ ",http://m3.org/rls#name," ++ show(a) ++ "\n"

-- unrdfmyexpr :: MyExpr Int String
unrdfmyexpr a exprid = 
    case a of 
      Sym s -> (unrdfcatom s exprid)
      Number s -> (unrdfcatom s exprid)
      Arith op a1 a2 -> (unrdfarith op a1 a2 exprid)

rdfargs parentid a = 
    if length a == 0 
    then ""
    else 
        -- let (res,ids) = foldr alist ("",parentid) a in res
        -- let (res,ids) = foldl alist ("",parentid) (reverse a) in res
        let (res,ids) = List.foldl alist ("",parentid) a in res
        -- let (res,ids) = foldl alist ("",parentid) (map unatom a) in res
        -- show(a)
    where 
      alist (accu,previd) i = 
          let argid = (myrand())::Int in 
          let exprid = (myrand())::Int in 
          let new_ac = accu ++ 
                       (unrdfmyexpr i argid) ++ 
{--
                       show(argid) ++ 
                       ",rdf:type," ++ atomt(i) ++ "\n" ++
                       -- ",rdf:type," ++ show(i) ++ "\n" ++
                                    (unrdfmyexpr min minexprid)) ++ 
--}
{--                                    
                       show(argid) ++ ",http://m3.org/rls#name," ++ 
                           show(unatom(i)) ++ "\n" ++
--}


                       -- show(argid) ++ ",http://m3.org/rls#name," ++ show(i) ++ "\n" ++
                       -- show(parentid) ++ ",http://m3.org/rls#arg," ++ "\n" ++
                       show(previd) ++ ",http://m3.org/rls#nxt," ++
                       show(argid) ++ "\n"
              in
                (new_ac,argid)

--  -> [[Char]]
{--
rdftypeargs parentid a = 
    if length a == 0 
    then ""
    else 
        let (res,ids) = foldl typelist ([],parentid) (reverse a) in res
    where 
      typelist (accu,previd) i = 
          let argid = (myrand())::Int in 
          let exprid = (myrand())::Int in 
          let new_ac = accu ++ 
                       (rdfbody' "http://m3.org/rls#hastype" argid i) ++ 
                       [show(previd) ++ ",http://m3.org/rls#nxt," ++
                       show(argid) ++ "\n"]
              in
                (new_ac,argid)
--}


-- 'r' is a single Rule
-- 'parentid' - the parent for this 
-- 'accu' is a list needed by fold 
rdfbody'' rel parentid r accu = accu ++ ["huh"]
rdfbody' :: [Char] -> Int -> Body -> [[Char]] -> [[Char]]
rdfbody' rel parentid r accu = 
  let factid = (myrand())::Int in 
  case r of
    Plain n a nonneg -> let myrel = (if rel == "" then "http://m3.org/rls#hashead" else rel)
                        in 
                        let embed = (myrand())::Int in 
                        accu ++ 
                        [show(parentid) ++ "," ++ myrel ++ "," ++ 
                        show(factid) ++ "\n" ++
                        show(factid) ++ ",rdf:type,http://m3.org/rls#fact\n" ++
                        show(factid) ++ ",owl:subClassof,http://m3.org/rls#stmt\n" ++
                        (if nonneg then "" 
                         else (show(factid) ++ 
                                       ",http://m3.org/rls#negated,\"yes\"\n")) ++ 
                        show(factid) ++ ",http://m3.org/rls#name," ++ 
                            show(unatom(n)) ++ "\n" ++ 
                        rdfargs factid a]
    Card min max b nonneg -> let myrel = (if rel == "" then "http://m3.org/rls#hashead" else rel)
                        in 
                          accu ++ 
                       [show(parentid) ++ "," ++ myrel ++ "," ++ 
                        show(factid) ++ "\n" ++
                        show(factid) ++ ",rdf:type,http://m3.org/rls#card\n" ++
                        show(factid) ++ ",owl:subClassof,http://m3.org/rls#stmt\n" ++
                        (if nonneg then "" 
                         else (show(factid) ++ 
                                       ",http://m3.org/rls#negated,\"yes\"\n")) ++ 
                        -- head(rdfbody' "" factid b []) ++ XXX
                        (List.foldr (++) "" 
                         (List.foldr 
                          (rdfbody' "http://m3.org/rls#hasbody" factid) [] b)) ++                         -- show("moo") ++ 
                        (let minexprid = (myrand())::Int in 
                         if min == (Sym (Const "any")) then "" else 
                             show(factid) ++ 
                                       ",http://m3.org/rls#min," ++ 
                                       -- show(unrdfmyexpr min minexprid) ++ 
                                       (unrdfmyexpr min minexprid)) ++
                                     -- "\n") ++
                        (let maxexprid = (myrand())::Int in 
                         if max == (Sym (Const "any")) then "" else 
                             show(factid) ++ 
                                       ",http://m3.org/rls#max," ++ 
                                       -- show(unrdfmyexpr max maxexprid) ++ 
                                       (unrdfmyexpr max maxexprid))
                       ]
    Count min max b nonneg -> let myrel = (if rel == "" then "http://m3.org/rls#hashead" else rel)
                        in 
                          accu ++ 
                       [show(parentid) ++ "," ++ myrel ++ "," ++ 
                        show(factid) ++ "\n" ++
                        show(factid) ++ ",rdf:type,http://m3.org/rls#count\n" ++
                        show(factid) ++ ",owl:subClassof,http://m3.org/rls#stmt\n" ++
                        (if nonneg then "" 
                         else (show(factid) ++ 
                                       ",http://m3.org/rls#negated,\"yes\"\n")) ++ 
                        -- head(rdfbody' "" factid b []) ++ XXX
                        (List.foldr (++) "" 
                         (List.foldr 
                          (rdfbody' "http://m3.org/rls#hasbody" factid) [] b)) ++                         -- show("moo") ++ 
                        (let minexprid = (myrand())::Int in 
                         if min == (Sym (Const "any")) then "" else 
                             show(factid) ++ 
                                       ",http://m3.org/rls#min," ++ 
                                       -- show(unrdfmyexpr min minexprid) ++ 
                                       (unrdfmyexpr min minexprid)) ++
                                     -- "\n") ++
                        (let maxexprid = (myrand())::Int in 
                         if max == (Sym (Const "any")) then "" else 
                             show(factid) ++ 
                                       ",http://m3.org/rls#max," ++ 
                                       -- show(unrdfmyexpr max maxexprid) ++ 
                                       (unrdfmyexpr max maxexprid))
                       ]
    Typed b -> let myrel = (if rel == "" then "http://m3.org/rls#hashead" else rel)
                        in 
                   accu ++ 
                   [show(parentid) ++ "," ++ myrel ++ "," ++ 
                     show(factid) ++ "\n" ++
                     show(factid) ++ ",rdf:type,http://m3.org/rls#qual\n" ++
                     -- show(parentid) ++ ",rdf:type,http://m3.org/rls#qual\n" ++
                     show(factid) ++ ",owl:subClassof,http://m3.org/rls#stmt\n" ++
                     (List.foldr (++) ""
                      (List.foldr
                       (rdfbody' "http://m3.org/rls#hastype" factid) [] b
                      ))]
    Weighed e1 b1 -> let wid = (myrand())::Int in
                     let eid = (myrand())::Int in
                     let myrel = (if rel == "" then "http://m3.org/rls#hashead" else rel)
                     in 
                     -- we reuse same factid essentially producing an rdfexpr
                     -- with added property #weight with its own ID
                     accu ++ 
                     [show(parentid) ++ "," ++ myrel ++ "," ++ 
                      show(factid) ++ "\n" ++
                      show(factid) ++ ",rdf:type,http://m3.org/rls#weighedstmt\n" ++
                     -- show(parentid) ++ ",rdf:type,http://m3.org/rls#qual\n" ++
                      show(factid) ++ ",owl:subClassof,http://m3.org/rls#stmt\n" ++
                     -- (head(rdfbody' "http://m3.org/rls#weighed" eid b1 [])) ++  
                     (head(rdfbody' "http://m3.org/rls#weighed" factid b1 [])) ++  
                     show (factid) ++ ",http://m3.org/rls#weight," ++ (unrdfmyexpr e1 wid) -- ++ "\n" 
                     ]
    BExpr op b1 b2 -> let lid = (myrand())::Int in
                      let rid = (myrand())::Int in
              accu ++ 
              [show (factid) ++ "\n" ++ 
              show (factid) ++ ",rdf:type,http://m3.org/rls#bexpr\n" ++ 
              show (factid) ++ ",http://m3.org/rls#bop,\"" ++ (unbop op) ++ "\"\n" ++ 
              show (factid) ++ ",http://m3.org/rls#left," ++ (unrdfmyexpr b1 lid ) ++ 
              show (factid) ++ ",http://m3.org/rls#right," ++ (unrdfmyexpr b2 rid )]

    Empty -> accu ++ [" NONE "]

rdfitem id i accu =
    -- 1st we make an unique identifier for this rule
    let ruleid = (myrand())::Int in 
    let preflink = show(id) ++ ",http://m3.org/rls#partof," ++ show(ruleid) ++ "\n" in 
    case i of
      Rule b l -> accu ++ preflink ++ show(ruleid) ++ ",rdf:type,http://m3.org/rls#rule\n" ++
           head(rdfbody' "" ruleid b []) ++ 
                  (List.foldr (++) "" (List.foldr (rdfbody' "http://m3.org/rls#hasbody" ruleid) [] l)) ++ 
                 "" 
      Deny l -> accu ++ preflink ++ show(ruleid) ++ ",rdf:type,http://m3.org/rls#constraint\n" ++
                (List.foldr (++) "" (List.foldr (rdfbody' "http://m3.org/rls#hasbody" ruleid) [] l))
                ++ 
                ""
      Fact l -> accu ++ preflink ++ show(ruleid) ++ ",rdf:type,http://m3.org/rls#assertion\n" ++
                (List.foldr (++) "" (List.foldr (rdfbody' "http://m3.org/rls#hasbody" ruleid) [] l))
                ++ 
                ""

rdfrender rb = 
    case rb of 
      Left l -> "error:" ++ show(l)
      Right r -> 
          let aid = (myrand())::Int in 
          List.foldr (rdfitem aid) "" r
      -- Right r -> show(r)

rdfrulerender n rb = 
    let fileid = (myrand())::Int in 
    let filepref = show(fileid) ++ ",rdf:type,http://m3.org/rls#ruleset\n" ++
                   show(fileid) ++ ",http://m3.org/rls#name," ++ show(n) ++ "\n" in 
    case rb of 
      Left l -> "error:" ++ show(l)
      Right r -> filepref ++ (List.foldr (rdfitem fileid) "" r)
