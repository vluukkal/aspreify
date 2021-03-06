--
-- Renderer to reified rules in predicate (ASP) format as text 
-- 
-- Copyright 2012,2013 Vesa Luukkala
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

module FactRender where

import qualified Data.List as List
import qualified Data.Map as Map
import System.IO.Unsafe
import Data.IORef 


import AspParse
import TxtRender 

-- This should be temporary as there is some copied code from RDF render
import RdfRender

-- An unsafe counter 
-- mknext :: (Num a) => IO (IO a)
-- mknext :: IO (IO Integer)
mknext = do 
  ref <- newIORef 0
  return (
    do 
      modifyIORef ref (+1)
      readIORef ref)

-- To use:
-- let a = unsafectr()
-- let myid = getnext(a)  
unsafectr = System.IO.Unsafe.unsafePerformIO (FactRender.mknext)


getnext :: IO Integer -> Integer
-- getnext :: IO Int -> Int
getnext c = System.IO.Unsafe.unsafePerformIO (c)

-- Another unsafe hack to keep the variablename -> ID mapping
-- To get rid of the we need refactoring the tree walking which produces 
-- the output string. 

varmap = unsafePerformIO $ newIORef Map.empty 

--- Start here the fact rendering 
factrender :: (Show t) => [Char] -> Bool-> Either t [Rules] -> [Char]      
factrender n flag rb  = 
    case rb of 
      Left l -> "error:" ++ show(l)
      Right r -> 
            -- let aid = (myrand())::Int in 
            -- let aid = 0 in 
            let ctr = FactRender.unsafectr in 
            let aid = FactRender.getnext(ctr::IO Integer) in 
            let txt = (n ++ (List.foldr (factitem aid ctr) "" (reverse r))) in 
            let maxctr = FactRender.getnext(ctr) in 
               txt ++ ("freectr(" ++ show(maxctr) ++ ").\n")

txtcomment t = 
  let l = lines t in 
  -- let newl = map (\t -> "% " ++ t ++ "\n") l in 
  -- unwords newl
  let newl = List.map (\t -> "% " ++ t ) l in 
  unlines newl

-- This one will have its own "namespace", that is it may be 
-- that variables with same lexical name should have same ID. 
-- factitem :: Show a => a -> IO Int -> Rules -> [Char] -> [Char]
factitem :: Show a => a -> IO Integer -> Rules -> [Char] -> [Char]
factitem id ctr i accu =
-- factitem id i accu =      
    -- 1st we make an unique identifier for this rule
    -- let ruleid = (myrand())::Int in 
    -- let ruleid = (unsafectr())::Int in 
    -- let ruleid = (id + 1) in 
    let ruleid = FactRender.getnext(ctr)::Integer in 
    -- let preflink = show(id) ++ ",http://m3.org/rls#partof," ++ show(ruleid) ++ "\n" in 
    let preflink = "hasrule(" ++ show(id) ++ "," ++ show(ruleid) ++ ").\n" in 
    let cnstlink = "hasconst(" ++ show(id) ++ "," ++ show(ruleid) ++ ").\n" in 
    let ctext = txtcomment(txtitem i "") in 
    case i of
      Rule b l -> 
                  let numbodies = show(List.length l) in 
                  accu ++ ctext ++ preflink ++ 
                  "rule(" ++ show(ruleid) ++ ")." ++ "\n" ++
                  "bodycount(" ++ show(ruleid) ++ "," ++ numbodies ++  ")." ++ "\n" ++
                  -- head(factbody "head" ruleid b []) ++ 
                  head(factbody "" ruleid ruleid ctr b []) ++ 
                  (List.foldr (++) "" (List.foldr (factbody "body" ruleid ruleid ctr) [] l)) 
                 -- "" 
      Deny l ->
                let numbodies = show(List.length l) in 
                 accu ++ ctext ++ preflink ++ 
                "constraint(" ++ show(ruleid) ++ ")." ++ "\n" ++
                "bodycount(" ++ show(ruleid) ++ "," ++ numbodies ++  ")." ++ "\n" ++
                (List.foldr (++) "" (List.foldr (factbody "body" ruleid ruleid ctr) [] l))
                -- ++ 
                -- ""
      Fact l -> accu ++ ctext ++ preflink ++ 
                "assert(" ++ show(ruleid) ++ ")." ++ "\n" ++
                (List.foldr (++) "" (List.foldr (factbody "head" ruleid ruleid ctr) [] l))
                -- ++ 
                -- ""
      Show l -> accu 
      Hide l -> accu 
      GShow l -> accu 
      GHide l -> accu 
      External l -> accu 
      Function l -> accu 
      Minimize l -> accu 
      Maximize l -> accu 
      Computes n l -> accu 
      Emptyset -> accu 
      Consts l -> accu ++ ctext ++ cnstlink ++ 
                  "constdef(" ++ show(ruleid) ++ ")." ++ "\n" ++
                  (List.foldr (++) "" (List.foldr (factbody "" ruleid ruleid ctr) [] l))

-- factcard :: [Char] -> Int -> IO Int -> Body -> [[Char]] -> [[Char]]
factcard :: [Char] -> Integer -> Integer -> IO Integer -> Body -> [[Char]] -> [[Char]]
factcard rel ruleid parentid ctr r accu = 
   let previd = 0 in 
   let newaccu = (accu ++ ["tlist''(" ++ show(parentid) ++ "," ++ show(previd) ++ "," ++ "jop" ++ ").\n" ] ++ (factbody "type" ruleid parentid ctr r accu)) 
   -- in (newaccu, (previd+1))
      in newaccu 

--- A wrapper around factbody, keeping track of the 
--- items in a typed or qualified list. 
-- factcard' :: [Char] -> Int -> IO Int -> Body -> ([[Char]], Int) -> ([[Char]], Int)
factcard' :: [Char] -> Integer -> Integer -> IO Integer -> Body -> ([[Char]], Int) -> ([[Char]], Int)
factcard' rel ruleid parentid ctr r (accu, previd) = 
   let nxt = 0 in 
   --- let newaccu = (accu ++ ["tlist(" ++ show(parentid) ++ "," ++ show(previd) ++ "," ++ show(nxt) ++ ").\n" ] ++ (factbody "type" parentid ctr r accu)) 
   -- let newaccu = (accu ++ (factbody "typed" parentid ctr r accu)) 
   -- let newaccu = (accu ++ (factbody rel parentid ctr r accu)) 
   let newaccu = (factbody rel ruleid parentid ctr r accu)
   -- let newaccu = tmp ++ ["tlist'(" ++ show(parentid) ++ "," ++ show(previd) ++ "," ++ show(nxt) ++ ").\n" ] 
   in (newaccu, (previd+1))
   --   in newaccu 

--- A wrapper around factbody, keeping track of the 
--- items in a typed or qualified list. 
-- factcard' :: [Char] -> Int -> IO Int -> Body -> ([[Char]], Int) -> ([[Char]], Int)
factcount :: [Char] -> Integer -> Integer -> IO Integer -> Body -> ([[Char]], Int) -> ([[Char]], Int)
factcount rel ruleid parentid ctr r (accu, previd) = 
   let nxt = 0 in 
   --- let newaccu = (accu ++ ["tlist(" ++ show(parentid) ++ "," ++ show(previd) ++ "," ++ show(nxt) ++ ").\n" ] ++ (factbody "type" parentid ctr r accu)) 
   -- let newaccu = (accu ++ (factbody "typed" parentid ctr r accu)) 
   -- let newaccu = (accu ++ (factbody rel parentid ctr r accu)) 
   let newaccu = (factbody rel ruleid parentid ctr r accu)
   -- let newaccu = tmp ++ ["tlist'(" ++ show(parentid) ++ "," ++ show(previd) ++ "," ++ show(nxt) ++ ").\n" ] 
   in (newaccu, (previd+1))
   --   in newaccu 


-- factbody :: [Char] -> Int -> IO Int -> Body -> [[Char]] -> [[Char]]
factbody :: [Char] -> Integer -> Integer -> IO Integer -> Body -> [[Char]] -> [[Char]]
factbody rel ruleid parentid ctr r accu = 
  -- let factid = (myrand())::Int in 
  -- let factid = (parentid+1) in 
  let factid = FactRender.getnext(ctr) in 
  case r of
    Plain n a nonneg -> let myrel = (if rel == "" then "head" else rel)
                        in 
                        -- let embed = (myrand())::Int in 
                         let embed = FactRender.getnext(ctr) in 
                         let arity = show(List.length a) in 
                        accu ++ 
                        [
                          (if nonneg then ("pos(" ++ show(factid) ++ ").\n")
                           else ("neg(" ++ show(factid) ++ ").\n")) ++ 
                          myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ")." ++ "\n" ++
                          "rulepred(" ++ show(parentid) ++ "," ++ show(factid) ++ ")." ++ "\n" ++ 
                          "arity(" ++ show(factid) ++ "," ++ arity ++ ")." ++ "\n" ++ 
                          "pred(" ++ show(factid) ++ "," ++ show(unatom(n)) ++ ")." ++ "\n" ++
                          --- "fact" ++ show(factid) ++ ",http://m3.org/rls#name," ++ 
                          --- show(unatom(n)) ++ "\n" ++ 
                        factargs ruleid factid a ctr]
    Card min max b nonneg -> let myrel = (if rel == "" then "head" else rel)
                        in 
                          accu ++ --- ["YYYCard\n"] ++ 
                       [(if nonneg then "" else ("neg(" ++ show(factid) ++ ").\n")) ++ 
                         myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" ++
                         "card(" ++ show(factid) ++ ").\n" ++ 
                        (List.foldr (++) "" 
                         -- (let content = (foldr (factbody "body" factid ctr) [] b) in content)) ++
                         (let (content,localid) = (List.foldr (factcard' "body" ruleid factid ctr) ([],0) b) in content)) 
                        ++ 
                        (-- let minexprid = (myrand())::Int in 
                         let minexprid = FactRender.getnext(ctr) in  
                         if min == (Sym (Const "any")) then "" else 
                             "mincard(" ++ show(factid) ++ "," ++ show(minexprid) ++ ").\n" ++ 
                                       (unfactmyexpr min ruleid minexprid ctr)) ++
                        (-- let maxexprid = (myrand())::Int in 
                          let maxexprid = FactRender.getnext(ctr) in  
                         if max == (Sym (Const "any")) then "" else 
                             "maxcard(" ++ show(factid) ++ "," ++  show(maxexprid) ++ ").\n" ++ 
                                       (unfactmyexpr max ruleid maxexprid ctr))
                       ]
    Count min max b nonneg -> let myrel = (if rel == "" then "head" else rel)
                        in 
                          accu ++ -- ["YYYCount\n"] ++ 
                       [(if nonneg then "" else ("neg(" ++ show(factid) ++ ").\n")) ++ 
                         myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" ++
                         "weigh(" ++ show(factid) ++ ").\n" ++ 
                        (List.foldr (++) "" 
                         -- (let content = (foldr (factbody "body" factid ctr) [] b) in content)) ++
                         (let (content,localid) = (List.foldr (factcard' "body" ruleid factid ctr) ([],0) b) in content)) 
                        ++ 
                        (-- let minexprid = (myrand())::Int in 
                         let minexprid = FactRender.getnext(ctr) in  
                         if min == (Sym (Const "any")) then "" else 
                             "mincount(" ++ show(factid) ++ "," ++ show(minexprid) ++ ").\n" ++ 
                                       (unfactmyexpr min ruleid minexprid ctr)) ++
                        (-- let maxexprid = (myrand())::Int in 
                          let maxexprid = FactRender.getnext(ctr) in  
                         if max == (Sym (Const "any")) then "" else 
                             "maxcount(" ++ show(factid) ++ "," ++  show(maxexprid) ++ ").\n" ++ 
                                       (unfactmyexpr max ruleid maxexprid ctr))
                       ]
    Optimize minmax b nonneg -> let myrel = (if rel == "" then "head" else rel)
                        in 
                          accu ++ 
                       [(if nonneg then "" else ("neg(" ++ show(factid) ++ ").\n")) ++ 
                         myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" ++
                         (if minmax == True then "optimize(" ++ show(factid) ++ ", max).\n" 
                                            else "optimize(" ++ show(factid) ++ ", min).\n") ++ 
                        (List.foldr (++) "" 
                         (let (content,localid) = (List.foldr (factcard' "body" ruleid factid ctr) ([],0) b) in content)) 
                       ]
    Typed b -> let myrel = (if rel == "" then "head" else rel)
                        in 
                   accu ++ -- ["YYYTyped\n"] ++ 
                   [myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" ++
                     "composite(" ++ show(factid) ++ ").\n", -- Z1
                     -- show(factid) ++ ",rdf:type,http://m3.org/rls#qual\n" ++
                     (List.foldr (++) ""
                      (typeargs ruleid factid ctr b))
                      {--
                      (foldr
                       -- (factbody "type" factid ctr) [] b -- Z2
                       (factbody "qual" factid ctr) [] b 
                      ))
                      --}
                   ] 
    Weighed e1 b1 nonneg -> -- let wid = (myrand())::Int in
                     -- let eid = (myrand())::Int in
                     let wid = FactRender.getnext(ctr) in
                     let eid = FactRender.getnext(ctr) in
                     let myrel = (if rel == "" then "head" else rel)
                     in 
                     accu ++ -- ["YYYWeighed\n"] ++ 
                     [ (if nonneg then ("pos(" ++ show(parentid) ++ ").\n")
                        else ("neg(" ++ show(parentid) ++ ").\n")) ++
                        myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" ++
                        (List.foldr (++) "" 
                         -- (let (content,localid) = (List.foldr (factcount "body" factid ctr) ([],0) b1) in content)) 
                         (let (content,localid) = (List.foldr (factcount "body" ruleid factid ctr) ([],0) [b1]) in content)) 
                        ++ 
                        (if e1 == (Sym (Const "any")) then "" else 
                             "weight(" ++ show(factid) ++ "," ++ show(eid) ++ ").\n" ++ 
                                       (unfactmyexpr e1 ruleid eid ctr))
                     ]
    BExpr op b1 b2 -> -- let lid = (myrand())::Int in
                      -- let rid = (myrand())::Int in
                      let lid = FactRender.getnext(ctr) in
                      let rid = FactRender.getnext(ctr) in
              accu ++ 
              [-- show (factid) ++ "). %X5\n" ++ 
              "bexpr(" ++ show(parentid) ++ "," ++ show (factid) ++ ").\n" ++ 
              "bop(" ++ show (factid) ++ "," ++ "\"" ++ (unbop op) ++ "\"" ++ ").\n" ++ 
              "larg(" ++ show(factid) ++ "," ++ show(lid) ++ ").\n" ++ (unfactmyexpr b1 ruleid lid ctr) ++ 
              "rarg(" ++ show(factid) ++ "," ++ show(rid) ++ ").\n" ++ (unfactmyexpr b2 ruleid rid ctr)  ]
              
              --- show (factid) ++ ",http://m3.org/rls#bop,\"" ++ (unbop op) ++ "\"\n" ++ 
              --- show (factid) ++ ",http://m3.org/rls#left," ++ (unrdfmyexpr b1 lid ) ++ 
              --- show (factid) ++ ",http://m3.org/rls#right," ++ (unrdfmyexpr b2 rid )]
    Assign nm e -> 
           let nid = FactRender.getnext(ctr) in
           let eid = FactRender.getnext(ctr) in
           accu ++ 
           [
           -- "constdef(" ++ show(factid) ++ ").\n" ++ 
           "constn(" ++ show(parentid) ++ "," ++ show(nid) ++ ").\n" ++ 
           "constval(" ++ show(parentid) ++ "," ++ show(eid) ++ ").\n" ++ 
           (unfactcatom nm nid ruleid) ++ 
           (unfactmyexpr e ruleid eid ctr)
           ]
    -- Empty -> accu ++ [" NONE "]
    Assignment nm e nonneg -> 
           let nid = FactRender.getnext(ctr) in
           let eid = FactRender.getnext(ctr) in
           accu ++ 
           [
           (if nonneg then ("pos(" ++ show(parentid) ++ ").\n")
                           else ("neg(" ++ show(parentid) ++ ").\n")) ++
           "lefthand(" ++ show(parentid) ++ "," ++ show(nid) ++ ").\n" ++ 
           "value(" ++ show(parentid) ++ "," ++ show(eid) ++ ").\n" ++ 
           (unfactcatom nm nid ruleid) ++ 
           (let (content,localid) = (List.foldr (factcard' "body" ruleid eid ctr) ([],0) [e]) in List.head (content))
           -- (factbody "body" eid ctr)
           -- (unfactmyexpr e eid ctr)
           ]
    Empty -> accu 
    Comment s -> accu ++ ["% " ++ s]
    Arity a n -> accu

factargs ruleid parentid a ctr = 
    if length a == 0 
    then ""
    else 
        -- let (res,ids) = foldr alist ("",parentid) a in res
        -- let (res,ids) = foldl alist ("",parentid) (reverse a) in res
        -- let (res,ids) = foldl alist ("",parentid) a in res
        let (res,ids) = List.foldl alist ("",0) a in res
        -- let (res,ids) = foldl alist ("",parentid) (map unatom a) in res
        -- show(a)
    where 
      alist (accu,previd) i = 
          -- let argid = (myrand())::Int in 
          -- let exprid = (myrand())::Int in 
          let argid = FactRender.getnext(ctr) in 
          let exprid = FactRender.getnext(ctr) in 
          let new_ac = accu ++ 
                       (unfactmyexpr i ruleid argid ctr) ++ 
                       "alist(" ++ show(parentid) ++ "," ++ (show (previd+1)) ++ "," ++ show(argid) ++ ").\n" 
                       -- "nxt(" ++ show(previd) ++ "," ++ show(argid) ++ ").\n"
              in
                -- (new_ac,argid)
                (new_ac,(previd + 1))

-- typeargs parentid a ctr = 
typeargs ruleid parentid ctr a =       
    if length a == 0 
    then [""]
    else 
        let (res,ids) = List.foldl typelist ([],0) a in 
          (["rulecomposite(" ++ show(ruleid) ++ "," ++ show(parentid) ++ ").\n"] ++ res)
    where 
      typelist (accu,previd) i = 
          -- let argid = (myrand())::Int in 
          -- let exprid = (myrand())::Int in 
          let argid = FactRender.getnext(ctr) in 
          let exprid = FactRender.getnext(ctr) in 
          let new_ac = accu ++ ["tlist(" ++ show(parentid) ++ "," ++ (show (previd+1)) ++ "," ++ show(argid) ++ ").\n"] ++ (factbody "qual" ruleid argid ctr i []) 
              in
                (new_ac,(previd + 1))

unfactcatom v id ruleid = 
    case v of 
      Const a -> -- show (id) ++ "). % unfactcatom Const\n" ++ 
                 "cnst(" ++ show(id) ++ "," ++ show(a) ++ ").\n"
      Var a -> -- show (id) ++ "). % unfactcatom Var \n" ++ -- "cvar
               "var(" ++ show(id) ++ "," ++ show(a) ++ ").\n" ++
               "rulevar(" ++ show(ruleid) ++ "," ++ show(id) ++ ").\n"

unfactarith op a1 a2 ruleid exprid ctr = 
    -- let lid = (myrand())::Int in
    -- let rid = (myrand())::Int in
    let lid = FactRender.getnext(ctr) in
    let rid = FactRender.getnext(ctr) in
    -- show(exprid) ++ "). % X1\n" ++ 
    "arithexpr(" ++ show (exprid) ++ ").\n" ++ 
    "op(" ++ show (exprid) ++ "," ++ "\"" ++ (unop op)  ++ "\"" ++ ").\n" ++ 
    -- show (exprid) ++ ",rdf:type,http://m3.org/rls#arithexpr\n" ++ 
    -- show (exprid) ++ ",http://m3.org/rls#op,\"" ++ (unop op) ++ "\"\n" ++ 
    -- Perhaps we should have the order here explicitely rather than just lines?
    -- The same mechanism as tlist could work here 
    -- "arg(" ++ show(exprid) ++ "," ++ (unfactmyexpr a1 lid ctr) ++ "). % Y2\n" ++ 
    -- "arg(" ++ show(exprid) ++ "," ++ (unfactmyexpr a2 rid ctr) ++ "). % Y1\n" 
    "larg(" ++ show(exprid) ++ "," ++ show(lid) ++ ").\n" ++ (unfactmyexpr a1 ruleid lid ctr) ++ 
    "rarg(" ++ show(exprid) ++ "," ++ show(rid) ++ ").\n" ++ (unfactmyexpr a2 ruleid rid ctr) 

unfactmyexpr a ruleid exprid ctr = 
    case a of 
      Sym s -> (unfactcatom s exprid ruleid)
      Number s -> (unfactcatom s exprid ruleid)
      Alternative l -> ("altlist(" ++ show(exprid) ++ ").\n") ++ (unaltlist l ctr ruleid exprid)
      Arith op a1 a2 -> (unfactarith op a1 a2 ruleid exprid ctr)
      Func n a nonneg -> let embed = FactRender.getnext(ctr) in 
                          "func" ++ "(" ++ show(exprid) ++ "," ++ show(embed) ++ ")." ++ "\n" ++
                          "fname(" ++ show(embed) ++ "," ++ show(unatom(n)) ++ ")." ++ "\n" ++
                          factargs ruleid embed a ctr

unaltlist a ctr ruleid parentid = 
    if length a == 0 
    then ""
    else 
       let (res,ids) = List.foldl mfacts ("",0) a in res
    where 
      mfacts (accu,previd) i = 
          let argid = FactRender.getnext(ctr) in 
          let exprid = FactRender.getnext(ctr) in 
          let new_ac = accu ++ 
                       (unfactmyexpr i ruleid argid ctr) ++ 
                       "altlist(" ++ show(parentid) ++ "," ++ (show (previd+1)) ++ "," ++ show(argid) ++ ").\n" 
              in
                (new_ac,(previd + 1))
