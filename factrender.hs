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

-- Comment this away later, this is for debugging 
-- {-# OPTIONS -Wall #-}

module FactRender where

import qualified Data.List as List
import qualified Data.Map as Map
import System.IO.Unsafe
import Data.IORef 


import AspParse
import TxtRender 

-- This should be temporary as there is some copied code from RDF render
import RdfRender ()

-- An unsafe counter 
-- mknext :: (Num a) => IO (IO a)
mknext :: IO (IO Integer)
mknext = do 
  ref <- newIORef 0
  return (
    do 
      modifyIORef ref (+1)
      readIORef ref)

-- To use:
-- let a = unsafectr()
-- let myid = getnext(a)  
unsafectr :: IO Integer
unsafectr = System.IO.Unsafe.unsafePerformIO (FactRender.mknext)


getnext :: IO Integer -> Integer
getnext c = System.IO.Unsafe.unsafePerformIO (c)

-- Another unsafe hack to keep the variablename -> ID mapping
-- To get rid of the we need refactoring the tree walking which produces 
-- the output string. 

varmap :: IORef (Map.Map k a)
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
               -- txt ++ ("freectr(" ++ show(maxctr) ++ ").\nfreectr(0).\n")
               txt ++ ("freectr(" ++ show(maxctr) ++ ").\n")

txtcomment :: String -> String
txtcomment t = 
  let l = lines t in 
  let newl = List.map (\x -> "% " ++ x ) l in 
  unlines newl

-- The arity of the head.
-- For now it is zero for anything else than plain body. 
getheadarity :: Body -> Int
getheadarity b = 
  case b of 
    Plain n a nonneg -> List.length a
    _ -> 0

getheadname :: Body -> String 
getheadname b = 
  case b of 
    Plain n a nonneg -> 
      case n of 
        Const s -> s 
        _ -> "NONAMEVAR"
    _ -> "NONAME"
              

-- We create the head of a skeleton based on the arity of the 
-- reified head. 
-- skeleton8(Rid, Jid1, Jid2)
mkskeletonhead :: String -> String -> Int -> String 
mkskeletonhead nm vn arity = 
  let nms = enumFromTo 1 arity in 
  let jids = map (\i -> vn ++ show(i)) nms in 
  let args = concat $ List.intersperse "," ("Rid":jids) in 
    nm ++ "(" ++ args ++ ")"
  
mkskeletoncommon :: Integer -> String 
mkskeletoncommon n =
 "  rule(Rid),\n  Rid == " ++ show(n) ++ ",\n"

mkrulemaps :: Int -> String 
mkrulemaps arity = 
  let nms = enumFromTo 1 arity in 
  let bds = map (\i -> "  onerulemap(Rid, Bidx" ++ show(i) ++ ",Predid" ++ show(i) ++ ",Jid" ++ show(i) ++ ",One"  ++ show(i) ++ ")") nms in 
  let bodies = concat $ List.intersperse ",\n" bds in 
    bodies
  
mkconsistentassignments arity =
  let nms = enumFromTo 1 (arity - 1) in 
  let bds = map (\i -> "  consistentassignments(Rid,Bidx" ++ show(i) ++ ",Jid" ++ show(i) ++ ",Bidx" ++ show(i+1) ++ ",Jid"  ++ show(i+1) ++ ")") nms in 
  let bodies = concat $ List.intersperse ",\n" bds in 
    bodies


justskeleton :: Body -> Int -> Integer -> String 
justskeleton b bodycount ruleid = 
  let arity = getheadarity b in 
  let pn = getheadname b in 
  -- let nm = "skeleton" ++ show(ruleid) in 
  let nm = "skeleton" ++ pn in 
  let hd = mkskeletonhead nm "Jid" arity in 
  let common = mkskeletoncommon ruleid in 
  let rulemaps = mkrulemaps arity in 
  let consistency = mkconsistentassignments arity in 
    hd ++ ":-\n" ++ common ++ (if consistency == "" then (rulemaps ++ ".\n") else rulemaps ++ ",\n" ++ consistency ++ ".\n")

mkheadvarstr i = 
   let one = "  headvarval(Rid,Pn,Idx" ++ show(i) ++ ",Vn" ++ show(i) ++ ",Bidx" ++ show(i) ++ ",Pos"  ++ show(i) ++ "),\n" in 
   let two = "  Idx" ++ show(i) ++ " == " ++ show(i) ++ ",\n" in 
   let three = "  alist(Jid" ++ show(i) ++ ",Pos" ++ show(i) ++ ",Vid" ++ show(i) ++ "),\n" in 
   let four = "  cnst(Vid" ++ show(i) ++ ",Val" ++ show(i) ++ ")" in 
     one ++ two ++ three ++ four 

mkheadvarval arity =
  let nms = enumFromTo 1 arity in 
  -- let bds = map (\i -> "  headvarval(Rid,Pn,Idx" ++ show(i) ++ ",Vn" ++ show(i) ++ ",Bidx" ++ show(i) ++ ",Pos"  ++ show(i) ++ ")") nms in 
  let bds = map mkheadvarstr nms in 
  let bodies = concat $ List.intersperse ",\n" bds in 
    bodies

mkskeletonfinal :: Integer -> Int -> String -> String 
mkskeletonfinal ruleid arity rname = 
  -- let nm = "skeletonfinal" ++ show(ruleid) in 
  let nm = "skeletonfinal" ++ rname in 
  let hd = mkskeletonhead nm "Val" arity in 
  -- let link = mkskeletonhead ("skeleton" ++ show(ruleid)) "Jid" arity in 
  let link = mkskeletonhead ("skeleton" ++ rname) "Jid" arity in 
  let final = mkheadvarval arity in 
    hd ++ ":-\n  " ++ link ++ ",\n" ++ final ++ ".\n"

mkskeletonassert :: Integer -> Int -> String -> String -> String 
mkskeletonassert ruleid arity firstarg rname = 
  -- let nm = ("skeletonassert" ++ show(ruleid)) in 
  let nm = ("skeletonassert" ++ rname) in 
  let nms = enumFromTo 1 arity in 
  let jids = map (\i -> "V" ++ show(i)) nms in 
  let args = concat $ List.intersperse "," (firstarg:"Rid":jids) in 
    nm ++ "(" ++ args ++ ")"

mkskeletonderivers hd ruleid arity rname = 
  let bd = mkskeletonassert ruleid arity "NF" rname in bd 

mkalistderivers ruleid arity rname = 
  let nms = enumFromTo 1 arity in 
  let ids = map (\i -> "alist(NF+1," ++ show(i) ++ ",NF+" ++ show(i) ++ "+1) :-" ++ (mkskeletonderivers "XXX" ruleid arity rname) ) nms in 
  let res = concat $ List.intersperse ".\n" (ids) in 
  res

mkcnstderivers ruleid arity rname = 
  let nms = enumFromTo 1 arity in 
  let ids = map (\i -> "cnst(NF+" ++ show(i) ++ "+1,V" ++ show(i) ++ ") :-" ++ (mkskeletonderivers "XXX" ruleid arity rname) ) nms in 
  let res = concat $ List.intersperse ".\n" (ids) in 
  res

  

mkskeletoncreator :: Integer -> Int -> String -> String 
mkskeletoncreator ruleid arity rname = 
  let ctrname = "@nxtctr(N+3)" in 
  let hd = mkskeletonassert ruleid arity ctrname rname in 
  -- let final = mkskeletonhead ("skeletonfinal" ++ show(ruleid)) "V" arity in 
  let final = mkskeletonhead ("skeletonfinal" ++ rname) "V" arity in 
  let one = "  Rid == " ++ show(ruleid) in 
  let two = "  head(Rid,Hid)" in 
  let three = "  arity(Hid,N)" in 
  hd ++ ":-\n  " ++ final ++ ",\n" ++ one ++ ",\n" ++ two ++ ",\n" ++ three ++ ".\n"

mkskeletons :: Body -> Int -> Integer -> String 
mkskeletons b numbodies ruleid = 
  let arity = (getheadarity b) in 
  let nm = (getheadname b) in 
  let justified = justskeleton b numbodies ruleid in 
  let final = mkskeletonfinal ruleid arity nm in 
  let creator = mkskeletoncreator ruleid arity nm in 
  let d1 = "hasrule(1,NF) :- " ++ (mkskeletonderivers "" ruleid arity nm) in 
  let d2 = "pos(NF+1) :- " ++ (mkskeletonderivers "" ruleid arity nm) in 
  let d3 = "newname(NF,\"JOPI\") :- " ++ (mkskeletonderivers "" ruleid arity nm) in 
  let d4 = "head(NF,NF+1) :- " ++ (mkskeletonderivers "" ruleid arity nm) in 
  let d5 = ("pred(NF+1,Pn) :- " ++ (mkskeletonderivers "" ruleid arity nm) ++ ",\n  head(Rid,Hid),\n  pred(Hid,Pn)" ) in 
  let alistd = mkalistderivers ruleid arity nm in 
  let cnstd = mkcnstderivers ruleid arity nm in 
  let d6 = ("arity(NF+1,A) :- " ++ (mkskeletonderivers "" ruleid arity nm) ++ ",\n  head(Rid,Hid),\n  arity(Hid,A)" ) in 
  let d7 = "assert(NF) :- " ++ (mkskeletonderivers "" ruleid arity nm) in 
  "\n" ++ justified ++ "\n" ++ final ++ "\n" ++ creator ++ (concat $ List.intersperse ".\n" [d1,d2,d3,d4,d5,alistd,cnstd,d6,d7]) ++ ".\n\n"


-- This one will have its own "namespace", that is it may be 
-- that variables with same lexical name should have same ID. 
factitem :: Show a => a -> IO Integer -> Rules -> [Char] -> [Char]
factitem fid ctr i accu =
    -- 1st we make an unique identifier for this rule
    -- let ruleid = (myrand())::Int in 
    -- let ruleid = (unsafectr())::Int in 
    -- let ruleid = (id + 1) in 
    let ruleid = FactRender.getnext(ctr)::Integer in 

    -- let bidx = FactRender.unsafectr in 
    let bidx = 1 in 
    -- let bidx = FactRender.getnext(0)::Integer in 

    -- let preflink = show(id) ++ ",http://m3.org/rls#partof," ++ show(ruleid) ++ "\n" in 
    let preflink = "hasrule(" ++ show(fid) ++ "," ++ show(ruleid) ++ ").\n" in 
    let cnstlink = "hasconst(" ++ show(fid) ++ "," ++ show(ruleid) ++ ").\n" in 
    let ctext = txtcomment(txtitem i "") in 
    case i of
      Rule b l -> 
                  let bn = List.length l in 
                  let numbodies = show(bn) in 
                  let (tmplst,_) = factbody "" ruleid ruleid ctr (bidx,False) (b,bidx) ([],0) in 
                  let hdlst = head(tmplst) in 
                  -- let (bodylst,ctr) = (List.foldr (++) "" (List.foldr (factbody "body" ruleid ruleid ctr (bidx,True)) ([],0) (l,bidx))) in 
                  -- Make l amenable for this 
                  let l' = List.zip l [1..toInteger(List.length(l))] in 
                  let (tmplst',ctr') = (List.foldr (factbody "body" ruleid ruleid ctr (bidx,True)) ([],0) l') in 
                  -- let (bodylst,ctr) = (List.foldr (++) "" (List.foldr (factbody "body" ruleid ruleid ctr (bidx,True)) ([],0) (l,bidx))) in 
                  let bodylst = (List.foldr (++) "" tmplst') in 
                  let resultstr = accu ++ ctext ++ preflink ++ 
                                  "rule(" ++ show(ruleid) ++ ")." ++ "\n" ++
                                  "bodycount(" ++ show(ruleid) ++ "," ++ numbodies ++  ")." ++ "\n" ++
                                  -- head(factbody "" ruleid ruleid ctr (bidx,True) b []) ++ 
                                  hdlst ++ 
                                  -- (List.foldr (++) "" (List.foldr (factbody "body" ruleid ruleid ctr (bidx,True)) [] l)) 
                                  bodylst in 
                 -- let meta = mkskeletons b bn ruleid in 
                 let meta = "" in
                 resultstr ++ meta 
                 -- "" 
      Deny l ->
                let numbodies = show(List.length l) in 
                -- let bodylst = (List.foldr (++) "" (List.foldr (factbody "body" ruleid ruleid ctr (bidx,True) ) [] l)) in 
                let l' = List.zip l [1..toInteger(List.length(l))] in 
                let (tmplst',ctr') = (List.foldr (factbody "body" ruleid ruleid ctr (bidx,True)) ([],0) l') in 
                let bodylst = (List.foldr (++) "" tmplst') in 
                accu ++ ctext ++ preflink ++ 
                "constraint(" ++ show(ruleid) ++ ")." ++ "\n" ++
                "bodycount(" ++ show(ruleid) ++ "," ++ numbodies ++  ")." ++ "\n" ++
                -- (List.foldr (++) "" (List.foldr (factbody "body" ruleid ruleid ctr (bidx,True) ) [] l))
                bodylst
                -- ++ 
                -- ""
      Fact l -> 
                let l' = List.zip l [1..toInteger(List.length(l))] in 
                let (tmplst',ctr') = (List.foldr (factbody "head" ruleid ruleid ctr (bidx,False)) ([],0) l') in 
                let bodylst = (List.foldr (++) "" tmplst') in 
                -- let bodylst = (List.foldr (++) "" (List.foldr (factbody "head" ruleid ruleid ctr (bidx,False)) [] l)) in 
                accu ++ ctext ++ preflink ++ 
                "assert(" ++ show(ruleid) ++ ")." ++ "\n" ++
                -- (List.foldr (++) "" (List.foldr (factbody "head" ruleid ruleid ctr (bidx,True)) [] l))
                bodylst
                -- ++ 
                -- ""
      Show _ -> accu 
      Hide _ -> accu 
      GShow _ -> accu 
      GHide _ -> accu 
      External _ -> accu 
      Function _ -> accu 
      Minimize _ -> accu 
      Maximize _ -> accu 
      RComment _ -> accu 
      Computes _ _ -> accu 
      Emptyset -> accu 
      Consts l -> 
                  let l' = List.zip l [1..toInteger(List.length(l))] in 
                  let (tmplst',ctr') = (List.foldr (factbody "body" ruleid ruleid ctr (bidx,False)) ([],0) l') in 
                  let bodylst = (List.foldr (++) "" tmplst') in 
                  accu ++ ctext ++ cnstlink ++ 
                  "constdef(" ++ show(ruleid) ++ ")." ++ "\n" ++ bodylst 
                  -- (List.foldr (++) "" (List.foldr (factbody "" ruleid ruleid ctr (bidx,True)) [] l))

--- A wrapper around factbody, keeping track of the 
--- items in a typed or qualified list. 
factcard' :: [Char] -> Integer -> Integer -> IO Integer -> (Integer, Bool) -> Body -> ([[Char]], Int) -> ([[Char]], Int)
factcard' relstr ruleid parentid ctr (idx,useidx) r (accu, previd) = 
   let accu' = (if useidx then let bidx = idx in accu ++ ["bodylist(" ++ show(parentid) ++ "," ++ show(bidx) ++ "," ++ show(previd) ++ ").\n"] else accu) in 
   let (newaccu,ctr') = factbody relstr ruleid parentid ctr (idx,False) (r,0) (accu',0)
   -- let newaccu = (factbody relstr ruleid parentid ctr (idx,useidx) r accu')
   in (newaccu, (previd+1))
   --   in newaccu 

--- A wrapper around factbody, keeping track of the 
--- items in a typed or qualified list. 
factcount :: [Char] -> Integer -> Integer -> IO Integer -> (Integer, Bool) -> Body -> ([[Char]], Int) -> ([[Char]], Int)
factcount relstr ruleid parentid ctr (idx,useidx) r (accu, previd) = 
   -- let nxt = 0 in 
   let accu' = (if useidx then let bidx = idx in accu ++ ["bodylist(" ++ show(parentid) ++ "," ++ show(bidx) ++ "," ++ show(previd) ++ ").\n"] else accu) in 
   let (newaccu,ctr') = factbody relstr ruleid parentid ctr (idx,False) (r,0) (accu',0)

   -- let newaccu = (factbody relstr ruleid parentid ctr (idx,useidx) r accu')

   -- let newaccu = tmp ++ ["tlist'(" ++ show(parentid) ++ "," ++ show(previd) ++ "," ++ show(nxt) ++ ").\n" ] 
   in (newaccu, (previd+1))
   --   in newaccu 


-- XXX Actually we should do this
-- factbody :: [Char] -> Integer -> Integer -> IO Integer -> Maybe IO Integer -> Body -> [[Char]] -> [[Char]]
-- of perhaps MaybeT Integer IO using a monad transformer
-- but now we cheat and do it like this:

-- factbody :: [Char] -> Int -> IO Int -> Body -> [[Char]] -> [[Char]]
factbody :: [Char] -> Integer -> Integer -> IO Integer -> (Integer, Bool) -> (Body,Integer) -> ([[Char]],Integer) -> ([[Char]], Integer)
-- factbody rel ruleid parentid ctr r accu = 
factbody relstr ruleid parentid ctr (oidx,useidx) (r,idx) (accu,bodyidx) = 
  -- let factid = (myrand())::Int in 
  -- let factid = (parentid+1) in 
  let factid = FactRender.getnext(ctr) in 
  -- bidx is the index of the body, we advance it only if this is a toplevel construct,
  -- that is, a fact. It may be that cardinals and others call us and they are expected 
  -- to have handled this. 
  let (accu',bidx') = (if useidx then let bidx = idx in (accu ++ ["bodylist(" ++ show(parentid) ++ "," ++ show(bidx) ++ "," ++ show(factid) ++ ").\n"], (idx+1)) else (accu,idx)) in 
  case r of
    Plain n a nonneg -> let myrel = (if relstr == "" then "head" else relstr)
                        in 
                        -- let embed = (myrand())::Int in 
                         -- let embed = FactRender.getnext(ctr) in 
                         let arity = show(List.length a) in 
                         let ln0 = (if nonneg then ("pos(" ++ show(factid) ++ ").\n") else ("neg(" ++ show(factid) ++ ").\n")) in 
                         let ln1 = ln0 ++ myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ")." ++ "\n" in 
                         let ln2 = ln1 ++ "rulepred(" ++ show(parentid) ++ "," ++ show(factid) ++ ")." ++ "\n" in 
                         let ln3 = ln2 ++ "arity(" ++ show(factid) ++ "," ++ arity ++ ")." ++ "\n" in 
                         let ln4 = ln3 ++ "pred(" ++ show(factid) ++ "," ++ show(unatom(n)) ++ ")." ++ "\n" in 
                         let ln5 = ln4 ++ factargs ruleid factid a ctr in 
                         let resaccu = accu' ++ [ln5] in 
                        (resaccu,bidx')
    Card minv maxv b nonneg -> let myrel = (if relstr == "" then "head" else relstr)
                        in 
                          -- let resaccu = accu' ++ --- ["YYYCard\n"] ++ 
                          let ln0 = (if nonneg then "" else ("neg(" ++ show(factid) ++ ").\n")) in 
                          let ln1 = ln0 ++ myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" in 
                          let ln2 = ln1 ++ "card(" ++ show(factid) ++ ").\n" in 
                          let crd = (List.foldr (++) "" 
                                    (let (content,localid) = (List.foldr (factcard' "body" ruleid factid ctr (bidx',False)) ([],0) b) in content)) in 
                          let ln3 = ln2 ++ crd in 
                          let minexprid = FactRender.getnext(ctr) in -- let minexprid = (myrand())::Int in 
                          let mne = if minv == (Sym (Const "any")) then "" 
                                    else  
                                    "mincard(" ++ show(factid) ++ "," ++ show(minexprid) ++ ").\n" ++ (unfactmyexpr minv ruleid minexprid ctr) in 
                          let maxexprid = FactRender.getnext(ctr) in -- let maxexprid = (myrand())::Int in 
                          let mxe = if maxv == (Sym (Const "any")) then "" 
                                    else "maxcard(" ++ show(factid) ++ "," ++  show(maxexprid) ++ ").\n" ++ (unfactmyexpr maxv ruleid maxexprid ctr) in 
                          let ln4 = ln3 ++ crd ++ mne ++ mxe in 
                          let resaccu = accu' ++ [ln4] in 
                        (resaccu,idx)
    Count minv maxv b nonneg -> let myrel = (if relstr == "" then "head" else relstr)
                        in 
                          -- let resaccu = accu' ++ -- ["YYYCount\n"] ++ 
                          let ln0 = (if nonneg then "" else ("neg(" ++ show(factid) ++ ").\n")) in 
                          let ln1 = ln0 ++ myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" in 
                          let ln2 = ln1 ++ "weigh(" ++ show(factid) ++ ").\n" in 
                          let crd = (List.foldr (++) "" 
                                    (let (content,localid) = (List.foldr (factcard' "body" ruleid factid ctr (bidx',False)) ([],0) b) in content)) in 
                          let minexprid = FactRender.getnext(ctr) in  
                          let mce = if minv == (Sym (Const "any")) then "" 
                                    else "mincount(" ++ show(factid) ++ "," ++ show(minexprid) ++ ").\n" ++ (unfactmyexpr minv ruleid minexprid ctr) in 
                          let maxexprid = FactRender.getnext(ctr) in  
                          let mxe = if maxv == (Sym (Const "any")) then "" 
                                    else "maxcount(" ++ show(factid) ++ "," ++  show(maxexprid) ++ ").\n" ++ (unfactmyexpr maxv ruleid maxexprid ctr) in 
                          let ln3 = ln2 ++ crd ++ mce ++ mxe in 
                          let resaccu = accu' ++ [ln3] in 
                          (resaccu,idx)
    Optimize minmax b nonneg -> let myrel = (if relstr == "" then "head" else relstr)
                        in 
                           -- let resaccu = accu' ++ 
                           let ln0 = (if nonneg then "" else ("neg(" ++ show(factid) ++ ").\n")) in 
                           let ln1 = ln0 ++ myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" in 
                           let mm = if minmax == True then "optimize(" ++ show(factid) ++ ", max).\n" 
                                    else "optimize(" ++ show(factid) ++ ", min).\n" in 
                           let crd = (List.foldr (++) "" 
                                     (let (content,localid) = (List.foldr (factcard' "body" ruleid factid ctr (bidx',False)) ([],0) b) in content)) in 
                           let ln2 = ln1 ++ mm ++ crd in 
                           let resaccu = accu' ++ [ln2] in 
                               (resaccu, idx)
    Typed b -> let myrel = (if relstr == "" then "head" else relstr)
                        in 
                   let resaccu = accu' ++ -- ["YYYTyped\n"] ++ 
                                 [myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" ++
                                 "composite(" ++ show(factid) ++ ").\n", -- Z1
                                 -- show(factid) ++ ",rdf:type,http://m3.org/rls#qual\n" ++
                                 (List.foldr (++) ""
                                 (typeargs ruleid factid ctr (bidx',False) b))
                                                       {--
                                                       (foldr
                                                         -- (factbody "type" factid ctr) [] b -- Z2
                                                         (factbody "qual" factid ctr) [] b 
                                                         ))
                                                         --}
                                  ] in (resaccu,idx)
    Weighed e1 b1 nonneg -> -- let wid = (myrand())::Int in
                     -- let eid = (myrand())::Int in
                     -- let wid = FactRender.getnext(ctr) in
                     let eid = FactRender.getnext(ctr) in
                     let myrel = (if relstr == "" then "head" else relstr)
                     in 
                     let resaccu = accu' ++ -- ["YYYWeighed\n"] ++ 
                                   [ (if nonneg then ("pos(" ++ show(parentid) ++ ").\n")
                                     else ("neg(" ++ show(parentid) ++ ").\n")) ++
                                     myrel ++ "(" ++ show(parentid) ++ "," ++ show(factid) ++ ").\n" ++
                                     (List.foldr (++) "" 
                                     -- (let (content,localid) = (List.foldr (factcount "body" factid ctr) ([],0) b1) in content)) 
                                     (let (content,localid) = (List.foldr (factcount "body" ruleid factid ctr (bidx',False)) ([],0) [b1]) in content)) 
                                     ++ 
                                     (if e1 == (Sym (Const "any")) then "" else 
                                     "weight(" ++ show(factid) ++ "," ++ show(eid) ++ ").\n" ++ 
                                       (unfactmyexpr e1 ruleid eid ctr))
                                     ] in (resaccu, idx)
    BExpr op b1 b2 -> -- let lid = (myrand())::Int in
                      -- let rid = (myrand())::Int in
                      let lid = FactRender.getnext(ctr) in
                      let rid = FactRender.getnext(ctr) in
              let resaccu = accu' ++ 
                          [-- show (factid) ++ "). %X5\n" ++ 
                          "bexpr(" ++ show(parentid) ++ "," ++ show (factid) ++ ").\n" ++ 
                          "bop(" ++ show (factid) ++ "," ++ "\"" ++ (unbop op) ++ "\"" ++ ").\n" ++ 
                          "larg(" ++ show(factid) ++ "," ++ show(lid) ++ ").\n" ++ (unfactmyexpr b1 ruleid lid ctr) ++ 
                          "rarg(" ++ show(factid) ++ "," ++ show(rid) ++ ").\n" ++ (unfactmyexpr b2 ruleid rid ctr)  ]
                          in (resaccu, idx)              
              --- show (factid) ++ ",http://m3.org/rls#bop,\"" ++ (unbop op) ++ "\"\n" ++ 
              --- show (factid) ++ ",http://m3.org/rls#left," ++ (unrdfmyexpr b1 lid ) ++ 
              --- show (factid) ++ ",http://m3.org/rls#right," ++ (unrdfmyexpr b2 rid )]
    Assign nm e -> 
           let nid = FactRender.getnext(ctr) in
           let eid = FactRender.getnext(ctr) in
           let resaccu = accu' ++ 
                         [
                         -- "constdef(" ++ show(factid) ++ ").\n" ++ 
                         "constn(" ++ show(parentid) ++ "," ++ show(nid) ++ ").\n" ++ 
                         "constval(" ++ show(parentid) ++ "," ++ show(eid) ++ ").\n" ++ 
                         (unfactcatom nm nid ruleid) ++ 
                         (unfactmyexpr e ruleid eid ctr)
                         ] in (resaccu,idx)
    -- Empty -> accu ++ [" NONE "]
    Assignment nm e nonneg -> 
           let nid = FactRender.getnext(ctr) in
           let eid = FactRender.getnext(ctr) in
           let resaccu = accu' ++ 
                         [
                         (if nonneg then ("pos(" ++ show(parentid) ++ ").\n")
                           else ("neg(" ++ show(parentid) ++ ").\n")) ++
                           "lefthand(" ++ show(parentid) ++ "," ++ show(nid) ++ ").\n" ++ 
                           "value(" ++ show(parentid) ++ "," ++ show(eid) ++ ").\n" ++ 
                           (unfactcatom nm nid ruleid) ++ 
                           (let (content,localid) = (List.foldr (factcard' "body" ruleid eid ctr (bidx', False)) ([],0) [e]) in List.head (content))
                           -- (factbody "body" eid ctr)
                           -- (unfactmyexpr e eid ctr)
                           ] in (resaccu,idx)
    Empty -> (accu, idx)
    Comment s -> ((accu ++ ["% " ++ s]), idx)
    Arity a n -> (accu,idx)

-- The types stop compiling 
-- factargs :: (Show a, Num a) => a -> Integer -> [MyExpr] -> IO Integer -> [Char]
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

-- Seems to stop compilation
-- typeargs :: Integer -> a -> IO Integer -> (IO Integer, t) -> [Body] -> [[Char]]
typeargs ruleid parentid ctr (idx,useidx) a =       
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
          -- let exprid = FactRender.getnext(ctr) in 
          let (fbd,_) = (factbody "qual" ruleid argid ctr (idx,useidx) (i,0) ([],0)) in 
          let new_ac = accu ++ ["tlist(" ++ show(parentid) ++ "," ++ (show (previd+1)) ++ "," ++ show(argid) ++ ").\n"] ++ fbd 
              in
                (new_ac,(previd + 1))

unfactcatom v aid ruleid = 
    case v of 
      Const a -> -- show (id) ++ "). % unfactcatom Const\n" ++ 
                 "cnst(" ++ show(aid) ++ "," ++ show(a) ++ ").\n"
      Var a -> -- show (id) ++ "). % unfactcatom Var \n" ++ -- "cvar
               "var(" ++ show(aid) ++ "," ++ show(a) ++ ").\n" ++
               "rulevar(" ++ show(ruleid) ++ "," ++ show(aid) ++ ").\n"

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
      Func n l nonneg -> let embed = FactRender.getnext(ctr) in 
                          "func" ++ "(" ++ show(exprid) ++ "," ++ show(embed) ++ ")." ++ "\n" ++
                          "fname(" ++ show(embed) ++ "," ++ show(unatom(n)) ++ ")." ++ "\n" ++
                          factargs ruleid embed l ctr

unaltlist :: Show a => [MyExpr] -> IO Integer -> a -> Integer -> [Char]
unaltlist a ctr ruleid parentid = 
    if length a == 0 
    then ""
    else 
       let (res,ids) = List.foldl mfacts ("",0) a in res
    where 
      mfacts (accu,previd) i = 
          let argid = FactRender.getnext(ctr) in 
          -- let exprid = FactRender.getnext(ctr) in 
          let new_ac = accu ++ 
                       (unfactmyexpr i ruleid argid ctr) ++ 
                       "altlist(" ++ show(parentid) ++ "," ++ (show (previd+1)) ++ "," ++ show(argid) ++ ").\n" 
              in
                (new_ac,(previd + 1))
