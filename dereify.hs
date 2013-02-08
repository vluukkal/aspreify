--
-- A backend which dereifies a parsed set of facts
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

module DeReify where

import qualified Data.List as L
import qualified Data.Map as M
import Data.Text


import Control.Monad

import Text.ParserCombinators.Parsec -- just to get the ParseError type


import AspParse

import TxtRender

-- This is really anti-idiomatic in haskell, we build a great big
-- record of hashes which we update upon every new fact. 
-- There must be a better, more typed way, now I'm just 
-- reconstructing the types as I go, blech. 

-- Good thing is that this is independent of order we do not 
-- need to start looking for a full 'Body', say, when seeing 
-- one. May pay off if the facts are coming in modified order from ASP tools. 
-- We get automatically getter functions named after the fields. 
data IntermediateR = IntermediateR {
     doground :: Bool, 
     -- The hashes for rules
     hasrulesh      :: (M.Map String [String]),
     rulesh      :: (M.Map String [String]),
     headsh      :: (M.Map String [String]),
     bodysh      :: (M.Map String [String]),
     posh      :: (M.Map String [String]),
     negh      :: (M.Map String [String]),
     predsh      :: (M.Map String [String]),
     varsh      :: (M.Map String [String]),
     alisth     :: (M.Map String [(String,String)]),
     tlisth     :: (M.Map String [(String,String)]),
     typeh      :: (M.Map String String),
     quals      :: (M.Map String String),
     composedh  :: (M.Map String String),
     boph      :: (M.Map String String),
     largh      :: (M.Map String String),
     rargh      :: (M.Map String String),
     mkassigns  :: (M.Map String (M.Map String String)),
     rassigns  ::  (M.Map String String),
     ptrue     :: (M.Map String String),
     pfalse     :: (M.Map String String),
     -- xpand     :: (M.Map (String,String) (M.Map String String)),
     -- xpand     :: (M.Map String [(M.Map String String)]),
     xpand     :: (M.Map String (M.Map String (M.Map String String))),
     -- 
     bexprh      :: (M.Map String [String]), 
     constsh     :: (M.Map String [String]),
     emptyh      :: (M.Map String [String])
} deriving (Show)

emptyIntermediate x = 
  IntermediateR {
       doground = x, 
       rulesh = M.empty, hasrulesh = M.empty, 
       headsh = M.empty, bodysh = M.empty, posh = M.empty, negh = M.empty,
       predsh = M.empty, varsh = M.empty, alisth = M.empty, typeh = M.empty, 
       largh = M.empty, rargh = M.empty, boph = M.empty,tlisth = M.empty, 
       quals = M.empty, composedh = M.empty, mkassigns = M.empty, rassigns = M.empty, 
       ptrue = M.empty, pfalse = M.empty, xpand = M.empty, 
       bexprh = M.empty, constsh = M.empty, emptyh = M.empty}

collectb :: t -> t1 -> Body
collectb rls bdy = Empty 

-- Obtain the nth argument of a::[MyExpr], assuming it is 
-- either a Sym (Var String) or Sym (Const String) or Number (Const String)
-- Old one with !!
getarg' :: [MyExpr] -> Int -> String
getarg' a n = 
  let elem = a!!n in 
  case elem of 
       Sym (Const s) -> s
       Number (Const s) -> s

getarg :: [MyExpr] -> Int -> String
getarg a n = 
  let mylen = L.length a in  
  if n > mylen then 
       ("getarg found no index " ++ show(n))
  else let elem = a!!n in 
       case elem of 
           Sym (Const s) -> s
           Number (Const s) -> s

-- Here we dispatch based on the name of the reified predicate 
-- The types of the hashes could be changed, but would it just make life
-- harder. 
assigntohash :: IntermediateR -> [Char] -> [MyExpr] -> t -> IntermediateR
assigntohash hs nm bdy neg = 
    case nm of 
      "hasrule" -> let src = getarg bdy 0 in 
                   let trgt = getarg bdy 1 in 
                   let tmphs = hasrulesh hs in 
                   let newhs = M.insertWith (++) src [trgt] tmphs in
                       hs { hasrulesh = newhs }
      {--
      "rule" ->  let src = getarg bdy 0 in 
                 let tmphs = typeh hs in 
                 let newhs = M.insert src nm tmphs in
                        hs { typeh = newhs }
       --}
      "rule" ->  addtype bdy nm 0
      "composite" ->  addtype bdy nm 0
      "constraint" -> addtype bdy nm 0
      "assert" -> addtype bdy nm 0
      "head" -> let src = getarg bdy 0 in 
                let trgt = getarg bdy 1 in 
                let tmphs = headsh hs in 
                let newhs = M.insertWith (++) src [trgt] tmphs in
                       hs { headsh = newhs }
      "qual" -> let src = getarg bdy 0 in 
                let trgt = getarg bdy 1 in 
                let tmphs = quals hs in 
                let newhs = M.insertWith (++) src trgt tmphs in
                       hs { quals = newhs }
      "bexpr" -> let src = getarg bdy 0 in 
                 let trgt = getarg bdy 1 in 
                 let hs' = addtype bdy nm 1 in 
                 let tmphs = bexprh hs' in 
                 let tmphs' = bodysh hs in 
                 let newhs = M.insertWith (++) src [trgt] tmphs in
                 let newhs' = M.insertWith (++) src [trgt] tmphs' in
                         hs' { bodysh = newhs', bexprh = newhs }
                         -- hs' { bexprh = newhs }
      "larg" -> let src = getarg bdy 0 in 
                let trgt = getarg bdy 1 in 
                let tmphs = largh hs in 
                let newhs = M.insertWith (++) src trgt tmphs in
                       hs { largh = newhs }
      "rarg" -> let src = getarg bdy 0 in 
                let trgt = getarg bdy 1 in 
                let tmphs = rargh hs in 
                let newhs = M.insertWith (++) src trgt tmphs in
                       hs { rargh = newhs }
      "bop" -> let src = getarg bdy 0 in 
               let trgt = getarg bdy 1 in 
               let tmphs = boph hs in 
               let newhs = M.insert src trgt tmphs in
                       hs { boph = newhs }
      "body" -> let src = getarg bdy 0 in 
                let trgt = getarg bdy 1 in 
                let tmphs = bodysh hs in 
                let newhs = M.insertWith (++) src [trgt] tmphs in
                       hs { bodysh = newhs }
      "pos" ->  let src = getarg bdy 0 in 
                let tmphs = posh hs in 
                let newhs = M.insert src [""] tmphs in -- This could be True instead of [""]
                       hs { posh = newhs }             -- Is it worth the while leaving like this?
      "neg" ->  let src = getarg bdy 0 in 
                let tmphs = negh hs in 
                let newhs = M.insert src [""] tmphs in
                       hs { negh = newhs }
      "ptrue" ->  let src = getarg bdy 0 in 
                let tmphs = ptrue hs in 
                let newhs = M.insert src "" tmphs in
                       hs { ptrue = newhs }
      "pfalse" ->  let src = getarg bdy 0 in 
                let tmphs = pfalse hs in 
                let newhs = M.insert src "" tmphs in
                       hs { pfalse = newhs }
      "pred" -> let src = getarg bdy 0 in 
                let trgt = getarg bdy 1 in 
                let hs' = addtype bdy nm 0 in 
                let tmphs = predsh hs' in 
                let newhs = M.insert src [trgt] tmphs in -- This could be trget instead of [trgt]
                       hs' { predsh = newhs }
      "var" ->  let src = getarg bdy 0 in 
                let trgt = getarg bdy 1 in 
                let hs' = addtype bdy nm 0 in 
                let tmphs = varsh hs' in 
                let newhs = M.insert src [trgt] tmphs in -- This could be trget instead of [trgt]
                       hs' { varsh = newhs }
      "cnst" ->  let src = getarg bdy 0 in 
                 let trgt = getarg bdy 1 in 
                 let hs' = addtype bdy nm 0 in 
                 let tmphs = constsh hs' in 
                 let newhs = M.insert src [trgt] tmphs in 
                        hs' { constsh = newhs }
      "alist" ->  let src = getarg bdy 0 in 
                  let idx = getarg bdy 1 in 
                  let trgt = getarg bdy 2 in 
                  let tmphs = alisth hs in 
                  let newhs = M.insertWith (++) src [(idx,trgt)] tmphs in
                       hs { alisth = newhs }
      "mkassign" ->  let rn = getarg bdy 0 in 
                  let varn = getarg bdy 1 in 
                  let varval = getarg bdy 2 in 
                  let tmphs = mkassigns hs in 
                  let tmpins = M.insert varn varval M.empty in 
                  let newhs = M.insertWith updvr rn tmpins tmphs in 
                       hs { mkassigns = newhs }
                  where 
                      updvr :: Ord k => M.Map k a -> M.Map k a -> M.Map k a
                      updvr newh oldh = M.union oldh newh
{--
      "xpand" ->  let rn = getarg bdy 0 in 
                  let prdid = getarg bdy 1 in 
                  let jstid = getarg bdy 2 in 
                  let tlistid = getarg bdy 3 in 
                  let tmphs = xpand hs in 
                  let tmpins = M.insert prdid jstid M.empty in 
                  let newhs = M.insertWith updvr tlistid tmpins tmphs in 
                       hs { xpand = newhs }
                  where 
                      updvr :: Ord k => M.Map k a -> M.Map k a -> M.Map k a
                      updvr newh oldh = M.union oldh newh
--}
      -- boundexpandvv(78,"edge","Y","2",86,81,23).
      -- later on we get tlistid and we want to get 
      -- all the same justifications.
      -- When travalling tlist later we may get 2, 86, 82 (index 2)
      -- typeh[81] = "composite"
      -- xpand[81] = [[23] = ["X"] = "2" 
      --                  = ["Y"] = "1"]
      -- Well keep a list of hashes, but do we need the middle key [23]?
      "boundexpandvv" ->  let rn = getarg bdy 0 in -- we dont want this
                  let prdnm = getarg bdy 1 in      -- we dont want this 
                  let vname = getarg bdy 2 in 
                  let vval = getarg bdy 3 in 
                  let predref = getarg bdy 4 in 
                  let tlistid = getarg bdy 5 in 
                  let justid = getarg bdy 6 in     -- this is to bind potential other 
                                                   -- values from same justification here. 
                                                   -- later we should be able to obtain all of the 
                                                   -- values of the same justification 
                  let newhs = puttohsh tlistid justid vname vval (xpand hs) in 
                  -- Since we are adding stuff to newhs, we need to mark 
                  -- the rule in rassigns as later on we need to have some 
                  -- content in rasssigns in order to proceed with grounding. 
                  let newrassigns = M.union (rassigns hs) (M.insert prdnm "bogusmarker" M.empty) in 
                       hs { xpand = newhs, rassigns = newrassigns }
                  where 
                    puttohsh k1 k2 k3 v hsh = 
                      let one = M.lookup k1 hsh in 
                      case one of 
                        Just two' -> 
                             let two = M.lookup k2 two' in 
                             case two of 
                               Just three -> 
                                    let newhsh3 = M.insert k3 v three in 
                                    let newhsh2 = M.insert k2 newhsh3 two' in 
                                      M.insert k1 newhsh2 hsh
                               Nothing -> M.insert k1 (M.insert k2 (M.insert k3 v M.empty) two') hsh 
                        Nothing -> M.insert k1 (M.insert k2 (M.insert k3 v M.empty) M.empty) hsh 
                  
{--
      "boundexpandvv" ->  let rn = getarg bdy 0 in -- we dont want this
                  let prdnm = getarg bdy 1 in      -- we dont want this 
                  let vname = getarg bdy 2 in 
                  let vval = getarg bdy 3 in 
                  let predref = getarg bdy 4 in 
                  let tlistid = getarg bdy 5 in 
                  let justid = getarg bdy 6 in     -- this is to bind potential other 
                                                   -- values from same justification here. 
                                                   -- later we should be able to obtain all of the 
                                                   -- values of the same justification 
                  let tmphs = xpand hs in 
                  let tmpins = M.insert vname vval M.empty in 
                  -- let newhs = M.insertWith updvr (tlistid,justid) tmpins tmphs in 
                  let newhs = M.insertWith updvr (tlistid,justid) tmpins tmphs in 
                       hs { xpand = newhs }
                  where 
                      updvr :: Ord k => M.Map k a -> M.Map k a -> M.Map k a
                      updvr newh oldh = M.union oldh newh
--}
      "tlist" ->  let src = getarg bdy 0 in 
                  let idx = getarg bdy 1 in 
                  let trgt = getarg bdy 2 in 
                  let tmphs = tlisth hs in 
                  let newhs = M.insertWith (++) src [(idx,trgt)] tmphs in
                       hs { tlisth = newhs }
      otherwise -> let tmphs = emptyh hs in 
                   let newhs = M.insert nm [""] tmphs in
                       hs { emptyh = newhs }
      where 
            addtype b val idx = 
                 let src = getarg b idx in 
                 let tmphs = typeh hs in 
                 let newhs = M.insert src val tmphs in
                        hs { typeh = newhs }

handlehead :: IntermediateR -> Body -> IntermediateR
handlehead hs hd  = 
   case hd of 
           Plain a args neg -> 
              case a of 
                  Const nm -> assigntohash hs nm args neg
                  Var vn -> hs
           _ -> hs

-- We are only interested in facts as the reified format
-- is that by construction. 
-- i::Rules                     -- an individual rule
-- intermediate::IntermediateR  -- the resulting internal format

collect :: Rules -> IntermediateR -> IntermediateR
collect i intermediate = 
   case i of 
         Fact (l:_) -> let x = handlehead intermediate l in 
              x
         _ -> intermediate

-- This is the actual dereification function. 
-- Above this the functions pertain to collecting stuff 
-- from the individual facts; here we go through them 
-- again and form a 'Rules' syntax tree which can be 
-- rendered back. 
pull i handleall = 
  -- if M.member i (typeh i)
  let rls = hasrulesh i in 
  -- let y = M.foldWithKey (citem i) [] rls in 
  let y = M.foldWithKey (crulebase handleall i) [] rls in 
       -- y <- M.foldWithKey (crule i) (Just []) rls 
       y
       -- (Fact y)

crulebase handleall hash key v accu = 
    L.foldr (citem handleall hash) [] v 

getrulevars h k = 
   let vars = M.lookup k (mkassigns h) in 
   case vars of 
        Just r -> if (doground h) then  (h { rassigns = r }) else h
        Nothing -> h 

{--
 -- Old one which does not produce facts 
 -- for assertions, i.e. rules without variables
citem :: IntermediateR -> String -> [Rules] -> [Rules]
citem hash key accu = 
   let hash' = getrulevars hash key in 
   if (M.null (rassigns hash')) && (doground hash') 
   then accu 
   else 
     -- Ugh, cake on cake here
     -- let hash' = if (doground hash') then hash' else (hash' { rassigns = M.empty }) in 
     let tp = M.lookup key (typeh hash') in 
     case tp of 
        Just "rule" -> crule hash' key accu 
        Just "constraint" -> cconstraint hash' key accu 
        Just "assert" -> cassert hash' key accu 
        -- Just "composite" -> cassert hash key accu 
        Just x -> (Deny [Plain (Const ("Error at citem: unknown item: "++ x )) [] True]):accu 
        Nothing -> -- accu 
                (Deny [Plain (Const ("Error at citem: unknown ID: "++key )) [] True]):accu 
--}

citem :: Bool -> IntermediateR -> String -> [Rules] -> [Rules]
citem handleall hash key accu = 
   let hash' = getrulevars hash key in 
   -- Ugh, cake on cake here
   -- let hash' = if (doground hash') then hash' else (hash' { rassigns = M.empty }) in 
   let tp = M.lookup key (typeh hash') in 
   let cmnt = (RComment ("Source key: " ++ show(key) )) in
   case tp of 
      Just "rule" -> checkground hash' (crule hash' key (cmnt:accu)) accu 
      Just "constraint" -> checkground hash' (cconstraint hash' key (cmnt:accu)) accu 
      Just "assert" -> if handleall then (cassert hash' key (cmnt:accu)) else accu 
      -- Just "composite" -> cassert hash key accu 
      Just x -> (Deny [Plain (Const ("Error at citem: unknown item: "++ x )) [] True]):accu 
      Nothing -> -- accu 
              (Deny [Plain (Const ("Error at citem: unknown ID: "++key )) [] True]):accu 
   where 
      checkground h func accu = 
        if (M.null (rassigns h)) && (doground h) 
        then (RComment ("Not grounding: " ++ show(key) ++ " -- " ++ (show h))):accu 
        -- else (RComment ("Vars: " ++ (rendervars h))):func
        else func ++ [(RComment ("Vars: " ++ (rendervars h)))]
                   
rendervars h = 
  let boundvars = (rassigns h) in 
  M.foldrWithKey sval "" boundvars
  where 
    sval v k accu = accu ++ ("(" ++ v ++ ": " ++ k ++ ")")


crule :: IntermediateR -> String -> [Rules] -> [Rules]
crule hash key accu = 
   let hdkm = M.lookup key (headsh hash) in 
   let bdksm = M.lookup key (bodysh hash) in 
   case (hdkm,bdksm) of 
        (Just hdk, Just bdks) -> 
              let hdc = chead hash (L.head hdk) in 
              let bdls = L.foldr (cbody hash) [] bdks in 
                  ((Rule hdc bdls):accu)
        (_,_) -> ((RComment ("crule no key " ++ show(key))):accu)

crule'' :: IntermediateR -> String -> [Rules] -> [Rules]
crule'' hash key accu = 
   -- Unsafe, will raise exception if no such key, aka
   -- incomplete refied file ...
   let hdk = (headsh hash) M.! key in 
   let hdc = chead hash (L.head hdk) in 
   let bdks = (bodysh hash) M.! key in 
   -- let bdks = (bexprh hash) M.! key in 
   let bdls = L.foldr (cbody hash) [] bdks in 
       ((Rule hdc bdls):accu)
       -- (hdc:accu)


cconstraint hash key accu = 
   let bdksm = M.lookup key (bodysh hash) in 
   case bdksm of 
        Just bdks -> let bdls = L.foldr (cbody hash) [] bdks in 
               ((Deny bdls):accu)
        Nothing -> ((RComment ("cconstraint no key " ++ show(key))):accu)

cconstraint' hash key accu = 
   -- Unsafe, will raise exception if no such key, aka
   -- incomplete refied file ...
   let bdks = (bodysh hash) M.! key in 
   let bdls = L.foldr (cbody hash) [] bdks in 
       ((Deny bdls):accu)

cassert hash key accu = 
   let hdkm = M.lookup key (headsh hash) in 
   case hdkm of 
        Just hdk -> 
           let hdc = chead hash (L.head hdk) in 
               ((Fact [hdc]):accu)
        Nothing -> ((RComment ("cassert no key " ++ show(key))):accu)

cassert' hash key accu = 
   -- Unsafe, will raise exception if no such key, aka
   -- incomplete refied file ...
   let hdk = (headsh hash) M.! key in 
   let hdc = chead hash (L.head hdk) in 
       ((Fact [hdc]):accu)
       -- (hdc:accu)


cbexpr :: IntermediateR -> String -> [Body] -> [Body]
cbexpr hash key accu = 
   let lftm = M.lookup key (largh hash) in 
   let rgtm = M.lookup key (rargh hash) in 
   let bopm = M.lookup key (boph hash) in 
   case (lftm,rgtm,bopm) of 
        (Just lft, Just rgt, Just bop) -> 
              let lft' = cexpr hash lft in 
              let rgt' = cexpr hash rgt in 
                  ((BExpr (tobop (rmquot bop)) lft' rgt'):accu)
        (_,_,_) -> ((Comment ("cbexpr, no key " ++ show(key))):accu)
       -- ((Rule hdc bdls):accu)

-- With no err check 
cbexpr' :: IntermediateR -> String -> [Body] -> [Body]
cbexpr' hash key accu = 
   let lft = (largh hash) M.! key in 
   let rgt = (rargh hash) M.! key in 
   let bop = (boph hash) M.! key in 
   let lft' = cexpr hash lft in 
   let rgt' = cexpr hash rgt in 
       ((BExpr (tobop (rmquot bop)) lft' rgt'):accu)
       -- ((Rule hdc bdls):accu)


-- crule' :: IntermediateR -> String -> t -> [Maybe Body] -> Maybe [Maybe Body]

-- We want to call this from a fold, so we need to have an accu 
-- but we'd like it to be [Body] instead of [Maybe Body], and certainly not
-- Maybe [Maybe Body]. 
crule' hash key v accu = 
      do 
         hdk <- M.lookup key (headsh hash)
         let hdc = chead' hash (L.head hdk)
         -- let hdc' = join hdc
         return []
         -- return(join (hdc:accu))
         -- try sequence from control monad

chead h k = 
      cpred h k 

cbody :: IntermediateR -> String -> [Body] -> [Body]
cbody hash key accu = 
   let unnecessary = M.lookup key (ptrue hash) in 
   case unnecessary of 
      Nothing -> actualbody hash key accu 
      Just a -> 
           let isnegated = M.lookup key (negh hash) in 
           case isnegated of 
             -- Nothing -> (Comment ("Potentially true and redendant " ++ show(key))):accu -- accu 
             Nothing -> (Comment ("Potentially true and redendant " ++ show(key))):((actualbody hash key accu)) -- accu 
             Just a -> actualbody hash key accu 
    where 
      actualbody hash key accu = 
          let tp = M.lookup key (typeh hash) in 
           case tp of 
                Just "bexpr" -> cbexpr hash key accu 
                Just "pred" -> (cpred hash key):accu 
                Just "composite" -> (ctlist hash key) ++ accu -- let nxt = ( hash) M.! key 
                Nothing -> -- accu 
                        (Plain (Const ("Error at cbody: unknown ID: "++key )) [] True):accu        

 -- The original, non grounding one 
-- ctlist :: IntermediateR -> String -> Body
ctlist' :: IntermediateR -> String -> [Body]
ctlist' h k = 
    let args = (tlisth h) M.! k in 
    let args' = L.foldr (targl h) [] args in -- [(idx,id)] to [(idx,Body)]
    let oargs = L.sortBy myc args' in -- order by index 
    let (_,oargs') = L.unzip oargs in -- We need to translate [(idx,Body)] to [Body]
      -- (Typed oargs')
      [(Typed oargs')]
    where 
      myc (i1,v1) (i2,v2) = i1 `compare` i2

{--  
Here we need to generate new instances of the zeroeth 
entry and follow xpands to get the values for the 
variables. 
We need to rewrite this to a set of plain facts with the
variables coming from the boundexpandvv, maybe.  
--}
{-- --}
ctlist'' :: IntermediateR -> String -> [Body]
ctlist'' h k = 
    let args = (tlisth h) M.! k in 
    let oargs = L.sortBy myc args in -- order by index, [(idx,id)]
    -- now get the first entry, which is the template to be filled in 
    -- by the following grounding phase 
    if (L.length oargs) == 0 then []
    else 
      let tmplt = oargs L.!! 0 in
      -- The rest of them contain the templates by which the template
      -- needs to be instantiated.  
      let rest = L.tail oargs in 
        (instantiatectlist h k tmplt rest) ++ [(Comment ("ctlist for " ++ show(k) ++ " with initial " ++ show(tmplt)) )]
    where 
      myc (i1,v1) (i2,v2) = i1 `compare` i2

ctlist :: IntermediateR -> String -> [Body]
ctlist h k = 
    let argsm = M.lookup k (tlisth h) in 
    case argsm of 
       Just args -> 
            let oargs = L.sortBy myc args in -- order by index, [(idx,id)]
            -- now get the first entry, which is the template to be filled in 
            -- by the following grounding phase 
            if (L.length oargs) == 0 then []
            else 
                 let tmplt = oargs L.!! 0 in
                 -- The rest of them contain the templates by which the template
                 -- needs to be instantiated.  
                 let rest = L.tail oargs in 
                     (instantiatectlist h k tmplt rest) ++ [(Comment ("ctlist for " ++ show(k) ++ " with initial " ++ show(tmplt)) )]
       Nothing -> [Comment ("ctlist, no such key " ++ show(k))]
    where 
      myc (i1,v1) (i2,v2) = i1 `compare` i2
{-- --}


-- instantiatectlist :: IntermediateR -> String -> a -> [a] -> Body
-- We use the tmplt and obtain the different variable bindings 
-- from xpand. 
-- tlist(81,2,86).
-- qual(86,87).
-- rulepred(86,87).
--
-- (idx,id) == (2, 86)
-- we are not really interested in idx, but the 
-- values produced by justification for particular variables
instantiatectlist h k (idx,id) l = 
-- We need to get the variables and feed them to 
-- the cbody. k is the tlist ID, which we use to get stuff
-- from xpand, but we need the justid for the key as well
-- and that can only come from l.
-- In the worst case we may need to get the variables from 
-- another 'scope', that is the binding may come from the 
-- regular variables... 
-- We may have to join and overwrite rassigns. 
  L.foldr cmbn [] l 
  where
    cmbn (idx',v) accu = 
       let assgn = joinalevel k (xpand h) in 
       -- For each of these assignments we need to create a cbody 
       -- instantiated with them. We also need to combine them 
       -- with the rassigns in order to do a proper expansion.
       let potqualidx = M.lookup id (quals h) in 
       case potqualidx of 
            Just qualidx -> 
                 let qualpredidx = M.lookup v (quals h) in 
                 case qualpredidx of 
                      Just vv -> -- let xpanded = L.foldr (\lhsh ac -> (cbody (h { rassigns = M.union lhsh (rassigns h)}) vv ac )) [] assgn in 
                           let xpanded = L.foldr (\lhsh ac -> (cbody (h { rassigns = M.union lhsh (rassigns h)}) qualidx ac )) [] assgn in 
                               xpanded++accu 
                      Nothing -> (Comment ("xpand no qualididx:" ++ show(v)) ):accu 
            Nothing -> (Comment ("xpand no template qualididx:" ++ show(idx)) ):accu 
    joinalevel k1 hsh = 
      -- We have a three level hash, we get the first by 
      -- key and then get a list of all leave hashes from the bottom level 
      -- irrespective of their keys. 
      let one = M.lookup k1 hsh in 
      case one of 
        Just two' -> 
            let res = M.foldr f [] two' in  
                res
        Nothing -> []
      where 
          f i accu = 
            let leaves = M.foldrWithKey (\k g ac -> (k,g):ac) [] i in 
                (M.fromList leaves):accu 

   
targl h (idx,v) accu = 
    let tmp = (quals h) in 
    let nxtm = M.lookup v tmp in 
    case nxtm of 
      Just nxt -> let nxtb = cbody h nxt [] in 
           (idx,L.head(nxtb)):accu
      Nothing -> accu 

targl' h (idx,v) accu = 
    let tmp = (quals h) in 
    let nxt = tmp M.! v in 
    let nxtb = cbody h nxt [] in 
        (idx,L.head(nxtb)):accu



cpred'' :: IntermediateR -> String -> Body
cpred'' h k = 
    let pn = (predsh h) M.! k in 
    let args = (alisth h) M.! k in 
    let args' = L.foldr (argl h) [] args in -- We need to translate [(idx,Atom)] to [MyExpr]
    let oargs = L.sortBy myc args' in -- order by index 
    let (_,oargs') = L.unzip oargs in 
    -- let oargs'' = L.map (\i -> (Sym i)) oargs' in     
    -- let oargs'' = L.map (\i -> (cexpr h) i ) oargs' in     
    -- let oargs'' = L.map (cexpr h) oargs' in     
    let ispos = (M.member k (negh h)) in -- && (not (M.member k (posh h) )) in 
      (Plain (Const (rmquot (L.head pn))) oargs' (not ispos))
    where 
      myc (i1,v1) (i2,v2) = i1 `compare` i2

cpred :: IntermediateR -> String -> Body
cpred h k = 
    let pnm = M.lookup k (predsh h) in 
    let argsm = M.lookup k (alisth h) in 
    case (pnm, argsm) of 
         (Just pn, Just args) -> 
             let args' = L.foldr (argl h) [] args in -- We need to translate [(idx,Atom)] to [MyExpr]
             let oargs = L.sortBy myc args' in -- order by index 
             let (_,oargs') = L.unzip oargs in 
             -- let oargs'' = L.map (\i -> (Sym i)) oargs' in     
             -- let oargs'' = L.map (\i -> (cexpr h) i ) oargs' in     
             -- let oargs'' = L.map (cexpr h) oargs' in     
             let ispos = (M.member k (negh h)) in -- && (not (M.member k (posh h) )) in 
             (Plain (Const (rmquot (L.head pn))) oargs' (not ispos))
         (_,_) -> (Comment ("cpred: no key " ++ show(k) ))
    where 
      myc (i1,v1) (i2,v2) = i1 `compare` i2
        
chead' h k = 
      cpred' h k 

cpred' :: IntermediateR -> String -> Maybe Body
cpred' h k = 
      do 
         pn <- M.lookup k (predsh h)
         args <- M.lookup k (alisth h) 
         -- We need to fold over args which is Just [(String,String)]
         let args' = L.foldr (argl h) [] args
         let oargs = L.sortBy myc args' -- order by index 
         let (_,oargs') = L.unzip oargs -- We need to translate [(idx,Atom)] to [MyExpr]
         -- let oargs'' = L.map (\i -> (Sym i)) oargs'
         return ((Plain (Const (rmquot (L.head pn))) oargs' True))
      where 
        myc (i1,v1) (i2,v2) = i1 `compare` i2

{--
cexpr hash key v accu = 
   let tp = M.lookup key (typeh hash) in 
   case tp of 
        Just "var" -> cvar hash key v accu 
        Just "cnst" -> cconst hash key v accu 
        Nothing -> accu 
--}
cexpr :: IntermediateR -> String -> MyExpr
cexpr hash key = 
   let tp = M.lookup key (typeh hash) in 
   case tp of 
        Just "var" -> cvar hash key
        Just "cnst" -> cconst hash key
        Nothing -> (Sym (Const ("cexpr error unknown key: " ++ key)))


-- This is where we may ground a variable,
-- if the rassign hash is nonempty and has
-- the given variable, we return a Cnst 
-- instead of var. 
-- let tst = (emptyIntermediate True) {xpand = fromList [("81",[fromList [("\"X\"","\"2\"")],fromList [("\"Y\"","\"1\"")],fromList [("\"X\"","\"3\"")],fromList [("\"Y\"","\"2\"")],fromList [("\"X\"","\"1\"")],fromList [("\"Y\"","\"3\"")],fromList [("\"X\"","\"3\"")],fromList [("\"Y\"","\"1\"")],fromList [("\"X\"","\"2\"")],fromList [("\"Y\"","\"3\"")],fromList [("\"X\"","\"1\"")],fromList [("\"Y\"","\"2\"")]])]}
-- let tst' = tst { rassigns = xpand}
ground hash vname = 
   let boundvars = (rassigns hash) in 
   let val = M.lookup vname boundvars in 
   case val of 
        Just cnst -> (Sym (Const (rmquot cnst)))
        Nothing -> (Sym (Var (rmquot vname)))


cvar hash key  = 
   let hdk = M.lookup key (varsh hash) in 
   case hdk of 
        Just vname -> ground hash (L.head vname)
        Nothing -> (Sym (Const ("Error no variable ID:" ++ show(key))))

cconst' hash key = 
   -- Unsafe, will raise exception if no such key, aka
   -- incomplete refied file ...
   let hdk = (constsh hash) M.! key in 
       -- (Number (Const (rmquot (L.head hdk))))
       (Sym (Const (rmquot (L.head hdk))))

cconst hash key = 
   -- Unsafe, will raise exception if no such key, aka
   -- incomplete refied file ...
   let hdkm = M.lookup key (constsh hash) in 
      case hdkm of 
           Just hdk -> -- (Number (Const (rmquot (L.head hdk))))
                       (Sym (Const (rmquot (L.head hdk))))
           Nothing -> (Sym (Const ("Error no const ID:" ++ show(key))))


{--
argl h (idx,v) accu = 
    let var = (varsh h) M.! v in 
        (idx,(Var (rmquot (L.head var)))):accu
--}
argl h (idx,v) accu = 
    let tmp = cexpr h v in 
        (idx,tmp):accu



rmquot s = 
  case s of 
       '\"':rst -> if (L.last rst) == '\"' then (L.take ((L.length rst)-1) rst) else s
       otherwise -> s        

-- dereify' (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "2")] True],Fact [Plain (Const "rule") [Number (Const "2")] True],Fact [Plain (Const "pos") [Number (Const "3")] True],Fact [Plain (Const "head") [Number (Const "2"),Number (Const "3")] True],Fact [Plain (Const "neg") [Number (Const "6")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "6")] True],Fact [Plain (Const "pos") [Number (Const "9")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "9")] True]])
-- dereify' (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "2")] True],Fact [Plain (Const "rule") [Number (Const "2")] True],Fact [Plain (Const "pos") [Number (Const "3")] True],Fact [Plain (Const "head") [Number (Const "2"),Number (Const "3")] True],Fact [Plain (Const "pred") [Number (Const "3"),Sym (Const "\"oncycle\"")] True],Fact [Plain (Const "var") [Number (Const "4"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "1"),Number (Const "4")] True],Fact [Plain (Const "var") [Number (Const "5"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "2"),Number (Const "5")] True],Fact [Plain (Const "neg") [Number (Const "6")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "6")] True],Fact [Plain (Const "pred") [Number (Const "6"),Sym (Const "\"other\"")] True],Fact [Plain (Const "var") [Number (Const "7"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "6"),Number (Const "1"),Number (Const "7")] True],Fact [Plain (Const "var") [Number (Const "8"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "6"),Number (Const "2"),Number (Const "8")] True],Fact [Plain (Const "pos") [Number (Const "9")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "9")] True],Fact [Plain (Const "pred") [Number (Const "9"),Sym (Const "\"edge\"")] True],Fact [Plain (Const "var") [Number (Const "10"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "9"),Number (Const "1"),Number (Const "10")] True],Fact [Plain (Const "var") [Number (Const "11"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "9"),Number (Const "2"),Number (Const "11")] True]])
--
-- 
-- reached(1).
-- parse rulebase "" "hasrule(1,40).assert(40).pos(41).head(40,41).pred(41,\"reached\").cnst(42,\"1\").alist(41,1,42)."
-- dereify' (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "40")] True],Fact [Plain (Const "assert") [Number (Const "40")] True],Fact [Plain (Const "pos") [Number (Const "41")] True],Fact [Plain (Const "head") [Number (Const "40"),Number (Const "41")] True],Fact [Plain (Const "pred") [Number (Const "41"),Sym (Const "\"reached\"")] True],Fact [Plain (Const "cnst") [Number (Const "42"),Sym (Const "\"1\"")] True],Fact [Plain (Const "alist") [Number (Const "41"),Number (Const "1"),Number (Const "42")] True]])

-- other(X , Y) :- edge(X , Y) , Y != Z.
-- Right [Rule (Plain (Const "other") [Sym (Var "X"),Sym (Var "Y")] True) [Plain (Const "edge") [Sym (Var "X"),Sym (Var "Y")] True,BExpr Neq (Sym (Var "Y")) (Sym (Var "Z"))]]
-- dereify' (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "2")] True],Fact [Plain (Const "rule") [Number (Const "2")] True],Fact [Plain (Const "pos") [Number (Const "3")] True],Fact [Plain (Const "head") [Number (Const "2"),Number (Const "3")] True],Fact [Plain (Const "pred") [Number (Const "3"),Sym (Const "\"other\"")] True],Fact [Plain (Const "var") [Number (Const "4"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "1"),Number (Const "4")] True],Fact [Plain (Const "var") [Number (Const "5"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "2"),Number (Const "5")] True],Fact [Plain (Const "bexpr") [Number (Const "2"),Number (Const "6")] True],Fact [Plain (Const "bop") [Number (Const "6"),Sym (Const "\"!=\"")] True],Fact [Plain (Const "larg") [Number (Const "6"),Number (Const "7")] True],Fact [Plain (Const "var") [Number (Const "7"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "rarg") [Number (Const "6"),Number (Const "8")] True],Fact [Plain (Const "var") [Number (Const "8"),Sym (Const "\"Z\"")] True],Fact [Plain (Const "pos") [Number (Const "9")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "9")] True],Fact [Plain (Const "pred") [Number (Const "9"),Sym (Const "\"edge\"")] True],Fact [Plain (Const "var") [Number (Const "10"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "9"),Number (Const "1"),Number (Const "10")] True],Fact [Plain (Const "var") [Number (Const "11"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "9"),Number (Const "2"),Number (Const "11")] True]])
-- dereify' (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "2")] True],Fact [Plain (Const "constraint") [Number (Const "2")] True],Fact [Plain (Const "pos") [Number (Const "3")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "3")] True],Fact [Plain (Const "pred") [Number (Const "3"),Sym (Const "\"node\"")] True],Fact [Plain (Const "var") [Number (Const "4"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "1"),Number (Const "4")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "5")] True],Fact [Plain (Const "composite") [Number (Const "5")] True],Fact [Plain (Const "tlist") [Number (Const "5"),Number (Const "1"),Number (Const "6")] True],Fact [Plain (Const "neg") [Number (Const "7")] True],Fact [Plain (Const "qual") [Number (Const "6"),Number (Const "7")] True],Fact [Plain (Const "pred") [Number (Const "7"),Sym (Const "\"oncycle\"")] True],Fact [Plain (Const "var") [Number (Const "8"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "7"),Number (Const "1"),Number (Const "8")] True],Fact [Plain (Const "var") [Number (Const "9"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "7"),Number (Const "2"),Number (Const "9")] True],Fact [Plain (Const "tlist") [Number (Const "5"),Number (Const "2"),Number (Const "10")] True],Fact [Plain (Const "pos") [Number (Const "11")] True],Fact [Plain (Const "qual") [Number (Const "10"),Number (Const "11")] True],Fact [Plain (Const "pred") [Number (Const "11"),Sym (Const "\"edge\"")] True],Fact [Plain (Const "var") [Number (Const "12"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "11"),Number (Const "1"),Number (Const "12")] True],Fact [Plain (Const "var") [Number (Const "13"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "11"),Number (Const "2"),Number (Const "13")] True]])
-- 

-- parse rulebase "" "xpand(78,87,23,81).xpand(78,87,19,81).xpand(78,87,15,81).xpand(78,87,11,81).xpand(78,87,7,81).xpand(78,87,3,81).boundexpandvv(78,\"edge\",\"Y\",\"2\",81,23).boundexpandvv(78,\"edge\",\"X\",\"1\",81,23).boundexpandvv(78,\"edge\",\"Y\",\"3\",81,19).boundexpandvv(78,\"edge\",\"X\",\"2\",81,19).boundexpandvv(78,\"edge\",\"Y\",\"1\",81,15).boundexpandvv(78,\"edge\",\"X\",\"3\",81,15).boundexpandvv(78,\"edge\",\"Y\",\"3\",81,11).boundexpandvv(78,\"edge\",\"X\",\"1\",81,11).boundexpandvv(78,\"edge\",\"Y\",\"2\",81,7).boundexpandvv(78,\"edge\",\"X\",\"3\",81,7).boundexpandvv(78,\"edge\",\"Y\",\"1\",81,3).boundexpandvv(78,\"edge\",\"X\",\"2\",81,3)."

-- dereify' (Right [Fact [Plain (Const "xpand") [Number (Const "78"),Number (Const "87"),Number (Const "23"),Number (Const "81")] True],Fact [Plain (Const "xpand") [Number (Const "78"),Number (Const "87"),Number (Const "19"),Number (Const "81")] True],Fact [Plain (Const "xpand") [Number (Const "78"),Number (Const "87"),Number (Const "15"),Number (Const "81")] True],Fact [Plain (Const "xpand") [Number (Const "78"),Number (Const "87"),Number (Const "11"),Number (Const "81")] True],Fact [Plain (Const "xpand") [Number (Const "78"),Number (Const "87"),Number (Const "7"),Number (Const "81")] True],Fact [Plain (Const "xpand") [Number (Const "78"),Number (Const "87"),Number (Const "3"),Number (Const "81")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"Y\""),Sym (Const "\"2\""),Number (Const "81"),Number (Const "23")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"X\""),Sym (Const "\"1\""),Number (Const "81"),Number (Const "23")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"Y\""),Sym (Const "\"3\""),Number (Const "81"),Number (Const "19")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"X\""),Sym (Const "\"2\""),Number (Const "81"),Number (Const "19")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"Y\""),Sym (Const "\"1\""),Number (Const "81"),Number (Const "15")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"X\""),Sym (Const "\"3\""),Number (Const "81"),Number (Const "15")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"Y\""),Sym (Const "\"3\""),Number (Const "81"),Number (Const "11")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"X\""),Sym (Const "\"1\""),Number (Const "81"),Number (Const "11")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"Y\""),Sym (Const "\"2\""),Number (Const "81"),Number (Const "7")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"X\""),Sym (Const "\"3\""),Number (Const "81"),Number (Const "7")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"Y\""),Sym (Const "\"1\""),Number (Const "81"),Number (Const "3")] True],Fact [Plain (Const "boundexpandvv") [Number (Const "78"),Sym (Const "\"edge\""),Sym (Const "\"X\""),Sym (Const "\"2\""),Number (Const "81"),Number (Const "3")] True]])

-- ([],IntermediateR {doground = True, hasrulesh = fromList [], rulesh = fromList [], headsh = fromList [], bodysh = fromList [], posh = fromList [], negh = fromList [], predsh = fromList [], varsh = fromList [], alisth = fromList [], tlisth = fromList [], typeh = fromList [], quals = fromList [], composedh = fromList [], boph = fromList [], largh = fromList [], rargh = fromList [], mkassigns = fromList [], rassigns = fromList [], ptrue = fromList [], pfalse = fromList [], xpand = fromList [(("81","11"),fromList [("\"X\"","\"1\""),("\"Y\"","\"3\"")]),(("81","15"),fromList [("\"X\"","\"3\""),("\"Y\"","\"1\"")]),(("81","19"),fromList [("\"X\"","\"2\""),("\"Y\"","\"3\"")]),(("81","23"),fromList [("\"X\"","\"1\""),("\"Y\"","\"2\"")]),(("81","3"),fromList [("\"X\"","\"2\""),("\"Y\"","\"1\"")]),(("81","7"),fromList [("\"X\"","\"3\""),("\"Y\"","\"2\"")])], bexprh = fromList [], constsh = fromList [], emptyh = fromList [("xpand",[""])]})

-- (IntermediateR {doground = True, hasrulesh = fromList [("1",["78","22","18","14","10","6","2"])], rulesh = fromList [], headsh = fromList [("10",["11"]),("14",["15"]),("18",["19"]),("2",["3"]),("22",["23"]),("6",["7"])], bodysh = fromList [("78",["81","79"])], posh = fromList [("11",[""]),("15",[""]),("19",[""]),("23",[""]),("3",[""]),("7",[""]),("79",[""]),("87",[""])], negh = fromList [("83",[""])], predsh = fromList [("11",["\"edge\""]),("15",["\"edge\""]),("19",["\"edge\""]),("23",["\"edge\""]),("3",["\"edge\""]),("7",["\"edge\""]),("79",["\"node\""]),("83",["\"oncycle\""]),("87",["\"edge\""])], varsh = fromList [("80",["\"X\""]),("84",["\"Y\""]),("85",["\"X\""]),("88",["\"Y\""]),("89",["\"X\""])], alisth = fromList [("11",[("2","13"),("1","12")]),("15",[("2","17"),("1","16")]),("19",[("2","21"),("1","20")]),("23",[("2","25"),("1","24")]),("3",[("2","5"),("1","4")]),("7",[("2","9"),("1","8")]),("79",[("1","80")]),("83",[("2","85"),("1","84")]),("87",[("2","89"),("1","88")])], tlisth = fromList [("81",[("2","86"),("1","82")])], typeh = fromList [("10","assert"),("11","pred"),("12","cnst"),("13","cnst"),("14","assert"),("15","pred"),("16","cnst"),("17","cnst"),("18","assert"),("19","pred"),("2","assert"),("20","cnst"),("21","cnst"),("22","assert"),("23","pred"),("24","cnst"),("25","cnst"),("3","pred"),("4","cnst"),("5","cnst"),("6","assert"),("7","pred"),("78","constraint"),("79","pred"),("8","cnst"),("80","var"),("81","composite"),("83","pred"),("84","var"),("85","var"),("87","pred"),("88","var"),("89","var"),("9","cnst")], quals = fromList [("82","83"),("86","87")], composedh = fromList [], boph = fromList [], largh = fromList [], rargh = fromList [], mkassigns = fromList [], rassigns = fromList [], ptrue = fromList [], pfalse = fromList [], xpand = fromList [], bexprh = fromList [], constsh = fromList [("12",["\"3\""]),("13",["\"1\""]),("16",["\"1\""]),("17",["\"3\""]),("20",["\"3\""]),("21",["\"2\""]),("24",["\"2\""]),("25",["\"1\""]),("4",["\"1\""]),("5",["\"2\""]),("8",["\"2\""]),("9",["\"3\""])], emptyh = fromList [("rulecomposite",[""]),("rulepred",[""]),("rulevar",[""])]},[])

dereify' :: Either ParseError [Rules] -> Bool -> ([Rules], IntermediateR)
dereify' rb ground = 
   let hs = emptyIntermediate ground
    in 
   case rb of 
        Left l -> ([],hs) -- [Empty] -- [Left l]
        --  Right r -> L.foldr (factitem r) [] (L.reverse r)
        Right r -> let x = L.foldr collect hs (L.reverse r) in 
                   let y = pull x True in 
                       -- x
                       -- [y]
                       (y,x)


dereify'' :: Either ParseError [Rules] -> IntermediateR
dereify'' rb = 
   let hs = emptyIntermediate True
    in 
   case rb of 
        Left l -> hs
        --  Right r -> L.foldr (factitem r) [] (L.reverse r)
        Right r -> let x = L.foldr collect hs (L.reverse r) in x


-- dereify (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "2")] True],Fact [Plain (Const "rule") [Number (Const "2")] True],Fact [Plain (Const "pos") [Number (Const "3")] True],Fact [Plain (Const "head") [Number (Const "2"),Number (Const "3")] True],Fact [Plain (Const "neg") [Number (Const "6")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "6")] True],Fact [Plain (Const "pos") [Number (Const "9")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "9")] True]])
-- dereify (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "2")] True],Fact [Plain (Const "rule") [Number (Const "2")] True],Fact [Plain (Const "pos") [Number (Const "3")] True],Fact [Plain (Const "head") [Number (Const "2"),Number (Const "3")] True],Fact [Plain (Const "pred") [Number (Const "3"),Sym (Const "\"oncycle\"")] True],Fact [Plain (Const "var") [Number (Const "4"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "1"),Number (Const "4")] True],Fact [Plain (Const "var") [Number (Const "5"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "2"),Number (Const "5")] True],Fact [Plain (Const "neg") [Number (Const "6")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "6")] True],Fact [Plain (Const "pred") [Number (Const "6"),Sym (Const "\"other\"")] True],Fact [Plain (Const "var") [Number (Const "7"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "6"),Number (Const "1"),Number (Const "7")] True],Fact [Plain (Const "var") [Number (Const "8"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "6"),Number (Const "2"),Number (Const "8")] True],Fact [Plain (Const "pos") [Number (Const "9")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "9")] True],Fact [Plain (Const "pred") [Number (Const "9"),Sym (Const "\"edge\"")] True],Fact [Plain (Const "var") [Number (Const "10"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "9"),Number (Const "1"),Number (Const "10")] True],Fact [Plain (Const "var") [Number (Const "11"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "9"),Number (Const "2"),Number (Const "11")] True]])
dereify :: Bool -> Either ParseError [Rules] -> String 
dereify ground x = 
    let (y,hs) = dereify' x ground in 
    txtrender ((Right (L.reverse y))::(Either ParseError [Rules]))

--
-- This returns the internal representation of parsed
-- facts representing the reified program along with the 
-- internal auxiliary hashtable. These are needed whenever
-- we want to avoid recomputing this. 
--
basedreify ground x = 
    let (y,hs) = dereify' x ground in 
      (y,hs)                

--
-- Do a ground dereification using previously constructed
-- Rulebase and intermediate hashes. 
--
-- dereifywithbase :: Either ParseError [Rules] -> [Rules] -> IntermediateR -> ([Rules], IntermediateR) 
dereifywithbase prevrb prevhs rb  = 
   -- let hs = emptyIntermediate ground
   -- in 
   case rb of 
        Left l -> -- ([],prevhs) -- [Empty] -- [Left l]
             []             
        --  Right r -> L.foldr (factitem r) [] (L.reverse r)
        Right r -> let x = L.foldr collect prevhs (L.reverse r) in 
                   let y = pull x False in 
                   -- let newy = prevrb ++ y in 
                   let newy = y in 
                       -- (newy,x)
                       txtrender ((Right (L.reverse newy))::(Either ParseError [Rules]))

--
-- This is for debugging on the interpreter, we return 
-- the internal representation rather than the 
-- textual format. 
-- dereifywithbase':: t -> IntermediateR -> Either t1 [Rules] -> (IntermediateR, [Rules])
dereifywithbase' prevrb prevhs rb  = 
   -- let hs = emptyIntermediate ground
   -- in 
   case rb of 
        Left l -> -- ([],prevhs) -- [Empty] -- [Left l]
             ((emptyIntermediate True),[],(emptyIntermediate True))
        --  Right r -> L.foldr (factitem r) [] (L.reverse r)
        Right r -> let x = L.foldr collect prevhs (L.reverse r) in 
                   let y = pull x False in 
                       (prevhs,y,x)

-- May need to get fromList by  
-- import Data.Map 
-- ctlist  (IntermediateR {doground = True, hasrulesh = fromList [("1",["78","22","18","14","10","6","2"])], rulesh = fromList [], headsh = fromList [("10",["11"]),("14",["15"]),("18",["19"]),("2",["3"]),("22",["23"]),("6",["7"])], bodysh = fromList [("78",["81","79"])], posh = fromList [("11",[""]),("15",[""]),("19",[""]),("23",[""]),("3",[""]),("7",[""]),("79",[""]),("87",[""])], negh = fromList [("83",[""])], predsh = fromList [("11",["\"edge\""]),("15",["\"edge\""]),("19",["\"edge\""]),("23",["\"edge\""]),("3",["\"edge\""]),("7",["\"edge\""]),("79",["\"node\""]),("83",["\"oncycle\""]),("87",["\"edge\""])], varsh = fromList [("80",["\"X\""]),("84",["\"Y\""]),("85",["\"X\""]),("88",["\"Y\""]),("89",["\"X\""])], alisth = fromList [("11",[("2","13"),("1","12")]),("15",[("2","17"),("1","16")]),("19",[("2","21"),("1","20")]),("23",[("2","25"),("1","24")]),("3",[("2","5"),("1","4")]),("7",[("2","9"),("1","8")]),("79",[("1","80")]),("83",[("2","85"),("1","84")]),("87",[("2","89"),("1","88")])], tlisth = fromList [("81",[("2","86"),("1","82")])], typeh = fromList [("10","assert"),("11","pred"),("12","cnst"),("13","cnst"),("14","assert"),("15","pred"),("16","cnst"),("17","cnst"),("18","assert"),("19","pred"),("2","assert"),("20","cnst"),("21","cnst"),("22","assert"),("23","pred"),("24","cnst"),("25","cnst"),("3","pred"),("4","cnst"),("5","cnst"),("6","assert"),("7","pred"),("78","constraint"),("79","pred"),("8","cnst"),("80","var"),("81","composite"),("83","pred"),("84","var"),("85","var"),("87","pred"),("88","var"),("89","var"),("9","cnst")], quals = fromList [("82","83"),("86","87")], composedh = fromList [], boph = fromList [], largh = fromList [], rargh = fromList [], mkassigns = fromList [], rassigns = fromList [], ptrue = fromList [], pfalse = fromList [], xpand = fromList [], bexprh = fromList [], constsh = fromList [("12",["\"3\""]),("13",["\"1\""]),("16",["\"1\""]),("17",["\"3\""]),("20",["\"3\""]),("21",["\"2\""]),("24",["\"2\""]),("25",["\"1\""]),("4",["\"1\""]),("5",["\"2\""]),("8",["\"2\""]),("9",["\"3\""])], emptyh = fromList [("rulecomposite",[""]),("rulepred",[""]),("rulevar",[""])]}) "81"

-- This may be the good one 
-- ctlist  (IntermediateR {doground = True, hasrulesh = fromList [("1",["78","22","18","14","10","6","2"])], rulesh = fromList [], headsh = fromList [("10",["11"]),("14",["15"]),("18",["19"]),("2",["3"]),("22",["23"]),("6",["7"])], bodysh = fromList [("78",["81","79"])], posh = fromList [("11",[""]),("15",[""]),("19",[""]),("23",[""]),("3",[""]),("7",[""]),("79",[""]),("87",[""])], negh = fromList [("83",[""])], predsh = fromList [("11",["\"edge\""]),("15",["\"edge\""]),("19",["\"edge\""]),("23",["\"edge\""]),("3",["\"edge\""]),("7",["\"edge\""]),("79",["\"node\""]),("83",["\"oncycle\""]),("87",["\"edge\""])], varsh = fromList [("80",["\"X\""]),("84",["\"Y\""]),("85",["\"X\""]),("88",["\"Y\""]),("89",["\"X\""])], alisth = fromList [("11",[("2","13"),("1","12")]),("15",[("2","17"),("1","16")]),("19",[("2","21"),("1","20")]),("23",[("2","25"),("1","24")]),("3",[("2","5"),("1","4")]),("7",[("2","9"),("1","8")]),("79",[("1","80")]),("83",[("2","85"),("1","84")]),("87",[("2","89"),("1","88")])], tlisth = fromList [("81",[("2","86"),("1","82")])], typeh = fromList [("10","assert"),("11","pred"),("12","cnst"),("13","cnst"),("14","assert"),("15","pred"),("16","cnst"),("17","cnst"),("18","assert"),("19","pred"),("2","assert"),("20","cnst"),("21","cnst"),("22","assert"),("23","pred"),("24","cnst"),("25","cnst"),("3","pred"),("4","cnst"),("5","cnst"),("6","assert"),("7","pred"),("78","constraint"),("79","pred"),("8","cnst"),("80","var"),("81","composite"),("83","pred"),("84","var"),("85","var"),("87","pred"),("88","var"),("89","var"),("9","cnst")], quals = fromList [("82","83"),("86","87")], composedh = fromList [], boph = fromList [], largh = fromList [], rargh = fromList [], mkassigns = fromList [], rassigns = fromList [], ptrue = fromList [], pfalse = fromList [], xpand = fromList [("81",fromList [("11",fromList [("\"X\"","\"1\""),("\"Y\"","\"3\"")]),("15",fromList [("\"X\"","\"3\""),("\"Y\"","\"1\"")]),("19",fromList [("\"X\"","\"2\""),("\"Y\"","\"3\"")]),("23",fromList [("\"X\"","\"1\""),("\"Y\"","\"2\"")]),("3",fromList [("\"X\"","\"2\""),("\"Y\"","\"1\"")]),("7",fromList [("\"X\"","\"3\""),("\"Y\"","\"2\"")])])],bexprh = fromList [], constsh = fromList [("12",["\"3\""]),("13",["\"1\""]),("16",["\"1\""]),("17",["\"3\""]),("20",["\"3\""]),("21",["\"2\""]),("24",["\"2\""]),("25",["\"1\""]),("4",["\"1\""]),("5",["\"2\""]),("8",["\"2\""]),("9",["\"3\""])], emptyh = fromList [("rulecomposite",[""]),("rulepred",[""]),("rulevar",[""])]}) "81"


