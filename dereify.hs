--
-- A backend which dereifies a parsed set of facts
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
     -- 
     denialsh    :: (M.Map String [String]),
     factsh      :: (M.Map String [String]),
     showsh      :: (M.Map String [String]),
     gshowsh     :: (M.Map String [String]),
     hidesh     :: (M.Map String [String]),
     ghidesh    :: (M.Map String [String]),
     externalsh  :: (M.Map String [String]),
     functionsh :: (M.Map String [String]),
     minimizesh  :: (M.Map String [String]),
     maximizesh  :: (M.Map String [String]),
     constsh     :: (M.Map String [String]),
     computesh   :: (M.Map String [String]), 
     -- The hashes for Body
     plainh      :: (M.Map String [String]), 
     cardh      :: (M.Map String [String]), 
     counth      :: (M.Map String [String]), 
     optimizeh      :: (M.Map String [String]), 
     typedh      :: (M.Map String [String]), 
     weighedh      :: (M.Map String [String]), 
     bexprh      :: (M.Map String [String]), 
     assignh      :: (M.Map String [String]), 
     assignmenth      :: (M.Map String [String]), 
     arityh      :: (M.Map String [String]), 
     emptyh      :: (M.Map String [String]), 
     -- MyExpr stuff 
     numberh :: (M.Map String [String]), 
     symh :: (M.Map String [String]), 
     alternativeh :: (M.Map String [String]), 
     arithh :: (M.Map String [String]), 
     funch :: (M.Map String [String]), 
     -- Operations are not recorded
     atomh :: (M.Map String [String]), 
     consth :: (M.Map String [String])
} deriving (Show)

collectb :: t -> t1 -> Body
collectb rls bdy = Empty 

-- Obtain the nth argument of a::[MyExpr], assuming it is 
-- either a Sym (Var String) or Sym (Const String) or Number (Const String)
getarg :: [MyExpr] -> Int -> String
getarg a n = 
  let elem = a!!n in 
  case elem of 
       Sym (Const s) -> s
       Number (Const s) -> s

-- Here we dispathc based on the name of the reified predicate 
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

-- Above this the functions pertain to collecting stuff 
-- from the individual facts; here we go through them 
-- again and form a 'Rules' syntax tree which can be 
-- rendered back. 
pull i = 
  -- if M.member i (typeh i)
  let rls = hasrulesh i in 
  -- let y = M.foldWithKey (citem i) [] rls in 
  let y = M.foldWithKey (crulebase i) [] rls in 
       -- y <- M.foldWithKey (crule i) (Just []) rls 
       y
       -- (Fact y)

crulebase hash key v accu = 
    L.foldr (citem hash) [] v 

getrulevars h k = 
   let vars = M.lookup k (mkassigns h) in 
   case vars of 
        Just r -> h { rassigns = r } 
        Nothing -> h 

citem :: IntermediateR -> String -> [Rules] -> [Rules]
citem hash key accu = 
   let hash' = getrulevars hash key in 
   let tp = M.lookup key (typeh hash') in 
   case tp of 
        Just "rule" -> crule hash' key accu 
        Just "constraint" -> cconstraint hash' key accu 
        Just "assert" -> cassert hash' key accu 
        -- Just "composite" -> cassert hash key accu 
        Just x -> (Deny [Plain (Const ("Error at citem: unknown item: "++ x )) [] True]):accu 
        Nothing -> -- accu 
                (Deny [Plain (Const ("Error at citem: unknown ID: "++key )) [] True]):accu 

crule :: IntermediateR -> String -> [Rules] -> [Rules]
crule hash key accu = 
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
   -- Unsafe, will raise exception if no such key, aka
   -- incomplete refied file ...
   let bdks = (bodysh hash) M.! key in 
   let bdls = L.foldr (cbody hash) [] bdks in 
       ((Deny bdls):accu)

cassert hash key accu = 
   -- Unsafe, will raise exception if no such key, aka
   -- incomplete refied file ...
   let hdk = (headsh hash) M.! key in 
   let hdc = chead hash (L.head hdk) in 
       ((Fact [hdc]):accu)
       -- (hdc:accu)

cbexpr :: IntermediateR -> String -> [Body] -> [Body]
cbexpr hash key accu = 
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

{--
cbody h k accu = 
      (cpred h k):accu
--}
cbody :: IntermediateR -> String -> [Body] -> [Body]
cbody hash key accu = 
   let tp = M.lookup key (typeh hash) in 
   case tp of 
        Just "bexpr" -> cbexpr hash key accu 
        Just "pred" -> (cpred hash key):accu 
        Just "composite" -> (ctlist hash key):accu -- let nxt = ( hash) M.! key 
        Nothing -> -- accu 
                (Plain (Const ("Error at cbody: unknown ID: "++key )) [] True):accu 

ctlist :: IntermediateR -> String -> Body
ctlist h k = 
    let args = (tlisth h) M.! k in 
    let args' = L.foldr (targl h) [] args in -- [(idx,id)] to [(idx,Body)]
    let oargs = L.sortBy myc args' in -- order by index 
    let (_,oargs') = L.unzip oargs in -- We need to translate [(idx,Body)] to [Body]
      (Typed oargs')
    where 
      myc (i1,v1) (i2,v2) = i1 `compare` i2

targl h (idx,v) accu = 
    let tmp = (quals h) in 
    let nxt = tmp M.! v in 
    let nxtb = cbody h nxt [] in 
        (idx,L.head(nxtb)):accu

targl' h (idx,v) accu = 
    let tmp = (quals h) in 
    let nxt = tmp M.! v in 
    let nxtb = Plain (Const nxt) [] True in 
        (idx,nxtb):accu


cpred :: IntermediateR -> String -> Body
cpred h k = 
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
{--
   let hdk = (varsh hash) M.! key in 
       -- ((Sym (Var (L.head hdk))):accu)
       (Sym (Var (rmquot (L.head hdk))))
--}

cconst hash key = 
   -- Unsafe, will raise exception if no such key, aka
   -- incomplete refied file ...
   let hdk = (constsh hash) M.! key in 
       -- (Number (Const (rmquot (L.head hdk))))
       (Sym (Const (rmquot (L.head hdk))))

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

dereify' :: Either ParseError [Rules] -> ([Rules], IntermediateR)
dereify' rb = 
   let hs = IntermediateR {
       rulesh = M.empty, hasrulesh = M.empty, 
       headsh = M.empty, bodysh = M.empty, posh = M.empty, negh = M.empty,
       predsh = M.empty, varsh = M.empty, alisth = M.empty, typeh = M.empty, 
       largh = M.empty, rargh = M.empty, boph = M.empty, tlisth = M.empty, 
       quals = M.empty, composedh = M.empty, mkassigns = M.empty, rassigns = M.empty,
       -- 
       denialsh = M.empty, factsh = M.empty, showsh = M.empty, gshowsh = M.empty,
       hidesh = M.empty, ghidesh = M.empty, externalsh = M.empty, functionsh = M.empty, 
       minimizesh = M.empty, maximizesh = M.empty, constsh = M.empty, computesh = M.empty, 
       plainh = M.empty, cardh = M.empty, counth = M.empty, optimizeh = M.empty, typedh = M.empty, 
       weighedh = M.empty, bexprh = M.empty, assignh = M.empty, assignmenth = M.empty, 
       arityh = M.empty, emptyh = M.empty, numberh = M.empty, symh = M.empty, 
       alternativeh = M.empty, arithh = M.empty, funch = M.empty, atomh = M.empty, consth = M.empty
    } in 
   case rb of 
        Left l -> ([],hs) -- [Empty] -- [Left l]
        --  Right r -> L.foldr (factitem r) [] (L.reverse r)
        Right r -> let x = L.foldr collect hs (L.reverse r) in 
                   let y = pull x in 
                       -- x
                       -- [y]
                       (y,x)


dereify'' :: Either ParseError [Rules] -> IntermediateR
dereify'' rb = 
   let hs = IntermediateR {
       rulesh = M.empty, hasrulesh = M.empty, 
       headsh = M.empty, bodysh = M.empty, posh = M.empty, negh = M.empty,
       predsh = M.empty, varsh = M.empty, alisth = M.empty, typeh = M.empty, 
       largh = M.empty, rargh = M.empty, boph = M.empty,tlisth = M.empty, 
       quals = M.empty, composedh = M.empty, mkassigns = M.empty, rassigns = M.empty,
       -- 
       denialsh = M.empty, factsh = M.empty, showsh = M.empty, gshowsh = M.empty,
       hidesh = M.empty, ghidesh = M.empty, externalsh = M.empty, functionsh = M.empty, 
       minimizesh = M.empty, maximizesh = M.empty, constsh = M.empty, computesh = M.empty, 
       plainh = M.empty, cardh = M.empty, counth = M.empty, optimizeh = M.empty, typedh = M.empty, 
       weighedh = M.empty, bexprh = M.empty, assignh = M.empty, assignmenth = M.empty, 
       arityh = M.empty, emptyh = M.empty, numberh = M.empty, symh = M.empty, 
       alternativeh = M.empty, arithh = M.empty, funch = M.empty, atomh = M.empty, consth = M.empty
    } in 
   case rb of 
        Left l -> hs
        --  Right r -> L.foldr (factitem r) [] (L.reverse r)
        Right r -> let x = L.foldr collect hs (L.reverse r) in x


-- dereify (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "2")] True],Fact [Plain (Const "rule") [Number (Const "2")] True],Fact [Plain (Const "pos") [Number (Const "3")] True],Fact [Plain (Const "head") [Number (Const "2"),Number (Const "3")] True],Fact [Plain (Const "neg") [Number (Const "6")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "6")] True],Fact [Plain (Const "pos") [Number (Const "9")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "9")] True]])
-- dereify (Right [Fact [Plain (Const "hasrule") [Number (Const "1"),Number (Const "2")] True],Fact [Plain (Const "rule") [Number (Const "2")] True],Fact [Plain (Const "pos") [Number (Const "3")] True],Fact [Plain (Const "head") [Number (Const "2"),Number (Const "3")] True],Fact [Plain (Const "pred") [Number (Const "3"),Sym (Const "\"oncycle\"")] True],Fact [Plain (Const "var") [Number (Const "4"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "1"),Number (Const "4")] True],Fact [Plain (Const "var") [Number (Const "5"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "3"),Number (Const "2"),Number (Const "5")] True],Fact [Plain (Const "neg") [Number (Const "6")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "6")] True],Fact [Plain (Const "pred") [Number (Const "6"),Sym (Const "\"other\"")] True],Fact [Plain (Const "var") [Number (Const "7"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "6"),Number (Const "1"),Number (Const "7")] True],Fact [Plain (Const "var") [Number (Const "8"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "6"),Number (Const "2"),Number (Const "8")] True],Fact [Plain (Const "pos") [Number (Const "9")] True],Fact [Plain (Const "body") [Number (Const "2"),Number (Const "9")] True],Fact [Plain (Const "pred") [Number (Const "9"),Sym (Const "\"edge\"")] True],Fact [Plain (Const "var") [Number (Const "10"),Sym (Const "\"X\"")] True],Fact [Plain (Const "alist") [Number (Const "9"),Number (Const "1"),Number (Const "10")] True],Fact [Plain (Const "var") [Number (Const "11"),Sym (Const "\"Y\"")] True],Fact [Plain (Const "alist") [Number (Const "9"),Number (Const "2"),Number (Const "11")] True]])
dereify :: Either ParseError [Rules] -> String 
dereify x = 
    let (y,hs) = dereify' x in 
    txtrender ((Right (L.reverse y))::(Either ParseError [Rules]))

