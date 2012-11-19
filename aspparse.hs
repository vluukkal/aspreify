--
-- Parsec parser for lparse
--
-- On the interpreter, see the comments in the code 
-- below for more tests and commands to execute on the interpreter. 
--
-- > ghci
-- Prelude> :load aspparse.hs
-- e.g.
-- Prelude> parse atom "" "\"wp1:Person\""
-- Right (Const "\"wp1:Person\"")
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

module AspParse where

import System.IO
import System.IO.Unsafe
import System.Random
import qualified Data.List as List
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr

import Data.IORef 

-- Here are the types for the variable map. We map from ruleid to 
-- another map which maps from variable name to id. 
type VarHash = Map.Map Int (Map.Map String Int)

newrule :: Int -> VarHash -> VarHash
newrule ruleid vars = Map.insert ruleid Map.empty vars

addvar :: String -> Int -> Int -> VarHash -> VarHash 
addvar vname ruleid id vars = 
       case Map.lookup ruleid vars of
       Just localvars -> 
            -- Here we just overwrite stuff in localvars
            Map.insert ruleid (Map.insert vname id localvars) vars
       Nothing -> Map.insert ruleid (Map.insert vname id Map.empty) vars

getvarid :: String -> Int -> VarHash -> Maybe Int
getvarid vname ruleid vars =
         do 
            localvars <- Map.lookup ruleid vars
            Map.lookup vname localvars

showvars :: VarHash -> String 
showvars vrs = 
          let all = Map.foldrWithKey f [] vrs in 
               -- Use this for pretty prenting
               -- List.concat $ List.intersperse "\n" all
               List.concat all 
           where
                f k lcvrs res = 
                  let l = Map.foldrWithKey g [] lcvrs in 
                      let tmp = (show k) ++ ": " ++ (List.concat $ List.intersperse "," l) in 
                          tmp:res
                   where 
                         g vname id accu = ("(" ++ vname ++ ":" ++ (show id) ++ ")" ) : accu



data Atom = Var String
          | Const String 
            deriving(Show,Eq)

data MyOp = Plus
          | Minus
          | Mult
          | Div 
          | Mod
          | Range
            deriving(Show,Eq)

data BOp = Gt
          | Lt 
          | GtEq
          | LtEq
          | Eq 
          | Neq
          | Eqeq
            deriving(Show,Eq)

data MyExpr = Number Atom
            | Sym Atom
            | Alternative [MyExpr]
            | Arith MyOp MyExpr MyExpr 
            deriving(Show,Eq)


-- To test this:
-- parse nvariable "" "Foo"
-- parse nvariable "" "F"
-- parse nvariable "" "X > Y"
nvariable :: GenParser Char st Atom
nvariable   = do{ c  <- upper
                ; cs <- option "" (many (noneOf "\n\r\t (){[]},.+-*/=:;<>"))
                ; skipMany space
                ; return (Var (c:cs))
                }

anyvar :: GenParser Char st Atom
anyvar      = do {
              string "_";
              return(Var "_")}

variable :: GenParser Char st Atom
variable   = anyvar <|>
             nvariable 



-- parse atomsimple "" "m" -- expects lowercase 
-- parse atomsimple "" "blah"
-- atomsimple :: GenParser Char st String
atomsimple :: GenParser Char st Atom
atomsimple   = do{ c  <- lower
                -- ; cs <- option "" (many (noneOf "\n\r\t (){,."))
                ; cs <- option "" (many (noneOf "\n\r\t (){[]},.+-*/=:;<>"))
                -- ; cs <- many letter
                ; skipMany space
                ; return (Const (c:cs))
                }

-- parse atomquoted "" "\"Foo\""
-- parse atomquoted "" "\"wp1:Person\""
-- parse atomquoted "" "p"
-- atomquoted :: GenParser Char st String
atomquoted :: GenParser Char st Atom
atomquoted   = do {
                 c1 <- char '"';
                 content <- (many (noneOf "\"")); --quotedC
                 c2 <- char '"';
                 return (Const((c1:content)++[c2]))
               }

--quotedC :: GenParser Char st String
--quotedC    = noneOf "\""



-- parse atom "" "Foo" -- should fail as it is a variable
-- parse atom "" "foo"
-- parse atom "" "\"Foo\""
-- parse atom "" "\"wp1:Person\""
-- parse atom "" "1" -- fails, should it?

-- parse atom "" "m"
atom :: GenParser Char st Atom 
atom  = 
    atomquoted <|>
    atomsimple
    <?> "a fact starting with lowercase or quoted string"
{--
atom  = 
    try(atomsimple) <|>
    try(atomquoted) 
    <?> "a fact starting with lowercase or quoted string"
--}

-- parse myelem "" "Foo"
-- parse myelem "" "foo"
-- parse myelem "" "_"
-- parse myelem "" "foo,Bar,goo" -- only gives the first foo
-- parse myelem "" "\"foo\""
myelem :: GenParser Char st MyExpr
myelem = 
       try(numericexpr) <?>
       "A numeric expression inside a fact"

-- myelem = do { res <- choice [numericexpr,atom, variable]; return res}


-- parse args "" "(Foo, Bar, Goo)"
-- parse args "" "(Foo,Bar, Goo)"
-- parse args "" "(Foo,Bar,Goo)"
-- parse args "" "(Foo)"
-- parse args "" "(foo)"
-- parse args "" "(foo,Bar,goo)"
-- parse args "" "( Foo)"
-- parse args "" "" -- should fail
-- parse args "" " ( Foo,Bar )" 
-- parse args "" "(1 .. k)"
-- parse args "" "(foo,Bar,5)"
-- parse args "" "(foo,\"Bar\",5)"
-- parse args "" "(X;X+1,Y)"
-- parse args "" "((N-1)*R+1,N)"
args :: GenParser Char st [MyExpr]
-- args    = do { cs <- between '(' ')' many (noneOf "\n\r\t ()")
--               ; return cs}
-- args    = do { words <- sepBy variable commasep; return words}
-- args    = do { words <- between (char '(') (char ')')
args    = do { skipMany space; 
               -- Here we need to be precise on the opening parenthesis 
               -- but the closing one should allow spaces, otherwise
               -- a typed choice (!) fails. 
               words <- between (char '(')
                                (skipMany1 ( space <|> char ')' <|> space))  -- (char ')') 
                   (sepBy myelem (skipMany1 (space <|> char ',')))
                        ; return words}


data Body = Plain Atom [MyExpr] Bool
          | Card MyExpr MyExpr [Body] Bool
          | Count MyExpr MyExpr [Body] Bool
          | Optimize Bool [Body] Bool -- min|max, 
          | Typed [Body]
          -- | Alternative [Body] 
          | Weighed MyExpr Body Bool
          | BExpr BOp MyExpr MyExpr 
          | Assign Atom MyExpr
          | Assignment Atom Body Bool -- urgh, we have to separate between 
          | Arity Atom String
          | Empty 
            deriving (Show,Eq)

data Rules = Rule Body [Body]
           | Deny [Body]
           | Fact [Body]
           | Show [Body]
           | GShow [Body]       -- Gringo syntax
           | Hide [Body]        
           | GHide [Body]       -- Gringo syntax
           | External [Body]    
           | Function [Body]    
           | Minimize [Body]
           | Maximize [Body]
           | Consts [Body]
           | Computes Atom [Body]
            deriving (Show,Eq)

-- parse arel "" "arc(X, Y, L) = L"
-- parse arel "" "border((N-1)*R+1,N)."
arel :: GenParser Char st Body
arel    = try(arel'') <|> 
          arel' 


-- an aggregate to contain negrel, wrel and srel from below
arel' :: GenParser Char st Body
arel'    = 
          try(wrel) <|>
          try(srel) <|>          
          try(negrel) <|>
          try(bexpr) <|>
          try(atomrel)

-- parse arel'' "" "not M = [ est(I,S) : est(I,S) : hasest(I) = S ]" -- NOK
-- parse arel'' "" "not arc(X, Y, L) = L"
arel'' :: GenParser Char st Body
arel'' = do {
       string "not";
       skipMany1 space;
       cntent <- arel;
       return (negateabody cntent)
}

negateabody x = 
 case x of 
      Plain n a nonneg -> Plain n a False
      Card min max b nonneg -> Card min max b False
      Count min max b nonneg -> Count min max b False
      Optimize opt b nonneg -> Optimize opt b False
      Assignment a b nonneg -> Assignment a b False
      Weighed a b nonneg -> Weighed a b False
      _ -> x

{--
varrel :: GenParser Char st Body
varrel    = do {n <- variable
            ;return (Plain n [] True)}

-- varexpr :: GenParser Char st MyExpr
-- varexpr    = (Sym variable)
            

-- Like above but include single variables here
-- This is to use with altrel only
arel' :: GenParser Char st Body
arel'    = 
          try(wrel) <|>
          try(srel) <|>          
          try(negrel) <|>
          try(bexpr) <|> -- note that this has to be before the ones below!
          try(atomrel)  <|>
          try(varrel)  
          -- try(myelem)
--}

-- negative relation
-- parse negrel "" "not blub(Foo,Bar,Goo)"
negrel :: GenParser Char st Body
negrel    = do {
            string "not"; 
            skipMany1 (space)
            ;n <- atom; many space;
            ;myargs <- args
            ;return (Plain n myargs False)}

-- weighed relation
-- parse wrel "" "arc(X, Y, L) = L"
-- parse wrel "" "arc(X, Y, L) = L+1"
-- parse wrel "" "arc(X, Y, L) = 1..L" -- OK
-- parse wrel "" "L = 1..X"
wrel :: GenParser Char st Body
wrel = try(wrel') <|> 
       try(wrel'')

wrel' :: GenParser Char st Body
wrel'    = do {
            -- we could call here arel, but it blows the stack
            ;n <- atom; many space;
            ;myargs <- args
            ;many space          
            ;string "=" 
            ;many space          
            ;weight <- numericexpr
            ;many space          
            ;return (Weighed weight (Plain n myargs True) True)}

-- Here we (re)use myassign stuff from 
-- weights. 
wrel'' :: GenParser Char st Body
wrel''    = myassign''''

--
-- simple relation 
-- parse srel "" "blub(Foo,Bar,Goo)"
-- parse srel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)" -- only the 1st one is handled
-- parse srel "" "r, s, not t" -- unexpected ','
-- parse srel "" "color(1 .. k)"
-- parse srel "" "blub(Foo,\"Bar\",Goo)"
-- parse srel "" "border((N-1)*R+1,N)."
-- A simple relation 
srel :: GenParser Char st Body
srel    = do {n <- atom; many space;
            ;myargs <- args
            ;return (Plain n myargs True)}

-- parse atomrel "" "blub(Foo,Bar,Goo)"
-- parse atomrel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)" -- only the 1st one is handled
-- parse atomrel "" "r, s, not t" 
-- A simple atom 
atomrel :: GenParser Char st Body
atomrel    = try(negatomrel) <|>
             try(posatomrel)


posatomrel :: GenParser Char st Body
posatomrel    = do {n <- atom
            ;return (Plain n [] True)}

negatomrel :: GenParser Char st Body
negatomrel    = do {string "not"; many space; n <- atom
            ;return (Plain n [] False)}

-- typed relation 
-- parse trel "" "arc_S(X, Y) : arc(X, Y)"
-- parse trel "" "not arc_S(X, Y) : arc(X, Yo)"
-- parse trel "" "lc(X, Y) : arc(X, Y, L) = L"
-- parse trel "" "not occurs(Y) : vtx(X) : Y < X"
-- parse trel "" "blub(Foo,Bar,Goo)" -- fails, not typed 
-- parse trel "" "f : vtx(Y) : Y < X."
-- parse trel "" "f : vtx(Y) : Y < X : L = X..Y."
-- parse trel "" "forth(J,NI+1,S-M) :" -- Should fail, we should not parse too far
-- parse trel "" "forth(J,NI+1,S-M) :-" -- Should fail
trel :: GenParser Char st Body
trel    = do { 
              one <- arel;
              skipMany1 (space <|> justcolon <|> space ); 
              rest <- (sepBy1 arel (skipMany1 (space <|> justcolon)));              
              -- the above forces that there is at least        
              -- two entries for the list of types.       
              return (Typed (one:rest))
             }

-- alternative relation 
-- parse altexpr "" "f;g"
-- parse altexpr "" "f ;g;x;y;z" -- OK 
-- parse altexpr "" "Foo;Bar" -- NOK, but should be OK
-- parse altexpr "" "f ;g;x;y;Z" -- NOK

-- These here are not even tested at this point, but left here as 
-- reminder of legacy. 
-- parse altexpr "" "arc_S(X, Y) ; arc(X, Y)" -- NOK
-- parse altexpr "" "not arc_S(X, Y) ; arc(X, Yo)" -- NOK
-- parse altexpr "" "lc(X, Y) ; arc(X, Y, L) = L" -- NOK
-- parse altexpr "" "not occurs(Y) ; vtx(X) ; Y < X" -- NOK
-- parse altexpr "" "f ; vtx(Y) ; Y < X." -- NOK
-- parse altexpr "" "blub(Foo;Bar,Bar;Foo,Goo;Moo)" -- NOK, as it should be -- loops
-- altrel :: GenParser Char st Body -- added 
altexpr :: GenParser Char st MyExpr 
altexpr    = do { -- one <- numericexpr; -- this will diverge
              -- one <- numeric;
              -- one <- numericexpr; -- loops
              one <- expr; -- loops
              skipMany1 (space <|> char ';' <|> space ); 
              -- rest <- (sepBy numericexpr (skipMany1 (space <|> char ';')));              
              -- rest <- (sepBy numeric (skipMany1 (space <|> char ';')));              
              rest <- (sepBy expr (skipMany1 (space <|> char ';')));              
              -- the above forces that there is at least        
              -- two entries for the list of types.       
              return (Alternative (one:rest))
             }
{--
altrel    = do {one <- arel;
              skipMany1 (space <|> char ';' <|> space ); 
              rest <- (sepBy arel (skipMany1 (space <|> char ';')));              
              -- the above forces that there is at least        
              -- two entries for the list of types.       
              return (Alternative (one:rest))
             }
--}



-- This is needed so that heads of rules are not parsed as 
-- beginnings of typed lists. 
-- foo(X) :- bar(X) 
-- could otherwise be intepreted as (foo(X)) (:) (- bar(X))
-- which would never parse. for the 2nd part. 
justcolon :: GenParser Char st Char
justcolon = do {
            g <- char ':';
            notFollowedBy (char '-');
            return g
          }

-- Question:
-- parse rel "" "blub(Foo,Bar,Goo),\"no\""
-- fails so that no is not detected
-- Where do we allow not?
-- only for facts and atoms, but also inside choices?
-- parse rel "" "arc(X, Y, L) = L"
-- parse rel "" "lc(X,Y) : arc(X, Y, L)"
-- parse rel "" "lc(X,Y) : arc(X, Y, L) = L"
-- parse rel "" "blub(Foo,Bar,Goo)"
-- parse rel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)" -- only the 1st one is handled
-- parse rel "" "r, s, not t" -- only the 1st one is handled
-- parse rel "" "not r, s, not t" -- only the 1st one is handled
-- parse rel "" "ttask(I,D) : ttask(I,D) : not haslet(I) : not tsklet(I) = D"
-- parse rel "" "field(X;X+1,Y)" -- NOK, wont parse the arguments 
-- parse rel "" "border((N-1)*R+1,N)."

rel :: GenParser Char st Body
{--
rel     = try(negrel) <|>
          try(trel) <|>
          try(srel)
--}       
rel     =  do { 
                try(trel) <|> 
                try(arel) <|>
                try(atomrel)} -- must be last 

    

-- lbrace :: GenParser Char st [Char]
-- parse lbrace "" "{" 
lbrace :: GenParser Char st ()
lbrace = do {
  skipMany space;
  char '{'; 
  skipMany space;
  }
  
rbrace :: GenParser Char st ()
rbrace = do {
  skipMany space;
  char '}'; 
  skipMany space;
  }

--
-- Here we assume that any excess space has been
-- removed already before the comma. 
listsep :: GenParser Char st ()
listsep = do {
  char ',';
  skipMany space;
  }

-- parse myassign "" "M = #min [ est(I,S) : est(I,S) : hasest(I) = S ]" 
-- parse myassign "" "M = [ est(I,S) : est(I,S) : hasest(I) = S ]"
-- parse myassign "" "M = { est(I,S) : est(I,S) : hasest(I) = S }"
myassign :: GenParser Char st Body
myassign = 
         try(myassign') <|>
         try(myassign'') <|> 
         try(myassign''') 

myassign' :: GenParser Char st Body
myassign' = do {
         lh <- lefthand;
         skipMany space;
         char '=';
         skipMany space;
         c <- myoptimize;
         return (Assignment lh c True)
}

myassign'' :: GenParser Char st Body
myassign'' = do {
         lh <- lefthand;
         skipMany space;
         char '=';
         skipMany space;
         c <- mycount;
         return (Assignment lh c True)
}

myassign''' :: GenParser Char st Body
myassign''' = do {
         lh <- lefthand;
         skipMany space;
         char '=';
         skipMany space;
         c <- mychoice;
         return (Assignment lh c True)
}

-- For L=1..X
-- parse myassign'''' "" "L = 1..X"
myassign'''' :: GenParser Char st Body
myassign'''' = do {
         lh <- lefthand;
         skipMany space;
         char '=';
         skipMany space;
         c <- nexpr;
         return (Assign lh c)
}


-- parse mychoice "" "1 {blub(Foo,Bar,Goo)} 2"
-- parse mychoice "" "M{blub(Foo,Bar,Goo)}"
-- parse mychoice "" "{blub(Foo,Bar,Goo)}"
-- parse mychoice "" "{  sat(C) : clause(C) } k-1" 
-- parse mychoice "" "{ lc(X, Y) : arc(X, Y, L) : mooh(Z) } 1"  
-- parse mychoice "" "1 { p, t }" 
-- parse mychoice "" "{ p, t, not x}" 
-- parse mychoice "" "{ p, t, not x }" 
-- parse mychoice "" "1 { p, not t t}"  --- error, as it should be 
-- parse mychoice "" "not 1 { at(T,D,P) : peg(P) } 1"
-- parse mychoice "" "{  sat(C) : clause(C) } k*(1/X)"
mychoice :: GenParser Char st Body
mychoice = do {
         try(mychoice') <|>
         try(mychoice'')
         }

mychoice' :: GenParser Char st Body
mychoice'    = do { low <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
                   content <- 
                   between (lbrace)
                            -- (skipMany1 (space <|> char ')')) 
                           (rbrace) 
                           -- rel; 
                           (sepBy rel listsep);
                           -- XXX perhaps here we may need to force at least one comma 
                           --- (sepBy rel (skipMany (space <|> char ',')));
--                         return content}
                   high <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
                         return (Card low high content True)}

mychoice'' :: GenParser Char st Body
mychoice''    = do { 
                string "not"; 
                skipMany1 space;
                res <- mychoice';
                return (negateabody res)
               }


mychoiceold :: GenParser Char st Body
mychoiceold    = do { low <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
                   content <- 
                   between (skipMany1 (space <|> char '{' <|> space ))
                            -- (skipMany1 (space <|> char ')')) 
                           (skipMany1 ( space <|> char '}' <|> space)) 
                           -- rel; 
                           (sepBy rel (skipMany1 (space <|> char ',')));
                           -- XXX perhaps here we may need to force at least one comma 
                           -- (sepBy rel (skipMany (space <|> char ',')));
--                         return content}
                   high <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
                         return (Card low high content True)}
                         -- return (Card "any" "any" content content2 True)}


-- parse mycount "" "1 [blub(Foo,Bar,Goo)] 2"
-- parse mycount "" "M[blub(Foo,Bar,Goo)]"
-- parse mycount "" "[blub(Foo,Bar,Goo)]"
-- parse mycount "" "[  sat(C) : clause(C) ] k-1" 
-- parse mycount "" "k [ lc(X, Y) : arc(X, Y, L) = L ]"
-- parse mycount "" "k [ lc(X, Y) : arc(X, Y, L) = L]" -- OK
-- parse mycount "" "k [ X : Y = L]" -- NOK
-- parse mycount "" "min [ lc(X, Y) : arc(X, Y, L) = L ]"
-- parse mycount "" "#max [ lc(X, Y) : arc(X, Y, L) = L ]"
mycount :: GenParser Char st Body
mycount    = do {
                try(mycount') <|>
                try(mycount'')
                }

mycount' :: GenParser Char st Body
mycount'    = do { low <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
                   content <- 
                   between (skipMany1 (space <|> char '[' <|> space ))
                            -- (skipMany1 (space <|> char ')')) 
                           (skipMany1 ( space <|> char ']' <|> space)) 
                           -- rel; 
                           (sepBy rel (skipMany1 (space <|> char ',')));
--                         return content}
                   high <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
                         return (Count low high content True)}

mycount'' :: GenParser Char st Body
mycount''    = do { 
                string "not"; 
                skipMany1 space;
                res <- mycount';
                return (negateabody res)
               }


-- parse myoptimize "" "k [ X : Y = L]" -- NOK
-- parse myoptimize "" "min [ lc(X, Y) : arc(X, Y, L) = L ]"
-- parse myoptimize "" "#max [ lc(X, Y) : arc(X, Y, L) = L ]"
myoptimize :: GenParser Char st Body
myoptimize    = do { minmax <- optstmt;
                   content <- 
                   between (skipMany1 (space <|> char '[' <|> space ))
                           (skipMany1 ( space <|> char ']' <|> space)) 
                           (sepBy rel (skipMany1 (space <|> char ',')));
                         return (Optimize minmax content True)}

optstmt :: GenParser Char st Bool
optstmt = do {
        try(do {string "#max"; return True}) <|>
        try(do {string "max"; return True}) <|>
        try(do {string "#min"; return False}) <|>
        try(do {string "min"; return False}) 
}


-- anumber :: GenParser Char st String
-- Urgh, a redundant try. 
-- One of these days this could be done, but I suppose
-- the reduction of try should start elsewhere:
-- http://www.haskell.org/pipermail/haskell-cafe/2002-August/003280.html
anumber :: GenParser Char st Atom 
anumber    = 
           try(anumber'') <|>
           anumber'

anumber'    = do 
           {
             low <- many1 digit; many space; return (Const low)
           }

anumber''    = do 
           {
             char '-'; skipMany space; low <- many1 digit; many space; return (Const ('-':low))
           }




-- fails:          
-- parse aggregateconst "" "1F4"
-- parse aggregateconst "" "C"
-- Right "1" 
-- aggregateconst :: GenParser Char st String
-- aggregateconst :: GenParser Char st Atom
aggregateconst :: GenParser Char st MyExpr
aggregateconst    =  
  -- try(nexpr) <|>
  try(do { r <- variable; return (Sym r) }) <|>
  try(do { num <- anumber; return (Number num)}) -- <|> 
 <?> "Expected a number of variable as aggregation constraint"

-- parse mybop "" ">"
mybop :: GenParser Char st BOp
mybop    = 
    try(do {s <- string "<="; return LtEq}) <|> 
    try(do {s <- string ">="; return GtEq}) <|> 
    try(do {s <- string "!="; return Neq}) <|> 
    try(do {s <- string "=="; return Eqeq}) <|>
    try(do {c <- char '>'; return Gt}) <|>
    try(do {c <- char '<'; return Lt}) <|>
    try(do {c <- char '='; return Eq}) 
           <?> "Expected a comparison operation: >,<,<=,>=,=,=="

-- parse bexpr "" "k > 2"
-- parse bexpr "" "X < Y" -- OK degree-bounded_connected_subgraph.lp
bexpr :: GenParser Char st Body
bexpr = do { 
              -- a1 <- numeric; 
              a1 <- numericexpr; 
              skipMany space; 
              o <- mybop;
              skipMany space; 
              -- a2 <- numeric; 
              a2 <- numericexpr; 
              return (BExpr o a1 a2)
        }


-- parse myop "" "+"
myop :: GenParser Char st MyOp
myop    = 
    try(do {c <- char '+'; return Plus}) <|>
    try(do {c <- char '-'; return Minus}) <|>
    try(do {c <- char '*'; return Mult}) <|>
    try(do {c <- char '/'; return Div}) <|>
    try(do {c <- string ".."; return Range}) <|>
    try(do {s <- string "mod"; return Mod}) <|>
    try(do {s <- string "#mod"; return Mod})
           <?> "Expected an arithmetic operation: +,-,*,/,mod,#mod"

-- Urgh, here we are limiting to two-op expressions.
-- Use the dedicated inbuilt expr parser?
-- parse nexpr "" "k + 2"
-- parse nexpr "" "k + 2 + Z" -- will not parse Z
-- parse nexpr "" "k + Z"
-- parse nexpr "" "k + + Z" -- parse error
-- Maybe replacement nexpr to expr will now work. 
nexpr :: GenParser Char st MyExpr
nexpr = do { 
              -- a1 <- numericexpr; 
              a1 <- numeric; 
              skipMany space; 
              o <- myop;
              skipMany space; 
              -- a2 <- numericexpr; 
              a2 <- numeric; 
              return (Arith o a1 a2)
        }
-- parse numeric "" "1 + 2" -- only 1 parsed
-- parse numeric "" "k + 2" -- only k parsed
-- parse numeric "" "k"
-- parse numeric "" "1"
-- parse numeric "" "X"
numeric :: GenParser Char st MyExpr
numeric    =
{--
{-- We cannot have this here as we overflow the stack --}
    try (do { 
              a1 <- numericexpr; 
              skipMany space; 
              o <- myop;
              skipMany space; 
              a2 <- numericexpr; 
              return (Arith o a1 a2)}) <|>
--} 
    -- try(nexpr) <|>
    try(do { v <- variable; return (Sym v) }) <|>
    try(do { v <- atomsimple; return (Sym v) }) <|>
    try(do { n <- anumber; return (Number n) }) <|>
    try(do { n <- atomquoted; return (Sym n) })
    <?> "A variable, atom or number"

-- parse numericexpr "" "k + 2"
-- parse numericexpr "" "k + 2 * Z"
-- parse numericexpr "" "(k + 2) * Z"
-- parse numericexpr "" "(k mod 2) / Z"
-- parse numericexpr "" "(k mod \"jopi\") / (Z)"
-- parse numericexpr "" "k"
-- parse numericexpr "" "1"
-- parse numericexpr "" "1;2"
-- parse numericexpr "" "g;k"
-- parse numericexpr "" "X;Y;k;1"
-- parse numericexpr "" "g/2;k+1" -- Only parses the first g/2
-- parse numericexpr "" "X;Y"
-- parse numericexpr "" "X"
-- parse numericexpr "" "X+1"
-- parse numericexpr "" "1..X"
-- parse numericexpr "" "(N-1)*R+1"
numericexpr :: GenParser Char st MyExpr
numericexpr = 
    -- try(nexpr) <|>
    try (altexpr) <|> -- added 
    try(expr) <|>
    try(numeric)
    <?> "A numeric expression"

-- This uses the parsec purpose-built expression parser 
expr :: GenParser Char st MyExpr 
expr    = buildExpressionParser table factor
        <?> "expression"

table   = [[  -- Infix (do{string "*" >> return (Op Times)}) AssocLeft
              op "*" Mult AssocLeft
            , op "/" Div AssocLeft
            , op ".." Range AssocLeft]
          ,[  op "+" Plus AssocLeft
            , op "-" Minus AssocLeft
            , op "mod" Mod AssocLeft
            , op "#mod" Mod AssocLeft]
          ]
          where 
          -- The try here is overkill, it is needed to separate '..' 
          -- from the finalizing '.'. We could just write it out 
          -- inside the table to avoid having a try for the one 
          -- letter tokens. 
          -- op opstr opval assoc = Infix (do{string opstr >> return (Arith opval)}) assoc
          op opstr opval assoc = Infix (do{try(string opstr) >> return (Arith opval)}) assoc

factor :: GenParser Char st MyExpr
factor  =       
        -- This must be before the others or we'll loop 
        try(do { skipMany space; a <- numeric; skipMany space; return a}) <|>    
        do{ skipMany space; char '('; skipMany space; 
            ; x <- expr
            ; skipMany space
            ; char ')'; skipMany space; 
            ; return x
            } <|> 
        -- This must be after the parenthesis or we'll loop
        -- but we must make sure that this is a valid starting 
        -- point or the expression parser comes here always 
        -- This may happen if give a statement that cannot be 
        -- recognized, since nothing matches, we recurse. 
        do {
           noneOf "{[]},.+-*/=:;";
           expr
        }
        -- <|> number
        <?> "simple expression"




-- parse atomm "" "blub"
-- parse atomm "" "\"blub\""
-- atomm :: GenParser Char st (String,[String])
atomm :: GenParser Char st (Atom,[MyExpr])
-- atomm    = do { r <- atom; return (r,[])}
-- atomm :: GenParser Char st (Atom,[MyExpr])
atomm    = do { r <- atom; return (r,[])}

-- Generic rel, fact or relation
-- parse genrel "" "blub"
-- parse genrel "" "blub(Foo,Bar,Goo)"
-- parse genrel "" "waitingfor(_,_)"
-- parse genrel "" "X > Y" 
-- parse genrel "" "{blub(Foo,Bar,Goo)}"
-- parse genrel "" "{blub(Foo,Bar,Goo),blab(Zub,Zap,Zoo)}"
-- parse genrel "" "1{blub(Foo,Bar,Goo)}2"
-- parse genrel "" "1 { maps_to(X, U) } 1"
-- parse genrel "" "{  sat(C) : clause(C) } 1" 
-- parse genrel "" "{  sat(C) : clause(C) } k-1"
-- parse genrel "" "{  sat(C) : clause(C) } k-1+2"
-- parse genrel "" "{  sat(C) : clause(C) } k-1+2*X"
-- parse genrel "" "{ true(A) : atom(A) }" 
-- parse genrel "" "2{i(A,\"wp1:active\",\"yes\"),d(A,\"wp1:active\",\"no\")}2"
-- parse genrel "" "M{\"wp1:commits\"(Cap,A3):\"rdf:type\"(A3,\"wp1:Activity\")}"
-- parse genrel "" "{i(A,\"wp1:active\",\"yes\"),d(A,\"wp1:active\",\"no\")}2"
-- parse genrel "" "{blub(Foo,\"Bar\",Goo)}"
-- parse genrel "" "[ lc(X, Y) : arc(X, Y, L) = L ]" 
-- parse genrel "" "not occurs(Y) : Y < X, vtx(X)" -- vtx should not be parsed 
-- parse genrel "" "f : vtx(Y) : Y < X"
-- parse genrel "" "person(a; b; c)"
-- parse genrel "" "#max [ lc(X, Y) : arc(X, Y, L) = L ]"
-- parse genrel "" "M = #min [ est(I,S) : est(I,S) : hasest(I) = S ]" -- NOK, but should be 
-- parse genrel "" "not 1 { at(T,D,P) : peg(P) } 1"
-- parse genrel "" "1 { pos(N,L,T) : L = 1..X : T = 1..Y } 1"
-- parse genrel "" "foo(X..Y)"
-- parse genrel "" "{  sat(C) : clause(C) } k*1." -- NOK, ignores the formula, only k stays 
-- parse genrel "" "{  sat(C) : clause(C) } k*1" -- NOK, ignores the formula, only k stays 
-- parse genrel "" "border((N-1)*R+1,N)."  -- stops at * 
genrel :: GenParser Char st Body
genrel    = 
            try(myassign) <|> 
            try(myoptimize) <|>
            try(mychoice) <|>
            try(mycount) <|>
            try(rel) <|> 
            try(bexpr) <|> -- X > Y 
            -- This is endlessly ugly, and may be the reason 
            -- we fail silently. 
            -- It is to detect a single atom and wrap 
            -- it with an empty list of arguments. 
           try( do { (r,l) <- atomm; return (Plain r l True) } )
           <?> "relation, choice or simple atom"

-- parse body "" "blub(Foo,Bar,Goo), blab(Baa), bii"
-- parse body "" "vtx(X), vtx(Y), X < Y, not r(X, Y)"
-- parse body "" "not arc_S(X, Y) : arc(X, Y), vtx(Y)"
-- parse body "" "not arc_S(X, Y) : arc(X, Y)"
-- parse body "" "occurs(X), not occurs(Y) : Y < X, vtx(X)"
-- parse body "" "not occurs(Y) : Y < X, vtx(X)" 
-- parse body "" "occurs(X), not occurs(Y) : vtx(X) : Y < X, vtx(X)" 
-- parse body "" "waitingfor(_,_)."
-- parse body "" "M = #min [ est(I,S) : est(I,S) : hasest(I) = S ],\nN = #max [ est(J,T) : est(J,T) : hasest(J) = T ], sest(P), est."
-- parse body "" "L = { leaking(V) : leaking(V) }." 
-- parse body "" "{  sat(C) : clause(C) } k*1."
-- parse body "" "{  sat(C) : clause(C) } (k-1)."
-- parse body "" "field(X;X+1,Y)." -- NOK
-- parse body "" "done(L,S), reach(J,NJ,M), forth(I,NI,S-(M+1)), NI = L-(NJ+1),\n           link(I,J,V),     leaking(V)." -- stops at NI 
-- parse body "" "link(I,J,V),\n     leaking(V)."
-- parse body "" "border((N-1)*R+1,N)."  -- stops at * 
body :: GenParser Char st [Body]
body    = do (sepBy genrel (skipMany1 (space <|> char ',')))

-- parse rule "" "blub(Foo,Bar,Goo) :-  blab(Baa), bii."
-- parse rule "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii."
-- parse rule "" "ok :- k [ lc(X, Y) : arc(X, Y, L) = L ] ."
-- parse rule "" "initial(X) :- occurs(X), not occurs(Y) : Y < X, vtx(X)." 
-- parse rule "" "{ lc(X, Y) : arc(X, Y, L) } 1 :- vtx(X)." 
-- parse rule "" "occurs(X) :- lc(X, Y), arc(X, Y, L)."
-- parse rule "" "initial(X) :- occurs(X), not occurs(Y) : vtx(X) : Y < X, vtx(X)."
-- parse rule "" "r(Y) :- lc(X, Y), initial(X), arc(X, Y, L)."             
-- parse rule "" "r(Y) :- lc(X, Y), r(X), arc(X, Y, L)."             
-- parse rule "" "denied(X,Y)." -- should not pass 
-- parse rule "" "1 { p(X), t(X) } :- 1 {r(X), s(X), not t(X)} 2."             
-- parse rule "" "1 { p, t } :- 1 {r, s, not t} 2."             
-- parse rule "" "ready(A) :- \"rdf:type\"(A,\"wp1:Activity\"), not missing_commit(A)."

-- parse rule "" "ready(A :- \"rdf:type\"(A,\"wp1:Activity\"), not missing_commit(A)." -- should fail
-- parse rule "" "ready(A) :- \"rdf:type\" A,\"wp1:Activity\"), not missing_commit(A)." -- should fail
-- parse rule "" "time(M..N)     :- mintime(M), maxtime(N)." -- OK
-- parse rule "" "ests(M..N+P) :- M = #min [ est(I,S) : est(I,S) : hasest(I) = S ],\nN = #max [ est(J,T) : est(J,T) : hasest(J) = T ], sest(P), est." -- OK
-- parse rule "" "dist(#abs(RK1-RK2)) :- restaurant(RN1,RK1), restaurant(RN2,RK2)." -- NOK, Abs
-- parse rule "" "1 { pos(N,L,T) : L = 1..X : T = 1..Y } 1 :- net(N), layers(X), tracks(Y)." -- NOK
-- parse rule "" "dneighbor(n,X,Y,X+1,Y) :- field(X;X+1,Y)."
-- parse rule "" "forth(J,NI+1,S-M) :- done(L,S), reach(J,NJ,M), forth(I,NI,S-(M+1)), NI = L-(NJ+1),\n           link(I,J,V),     leaking(V)."
-- parse rule "" "border((N-1)*R+1) :- number(N), sqrt(R), N<=R."

rule :: GenParser Char st Rules    
rule    = do { 
               n <- genrel; 
               -- n <-rel; 
               -- (skipMany1 (space <|> string ":-")); 
               skipMany space;
               string ":-"; 
               skipMany space;
               b <-body; 
               skipMany space; 
               char '.';
               return (Rule n b) }

-- parse deny "" ":-  blab(Baa), bii."
-- parse deny "" ":-  blab(Baa),\n bii."
-- parse deny "" ":- {  sat(C) : clause(C) } k-1."
-- parse deny "" ":- vtx(X), vtx(Y), X < Y, not r(X, Y)."
-- parse deny "" ":- not ok."
-- parse deny "" ":- vtx(X), occurs(X), not r(X)."
deny :: GenParser Char st Rules
deny    = do { 
               string ":-"; 
               skipMany space;
               b <-body; 
               skipMany space; 
               char '.';
               -- return (("",[]),b) }
               return (Deny b) }

-- parse fact "" "waitingfor(_,_)."
-- parse fact "" "waitingfor(X,Y)."
fact :: GenParser Char st Rules
fact    = do { 
               -- setState Map.empty; -- not working 
               b <- body; 
               skipMany space; 
               char '.';
               return (Fact b) }

-- The replication of hide and show should be redone
----------------------------------------------------
showf :: GenParser Char st Rules
showf    = try (showfc) <|> 
           try (showfempty)

hidef :: GenParser Char st Rules
hidef    = try (hidefc) <|> 
           try (hidefempty)


showfc :: GenParser Char st Rules
showfc    = do { 
               string "show";
               skipMany1 space; 
               Fact f <- fact;
               return (Show f) }

hidefc :: GenParser Char st Rules
hidefc    = do { 
               string "hide";
               skipMany1 space; 
               Fact f <- fact;
               return (Hide f) }

showfempty :: GenParser Char st Rules
showfempty    = do { 
               string "show";
               skipMany space; 
               char '.';
               return (Show [Empty]) }

hidefempty :: GenParser Char st Rules
hidefempty    = do { 
               string "hide";
               skipMany space; 
               char '.';
               return (Hide [Empty]) }

----------------------------------------------------
-- Gringo versions of show and hide

gshowfc :: GenParser Char st Rules
gshowfc    = do { 
               string "#show";
               skipMany1 space; 
               Fact f <- fact;
               return (GShow f) }

ghidefc :: GenParser Char st Rules
ghidefc    = do { 
               string "#hide";
               skipMany1 space; 
               Fact f <- fact;
               return (GHide f) }

gshowfarity :: GenParser Char st Rules
gshowfarity    = do { 
               string "#show";
               skipMany space; 
               a <- atom;
               char '/';
               skipMany space; 
               Const n <- anumber;
               skipMany space; 
               char '.';
               return (GShow [Arity a n]) }

ghidefarity :: GenParser Char st Rules
ghidefarity    = do { 
               string "#hide";
               skipMany space; 
               a <- atom;
               char '/';
               skipMany space; 
               Const n <- anumber;
               skipMany space; 
               char '.';
               return (GHide [Arity a n]) }

gshowfempty :: GenParser Char st Rules
gshowfempty    = do { 
               string "#show";
               skipMany space; 
               char '.';
               return (GShow [Empty]) }

ghidefempty :: GenParser Char st Rules
ghidefempty    = do { 
               string "#hide";
               skipMany space; 
               char '.';
               return (GHide [Empty]) }

gshowf :: GenParser Char st Rules
gshowf    = try (gshowfc) <|> 
           try (gshowfarity) <|>
           try (gshowfempty)

ghidef :: GenParser Char st Rules
ghidef    = try (ghidefc) <|> 
           try (ghidefarity) <|> 
           try (ghidefempty)

-- parse extdef "" "external f(X,Y,b)."
extdef :: GenParser Char st Rules
extdef    = do { 
               string "external";
               skipMany1 space; 
               Fact f <- fact;
               return (External f) }

-- parse funcdef "" "function f."
funcdef :: GenParser Char st Rules
funcdef    = do { 
               string "function";
               skipMany1 space; 
               f <- atom;
               skipMany space; 
               string ".";
               return (Function [(Plain f [] True)]) }

-- parse constdef "" "const k = 10."
constdef :: GenParser Char st Rules
constdef    = do { 
               string "const";
               skipMany1 space; 
               nm <- atom;
               string "="; 
               skipMany1 space; 
               e <- numericexpr;
               char '.'; 
               return (Consts [(Assign nm e)]) }

lefthand :: GenParser Char st Atom
lefthand = try(do {(a,_) <- atomm; return a}) <|> -- (Atom,[MyExpr])
           try(variable) 

-- parse mindef "" "minimize [a1,a2]."
-- parse mindef "" "minimize [a1 =5,a2=6,a3]."
-- parse mindef "" "minimize {b1,b2}."
-- parse mindef "" "minimize [a1(X),a2]." -- this should not parse, but we overapproximate
mindef :: GenParser Char st Rules
mindef    = do { 
               string "minimize";
               skipMany1 space; 
               b <- choiceorcount;
               skipMany space; 
               string ".";
               return (Minimize [b]) }

-- parse mindef "" "maximize [a1,a2]."
-- parse mindef "" "maximize {b1,b2}."
maxdef :: GenParser Char st Rules
maxdef    = do { 
               string "maximize";
               skipMany1 space; 
               b <- choiceorcount;
               skipMany space; 
               string ".";
               return (Minimize [b]) }

choiceorcount = 
              try(mycount) <|>
              try(mychoice)

-- parse compute "" "compute models {b1,b2}."
-- parse compute "" "compute Models {b1,b2}." -- should fail 
compute :: GenParser Char st Rules
compute    = do { 
               string "compute";
               skipMany1 space;
               n <- atom; 
               skipMany space; -- atom may already eat the trailing space 
               b <- choiceorcount;
               skipMany space; 
               string ".";
               return (Computes n [b]) }

-- parse showorhide "" "show waitingfor(_,_)."
-- parse showorhide "" "#show waitingfor(_,_)."
-- parse showorhide "" "#hide waitingfor(_,_)."
-- parse showorhide "" "#hide."
-- parse showorhide "" "#hide pos/3."
-- parse showorhide "" "#show pos/3."
showorhide :: GenParser Char st Rules
showorhide    = 
              try(showf) <|> 
              try(hidef) <|>
              try(gshowf) <|> 
              try(ghidef) 


-- parse rulebase "" ":-  blab(Baa),\n bii."
-- parse rulebase "" "{ true(A) : atom(A) }."
-- parse rulebase "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii."
-- parse rulebase "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.\n\n:-  zuu(Zaa),\n zii."
-- parse rulebase "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.:-  zuu(Zaa),\n zii."
-- parse rulebase "" "\n:-  zuu(Zaa),\n zii.blub(Foo,Bar,Goo) :-  blab(Baa),\n bii.\n"
-- parse rulebase "" "p(X) :- q(X), d(X).\n"
-- parse rulebase "" "ready(A) :- rdftype(A,\"wp1:Activity\"), not missing_commit(A)."
-- parse rulebase "" "ready(A) :- rdftype(A,\"wp1:Activity\"), not missing_commit(A).\n\nmissing_commit(A) :- \n    \"rdf:type\"(A,\"wp1:Activity\"),\n    \"wp1:uses\"(A,Cap),\n    not \"wp1:commits\"(Cap,A).\n " 
-- parse rulebase "" "show deadlock(_).\nshow conflict(_,_,_).\nshow banish(_)."
-- parse rulebase "" "ready(A) :- rdftype(A,\"wp1:Activity\"), not missing_commit(A).\n\nmissing_commit(A) :- \n    \"rdf:type\"(A,\"wp1:Activity\"),\n    \"wp1:uses\"(A,Cap),\n    not \"wp1:commits\"(Cap,A).\nshow deadlock(_).\nshow conflict(_,_,_).\nshow banish(_)." 

-- parse rulebase "" "ready(A :- \"rdf:type\"(A,\"wp1:Activity\"), not missing_commit(A)." -- should fail
-- parse rulebase "" "ready(A) :- \"rdf:type\" A,\"wp1:Activity\"), not missing_commit(A)." -- should fail
-- parse rulebase "" "k { in(X) : vtx(X) }.\n:- in(X), in(Y), not arc(X, Y), vtx(X), vtx(Y).\n"
-- parse rulebase "" "const k = 10."
-- parse rulebase "" "#hide.\n#show dom/1.\n"
-- parse rulebase "" "#hide.\n#show dom/1.\n{ dom(U) : vtx(U) }."
-- parse rulebase "" "#hide.\n#show dom/1.\n{ dom(U) : vtx(U) }.\nuedge(U,V) :- edge(U,V), U < V."


rulebase :: GenParser Char st [Rules]
rulebase = (sepEndBy (threerule) spaces) -- this actually works with the hamiltonian!
                                         -- but not with test3.lp. 
-- rulebase = manyTill threerule eof
{-- --
-- This was the previous rulebase which swallowed 
-- all errors. 
-- The skipMany space seem to be needed...
rulebase    = many (
                    try ((skipMany space) >> deny) <|>
                    try ((skipMany space) >> rule) <|>
                    try ((skipMany space) >> fact) -- <|> 
                    -- try (fact) 
                   ) <?> "Not a rule, denial or fact."
-- --}

-- parse ruleorfact "" "k { in(X) : vtx(X) }.\n"
-- parse ruleorfact "" "a(X,Y) :- in(X), in(Y), not arc(X, Y), vtx(X), vtx(Y).\n"
-- We have to factor this out; these two are 
-- really similar and only after trying to match a rule
-- we know whether it was a fact after all. 
ruleorfact = try(rule) <|> 
             fact

threerule = do {
            skipMany space;
            try(showorhide) <|> -- the following have fixed keywords in the beginning
            try(constdef) <|>   -- that's why we try them before the general ones
            try(compute) <|>   --
            try(maxdef) <|>   --
            try(mindef) <|>   --
            try(funcdef) <|>   --
            try(extdef) <|>   --
            deny <|>     -- here we estart with the generic ones, if they all are tried
            ruleorfact   -- the error messages are suppressed 
            <?> "rule, denial or fact, ugh"}
 

-- rulebase    = many rule

-- parse rulebase "" "1 { maps_to(X, U) : vtx_H(U) } 1 :- vtx_G(X).\n1 { maps_to(X, U) : vtx_G(X) } 1 :- vtx_G(U).\n :- maps_to(X, U),\n        maps_to(Y, V),\n        arc_G(X, Y),\n        not arc_H(U, V),\n        vtx_H(U),\n        vtx_H(V).\n :- maps_to(X, U),\n        maps_to(Y, V),\n        not arc_G(X, Y),\n        arc_H(U, V),\n        vtx_G(X),\n        vtx_G(Y).\n"
-- parse rulebase "" "1 { maps_to(X, U) } 1 :- vtx_G(X)."

-- parse rulebase "" "ready(A) :- \"rdf:type\"(A,\"wp1:Activity\"), not missing_commit(A)."


-- rule = header >> string ":-" >> body

-- The actual call to the parser is in 
-- parse rulebase "" istr 

-- But if we want to have user state, here an empty map, 
-- we need 
-- runParser rulebase Map.empty "" istr 
-- Note that the "" is the filename that is used for error
-- messages, may be empty as here. 

-- For some reason I cant make this 
-- to return the result without using 
-- putStrLn to render it first?
-- parseSmod'' :: String -> IO ()
parseSmod'' :: String -> IO (Either ParseError [Rules])
parseSmod'' fname = 
    do {
      inh <- System.IO.openFile fname ReadMode;
      istr <- System.IO.hGetContents inh; 
      putStrLn (istr); 
      -- return(istr);
      System.IO.hClose inh;
      return (parse rulebase "" istr)
    }

parseSmod' :: String -> IO () -- this with hClose ending
-- parseSmod' :: String -> IO String
-- parseSmod' :: String -> IO String
parseSmod' fname = 
    do {
      -- inh <- System.IO.openFile "test.lp" ReadMode;
      inh <- System.IO.openFile fname ReadMode;
      istr <- System.IO.hGetContents inh; 
      System.IO.hClose inh;
      -- res <- parse rulebase "" istr; 
      putStrLn (show( parse rulebase "" istr )); 
      -- res <- show( parse rulebase "" istr); 
    }

-- parseSmod :: String -> IO ()
-- parseSmod :: String -> IO (Either ParseError [Rules])
-- Used just to debug stuff, see smod2txt below. 
parseSmod fname = 
    do {
      istr <- readFile fname; 
      return (parse rulebase "" istr)
    }

-- In order to feed the result of parseSmod 
-- to this we need to
-- let goo = System.IO.Unsafe.unsafePerformIO moo
-- smod2txt goo
-- but what we really want to do is to 
-- perform the computaiton before going 
-- to IO 
smod2txt:: (Either ParseError [Rules]) -> String 
smod2txt rb = 
    case rb of 
      Left _ -> show("error")
      Right r -> show(r)

unatom a = 
    case a of 
      Var s -> s 
      Const s -> s

unop op = 
    case op of 
      Plus -> "+"
      Minus -> "-"
      Mult -> "*"
      Div -> "/"
      Mod -> "mod"
      Range -> ".."

unbop op = 
    case op of 
      Gt -> ">"
      Lt -> "<"
      GtEq -> ">="
      LtEq -> "<="
      Eq -> "="
      Neq -> "!="
      Eqeq -> "=="

unarith op a1 a2 = 
    (unmyexpr a1) ++ " " ++  (unop op) ++ " " ++ (unmyexpr a2)

unmyexpr a = 
    case a of 
      Sym s -> (unatom s)
      Number s -> (unatom s)
      Alternative l -> List.concat $ (List.intersperse ";" (List.foldr (\x accu -> (unmyexpr x):accu) [] l))
      Arith op a1 a2 -> (unarith op a1 a2)


type Counter = Int -> IO Int 

makeCounter :: IO Counter
makeCounter = do 
  r <- newIORef 0
  return (\i -> do modifyIORef r (+i)
                   readIORef r)


-- newStdGen >>= print.random
iorand = 
    do 
      r <- randomIO
      return (r::Int)

-- And later 
--    let (a,b) = random (System.IO.Unsafe.unsafePerformIO iorand)::(Int,StdGen)
--                in b

-- Naughty unsafe 
--- myrand :: (Random a, Num a, Ord a) => () -> a
--- randomIO :: (Random a) => IO a
myrand () = 
      -- System.IO.Unsafe.unsafePerformIO (randomRIO (0,2^32))
    let res = System.IO.Unsafe.unsafePerformIO (randomIO) in 
    if res < 0 then (0-res) else res

-- An unsafe counter 
mknext :: (Num a) => IO (IO a)
mknext = do 
  ref <- newIORef 0
  return (
    do 
      modifyIORef ref (+1)
      readIORef ref)

-- To use:
-- let a = unsafectr()
-- let myid = getnext(a)  
unsafectr = System.IO.Unsafe.unsafePerformIO (mknext)

-- getnext :: IO Integer -> Integer
getnext c = System.IO.Unsafe.unsafePerformIO (c)

-- erroneous
mknext' :: (Num a) => IO a
mknext' = do 
  ref <- newIORef 0
  return . System.IO.Unsafe.unsafePerformIO $
    do 
      modifyIORef ref (+1)
      readIORef ref


myrandIO () = 
      randomRIO (0,2^32)
