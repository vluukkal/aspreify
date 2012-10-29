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
-- import List
import qualified Data.List as List
import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

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
            | Arith MyOp MyExpr MyExpr 
            deriving(Show,Eq)


-- To test this:
-- parse nvariable "" "Foo"
-- parse nvariable "" "F"
-- parse nvariable "" "X > Y"
nvariable :: GenParser Char st Atom
nvariable   = do{ c  <- upper
                ; cs <- option "" (many (noneOf "\n\r\t (){[]},.=:"))
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
                ; cs <- option "" (many (noneOf "\n\r\t (){[]},.+-*/=:"))
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



-- parse atom "" "Foo" -- should fail 
-- parse atom "" "foo"
-- parse atom "" "\"Foo\""
-- parse atom "" "\"wp1:Person\""
-- parse atom "" "1"

-- parse atom "" "m"
-- Fails on 09.11.2011
-- parse atom "" "M"
-- Left (line 1, column 1):
-- unexpected "M"
-- expecting a fact starting with lowercase or quoted string

-- atom :: GenParser Char st String
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
-- myelem :: GenParser Char st String
-- myelem :: GenParser Char st Atom
-- myelem = choice [atom, variable]

myelem :: GenParser Char st MyExpr
-- myelem = do { res <- choice [numericexpr,atom, variable]; return res}
myelem = 
       try(numericexpr) <?>
       "A numeric expression inside a fact"

{--
myelem = 
       try(numericexpr) <?>
       "A numeric expression inside a fact"
--}

--myelem' :: GenParser Char st MyExpr
--myelem' = choice [atom, variable]


-- parse args "" "(Foo, Bar, Goo)"
-- parse args "" "(Foo,Bar, Goo)"
-- parse args "" "(Foo,Bar,Goo)"
-- parse args "" "(Foo)"
-- parse args "" "(foo)"
-- parse args "" "(foo,Bar,goo)"
-- parse args "" "( Foo)"
-- parse args "" "" -- this should die, actually
-- parse args "" " ( Foo,Bar )" -- this will die,  XXX 
                                -- because of last space in front of )
-- parse args "" "(1 .. k)"
-- parse args "" "(foo,Bar,5)"
-- parse args "" "(foo,\"Bar\",5)"
-- args :: GenParser Char st [String]
-- args :: GenParser Char st [Atom]
args :: GenParser Char st [MyExpr]
-- args    = do { cs <- between '(' ')' many (noneOf "\n\r\t ()")
--               ; return cs}
-- args    = do { words <- sepBy variable commasep; return words}
-- args    = do { words <- between (char '(') (char ')')
args    = do { words <- between (skipMany1 (space <|> char '(' <|> space ))
                                -- (skipMany1 (space <|> char ')')) 
                                (skipMany1 ( space <|> char ')' <|> space)) 
                   (sepBy myelem (skipMany1 (space <|> char ',')))
                        ; return words}


--                (Name,[Args],Not_negated)
-- data Body = Plain String [String] Bool
-- data Body = Plain Atom [Atom] Bool
data Body = Plain Atom [MyExpr] Bool
--               (Min,Max,Plain, Type, Not_negated)
--               Should be Plain inside, though
          -- | Card Atom Atom [Body] Bool
          | Card MyExpr MyExpr [Body] Bool
          | Count MyExpr MyExpr [Body] Bool
          -- | Typed Body Body -- 26.3. 
          | Typed [Body]
          | Weighed MyExpr Body
          | BExpr BOp MyExpr MyExpr 
          | Assign Atom MyExpr
          | Empty 
            deriving (Show,Eq)

data Rules = Rule Body [Body]
           | Deny [Body]
           | Fact [Body]
           | Show [Body]
           | Hide [Body]
           | Consts [Body]
            deriving (Show)

-- an aggregate to contain negrel, wrel and srel from below
-- parse arel "" "arc(X, Y, L) = L"
arel :: GenParser Char st Body
arel    = 
          try(wrel) <|>
          try(srel) <|>          
          try(negrel) <|>
          try(bexpr) <|>
          try(atomrel)


-- negative relation
-- parse negrel "" "not blub(Foo,Bar,Goo)"
negrel :: GenParser Char st Body
negrel    = do {
            -- skipMany1 (space);
            string "not"; 
            skipMany1 (space)
            ;n <- atom; many space;
            ;myargs <- args
            ;return (Plain n myargs False)}

-- weighed relation
-- parse wrel "" "arc(X, Y, L) = L"
wrel :: GenParser Char st Body
wrel    = do {
            -- we could call here arel, but it blows the stack
            ;n <- atom; many space;
            ;myargs <- args
            ;many space          
            ;string "=" 
            ;many space          
            ;weight <- numericexpr
            ;many space          
            ;return (Weighed weight (Plain n myargs True))}

--
-- simple relation 
-- parse srel "" "blub(Foo,Bar,Goo)"
-- parse srel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)" -- only the 1st one is handled
-- parse srel "" "r, s, not t" -- unexpected ','
-- parse srel "" "color(1 .. k)"
-- Fails on 9.11.2011
-- parse srel "" "blub(Foo,\"Bar\",Goo)"
-- Left (line 1, column 10):
-- unexpected "\""
-- expecting A numeric expression inside a fact

-- A simple relation 
-- srel :: GenParser Char st (String,[String])
srel :: GenParser Char st Body
srel    = do {n <- atom; many space;
            ;myargs <- args
--            ;return (n,myargs)}
            ;return (Plain n myargs True)}

-- parse atomrel "" "blub(Foo,Bar,Goo)"
-- parse atomrel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)" -- only the 1st one is handled
-- parse atomrel "" "r, s, not t" -- unexpected ','
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

-- constrel = do {c <- constdef; return }

-- typed relation 
-- parse trel "" "arc_S(X, Y) : arc(X, Y)"
-- parse trel "" "not arc_S(X, Y) : arc(X, Yo)"
-- parse trel "" "lc(X, Y) : arc(X, Y, L) = L"
-- parse trel "" "not occurs(Y) : vtx(X) : Y < X"
-- parse trel "" "blub(Foo,Bar,Goo)"
-- parse trel "" "f : vtx(Y) : Y < X."
trel :: GenParser Char st Body
trel    = do {one <- arel;
                     -- skipMany1 (space <|> char ':' <|> space ); 
              skipMany1 (space <|> justcolon <|> space ); 
              -- two <- arel;
              -- rest <- (sepBy arel (skipMany1 (space <|> char ':')));              
              rest <- (sepBy arel (skipMany1 (space <|> justcolon)));              
              -- the above forces that there is at least        
              -- two entries for the list of types.       
              return (Typed (one:rest))
             }

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
-- fails sot that no is not detected
-- Where do we allow not?
-- only for facts and atoms, but also inside choices?
-- parse rel "" "arc(X, Y, L) = L"
-- parse rel "" "lc(X,Y) : arc(X, Y, L)"
-- parse rel "" "lc(X,Y) : arc(X, Y, L) = L"
-- parse rel "" "blub(Foo,Bar,Goo)"
-- parse rel "" "blub(Foo,Bar,Goo),chunga(Foo,Bar,Goo)" -- only the 1st one is handled
-- parse rel "" "r, s, not t" -- only the 1st one is handled

rel :: GenParser Char st Body
{--
rel     = try(negrel) <|>
          try(trel) <|>
          try(srel)
--}       
rel     =  try(trel) <|> 
           try(arel) <|>
           try(atomrel) -- must be last 

    

-- lbrace :: mychoice :: GenParser Char st Body
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

-- parse mychoice "" "1 {blub(Foo,Bar,Goo)} 2"
-- parse mychoice "" "M{blub(Foo,Bar,Goo)}"
-- parse mychoice "" "{blub(Foo,Bar,Goo)}"
-- parse mychoice "" "{  sat(C) : clause(C) } k-1" 
-- parse mychoice "" "{ lc(X, Y) : arc(X, Y, L) : mooh(Z) } 1"  
-- parse mychoice "" "1 { p, t }"  -- expects } 
-- parse mychoice "" "{ p, t, not x}" -- does work 
-- parse mychoice "" "{ p, t, not x }" -- does not work
-- parse mychoice "" "1 { p, not t t}"  --- works 
-- Right (Card (Number (Const "1")) (Sym (Const "any")) [Plain (Const "p") [] True,Plain (Const "t") [] False,Plain (Const "t") [] True] True)
-- mychoice :: GenParser Char st (String,[String])
mychoice :: GenParser Char st Body
mychoice    = do { low <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
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
                         -- return (Card "any" "any" content content2 True)}

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
  -- mycount :: GenParser Char st (String,[String])
mycount :: GenParser Char st Body
mycount    = do { low <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
                   content <- 
                   between (skipMany1 (space <|> char '[' <|> space ))
                            -- (skipMany1 (space <|> char ')')) 
                           (skipMany1 ( space <|> char ']' <|> space)) 
                           -- rel; 
                           (sepBy rel (skipMany1 (space <|> char ',')));
--                         return content}
                   high <- option (Sym (Const "any")) numericexpr; -- aggregateconst;
                         return (Count low high content True)}
                         -- return (Card "any" "any" content content2 True)}




-- anumber :: GenParser Char st String
anumber :: GenParser Char st Atom 
anumber    = do 
           {
             low <- many1 digit; many space; return (Const low)
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
    try(do {c <- char '>'; return Gt}) <|>
    try(do {c <- char '<'; return Lt}) <|>
    try(do {c <- char '='; return Eq}) <|>
    try(do {s <- string "<="; return LtEq}) <|> 
    try(do {s <- string ">="; return GtEq}) <|> 
    try(do {s <- string "!="; return Neq}) <|> 
    try(do {s <- string "=="; return Eqeq}) 
           <?> "Expected a comparison operation: >,<,<=,>=,=,=="

-- parse bexpr "" "k > 2"
-- parse bexpr "" "X < Y" -- OK degree-bounded_connected_subgraph.lp
bexpr :: GenParser Char st Body
bexpr = do { 
              a1 <- numeric; 
              skipMany space; 
              o <- mybop;
              skipMany space; 
              a2 <- numeric; 
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
    try(do {s <- string "mod"; return Mod})
           <?> "Expected an arithmetic operation: +,-,*,/,mod"

-- parse nexpr "" "k + 2"
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
-- parse numericexpr "" "1 + 2"
-- parse numericexpr "" "k + 2"
-- parse numericexpr "" "k"
-- parse numericexpr "" "1"
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
-- parse numericexpr "" "k"
-- parse numericexpr "" "1"
numericexpr = 
    try(nexpr) <|>
    try(numeric)
    <?> "A numeric expression"


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
-- parse genrel "" "{ true(A) : atom(A) }" 
-- parse genrel "" "2{i(A,\"wp1:active\",\"yes\"),d(A,\"wp1:active\",\"no\")}2"
-- parse genrel "" "M{\"wp1:commits\"(Cap,A3):\"rdf:type\"(A3,\"wp1:Activity\")}"
-- parse genrel "" "{i(A,\"wp1:active\",\"yes\"),d(A,\"wp1:active\",\"no\")}2"
-- parse genrel "" "{blub(Foo,\"Bar\",Goo)}"
-- parse genrel "" "[ lc(X, Y) : arc(X, Y, L) = L ]" 
-- parse genrel "" "not occurs(Y) : Y < X, vtx(X)" -- vtx should not be parsed 
-- parse genrel "" "f : vtx(Y) : Y < X"

-- genrel :: GenParser Char st (String,[String])
genrel :: GenParser Char st Body
genrel    = 
            try(mychoice) <|>
            try(mycount) <|>
            try(rel) <|> 
            try(bexpr) <|> -- X > Y 
            -- try(mycard1) <|>
            -- try(mycard2) <|>
            -- try(mycard3) <|>
            -- try(mychoice) <|>
            -- This is endlessly ugly, and may be the reason 
            -- we fail silently. 
            -- It is to detect a single atom and wrap 
            -- it with an empty list of arguments. 
           try( do { (r,l) <- atomm; return (Plain r l True) } )
           <?> "relation, choice or simple atom"

-- parse body "" "blub(Foo,Bar,Goo), blab(Baa), bii"
-- parse body "" "blub(Foo,Bar,Goo), blab(Baa), bii"
-- parse body "" "vtx(X), vtx(Y), X < Y, not r(X, Y)"
-- parse body "" "not arc_S(X, Y) : arc(X, Y), vtx(Y)"
-- parse body "" "not arc_S(X, Y) : arc(X, Y)"
-- parse body "" "occurs(X), not occurs(Y) : Y < X, vtx(X)" -- Up until ':'
-- parse body "" "not occurs(Y) : Y < X, vtx(X)" 
-- parse body "" "occurs(X), not occurs(Y) : vtx(X) : Y < X, vtx(X)" 
-- parse body "" "waitingfor(_,_)."
-- body :: GenParser Char st [(String,[String])]
body :: GenParser Char st [Body]
body    = do (sepBy genrel (skipMany1 (space <|> char ',')))

-- parse rule "" "blub(Foo,Bar,Goo) :-  blab(Baa), bii." -- NOK
-- parse rule "" "blub(Foo,Bar,Goo) :-  blab(Baa),\n bii."
-- parse rule "" "ok :- k [ lc(X, Y) : arc(X, Y, L) = L ] ."
-- parse rule "" "initial(X) :- occurs(X), not occurs(Y) : Y < X, vtx(X)." 
-- parse rule "" "{ lc(X, Y) : arc(X, Y, L) } 1 :- vtx(X)." 
-- parse rule "" "ok :- k [ lc(X, Y) : arc(X, Y, L) = L ] ." 
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
             
-- rule :: GenParser Char st ((String,[String]),[(String,[String])])
-- rule :: GenParser Char st (Body,[Body])
rule :: GenParser Char st Rules    
rule    = do { 
               n <- genrel; 
               -- n <-rel; 
               -- (skipMany1 (space <|> string ":-")); 
               -- many space;
               skipMany space;
               string ":-"; 
               -- many space;
               skipMany space;
               b <-body; 
               -- many space; 
               skipMany space; 
               char '.';
               return (Rule n b) }

-- parse deny "" ":-  blab(Baa), bii."
-- parse deny "" ":-  blab(Baa),\n bii."
-- parse deny "" ":- {  sat(C) : clause(C) } k-1."
-- parse deny "" ":- vtx(X), vtx(Y), X < Y, not r(X, Y)."
-- parse deny "" ":- not ok."
-- parse deny "" ":- vtx(X), occurs(X), not r(X)."
-- deny :: GenParser Char st ((String,[String]),[(String,[String])])
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

showf :: GenParser Char st Rules
showf    = do { 
               string "show";
               skipMany1 space; 
               Fact f <- fact;
               return (Show f) }

hidef :: GenParser Char st Rules
hidef    = do { 
               string "hide";
               skipMany1 space; 
               Fact f <- fact;
               return (Hide f) }

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

-- parse showorhide "" "show waitingfor(_,_)."

showorhide :: GenParser Char st Rules
showorhide    = 
              try(showf) <|> 
              try(hidef)


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
ruleorfact = try(rule) <|> 
             fact

threerule = do {
            skipMany space;
            try(showorhide) <|> -- the following have fixed keywords in the beginning
            try(constdef) <|>   -- that's why we can try them 
            deny <|>     -- here we estart with the generic ones, if they all are tried
            ruleorfact   -- the error messages are suppressed 
            -- rule <|>
            -- fact -- <|>
            <?> "rule, denial or fact, ugh"}
 

-- rulebase    = many rule

-- parse rulebase "" "1 { maps_to(X, U) : vtx_H(U) } 1 :- vtx_G(X).\n1 { maps_to(X, U) : vtx_G(X) } 1 :- vtx_G(U).\n :- maps_to(X, U),\n        maps_to(Y, V),\n        arc_G(X, Y),\n        not arc_H(U, V),\n        vtx_H(U),\n        vtx_H(V).\n :- maps_to(X, U),\n        maps_to(Y, V),\n        not arc_G(X, Y),\n        arc_H(U, V),\n        vtx_G(X),\n        vtx_G(Y).\n"
-- parse rulebase "" "1 { maps_to(X, U) } 1 :- vtx_G(X)."

-- parse rulebase "" "ready(A) :- \"rdf:type\"(A,\"wp1:Activity\"), not missing_commit(A)."


--constant :: GenParser Char st String
--constant   = many (noneOf "\n\r\t ()")
       
-- parse tok "" "Foo"
-- parse tok "" "foo"
--tok :: GenParser Char st String
-- tok = choice [atom, variable]

-- parse atom "" "foo"
-- parse atom "" "foo(X,Y)"


-- rule = header >> string ":-" >> body
-- atom = endBy char '.'

-- constant = many (noneOf "\n\r\t ()")
-- variable = many (noneOf "\n\r\t ()")
-- eol = char '\n'

-- The actual call to the parser is in 
-- parse rulebase "" istr 

-- But if we want to have user state, here an empty map, 
-- we need 
-- Note that the "" is the filename that is used for error
-- messages, may be empty as here. 
-- runParser rulebase Map.empty "" istr 

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
