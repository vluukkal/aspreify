--
-- Main file for aspparse. 
-- 
-- To compile:
-- > ghc -o aspreify main.hs factrender.hs aspparse.hs 
-- To test 
-- > ./aspreify tests/hamiltonian_cycle.lp
-- The result is 
-- tests/hamiltonian_cycle.lp.reified 
-- 
-- > ./aspreify -t tests/hamiltonian_cycle.lp
-- The result is 
-- tests/hamiltonian_cycle.lp.lp
-- 
-- > ./aspreify -r tests/hamiltonian_cycle.lp
-- The result is 
-- tests/hamiltonian_cycle.lp.ssls
-- 
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

import System.Environment (getArgs)
import System.Directory (removeFile)

import qualified Data.List as List
import Text.ParserCombinators.Parsec
import System.IO

import System.Console.GetOpt
import System.Exit
import System.Environment

import Control.Monad

import AspParse
import FactRender
import TxtRender
import RdfRender

parsenrender :: String -> ((Either ParseError [Rules]) -> String) -> IO String
parsenrender fname renderer = 
    do {
      istr <- readFile fname; 
      let tree = parse rulebase "" istr in 
      let output = renderer tree in 
      return (show output)
    }

removecomm :: String -> String 
removecomm s = 
  unlines (reverse(List.foldl precomment [] (lines s)))
  where 
    precomment accu l = 
      if l == ""
      then accu 
      else
        case List.elemIndex '%' l of
          Just idx -> (take idx l):accu
          Nothing -> l:accu 

-- parsenrendernwrite "test2.lp" "mooh.lp" txtrender
-- parsenrendernwrite "test2.lp" "mooh.lp" rdfrender
-- parsenrendernwrite "maxsat_preproc.lp" "mooh.lp" txtrender
-- parsenrendernwrite "maxsat.lp" "mooh.lp" txtrender
parsenrendernwrite fname fname2 renderer = 
    do 
      istr <- readFile fname
      -- let tree = parse rulebase "" istr 
      -- let output = renderer tree 
      let ppstr = removecomm istr -- an ugly hack to remove the comments before parsing 
      let output = renderer (parse rulebase "" ppstr )
      outh <- openFile fname2 WriteMode
      hPutStr outh output 
      hClose outh

-- tossls "test4.lp" "mooh4.lp" "mooh4.ssls"
tossls fn1 fn2 fn3 =
    do 
      let prefix = "ssls $Revision: 1.12 $\nb---\n"
      let lineprefix = "1:a: i "
      let postfix = "2:a: update\ne---\n"
      parsenrendernwrite fn1 fn2 rdfrender
      -- parsenrendernwrite fn1 fn2 (rdfrulerender fn1) -- 9.11.2011

      -- Now read in the text and construct the 
      -- the ssls string. 
      inpstr <- readFile fn2 
      writeFile fn3 (prefix ++ (unlines(List.map ((++) lineprefix) (lines inpstr))) ++ postfix)
    
backtolp fn1 fn2 =
    do 
      parsenrendernwrite fn1 fn2 txtrender

reify fn1 fn2 =
    do 
      parsenrendernwrite fn1 fn2 (factrender ("% Inputfile: " ++ fn1 ++ "\n"))

data Flag
    = Lparse                -- -l (default)
    | Rdf                   -- -r
    | Test                  -- -t
    | Help                  -- --help
    deriving (Eq,Ord,Enum,Show,Bounded)

flags =
   [Option ['l'] []       (NoArg Lparse)
        "Produces reified facts in ASP format (default)."
   ,Option ['r'] []       (NoArg Rdf)
        "Produces reified facts in RDF/N3 compatible format."
   ,Option ['t'] []       (NoArg Test)
        "Renders the parsetree back to text, useful for testing."
   ,Option []    ["help"] (NoArg Help)
        "Print this help message"
   ]

parseopts argv = 
   case getOpt Permute flags argv of
   (args,fs,[]) -> do
        let files = if null fs then ["-"] else fs
        if Help `elem` args
            then do hPutStrLn stderr (usageInfo header flags)
                    exitWith ExitSuccess
            else return (List.nub (concatMap set args), files)
   (_,_,errs)      -> do
        hPutStrLn stderr (concat errs ++ usageInfo header flags)
        exitWith (ExitFailure 1)
   where header = "Usage: aspparse [-l|r|t] [file ...]"
         set Lparse      = [Lparse] 
         set Rdf      = [Rdf] 
         set Test      = [Test] 
         set f      = [f] 

handleafile args f = 
 case args of 
 [Rdf] -> do 
       let tmpfname = (f ++ ".tmp") 
       let outfile = (f ++ ".ssls") 
       putStrLn ("tossls " ++ show(f) ++ " " ++ show(tmpfname) ++ " " ++ show(outfile))
       tossls f tmpfname outfile 
 [Test] -> do
       let loopbackfile = (f ++ ".lp") 
       putStrLn ("backtolp " ++ show(f) ++ " " ++ show(loopbackfile))
       backtolp f loopbackfile
 _ -> do -- default is [Lparse]
      let reifiedfile = (f ++ ".reified") 
      putStrLn ("reify " ++ show(f) ++ " " ++ show(reifiedfile))
      reify f reifiedfile 

main = 
    do 
      (args,files) <- getArgs >>= parseopts
      -- The exclusivity must be somewhere in getopt though 
      if length args > 1 
      then do hPutStrLn stderr ("Only one option permitted\n" ++ (usageInfo header flags))
              exitWith (ExitFailure 1)
      else do mapM_ (handleafile args) files 
              exitWith ExitSuccess

      where header = "Usage: aspparse [-l|r|t] [file ...]"
