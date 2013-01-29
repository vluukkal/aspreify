--
-- Main file for aspparse. 
-- 
-- To compile:
-- > ghc -o aspreify main.hs factrender.hs rdfrender.hs txtrender.hs aspparse.hs 
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

import System.Environment (getArgs)
import System.Directory (removeFile)

import qualified Data.List as List
import Text.ParserCombinators.Parsec

import System.IO
import Data.Text
import Data.Text.IO
import qualified Data.Text.Encoding as E
import qualified Data.Text.Encoding.Error as Err
import qualified Data.ByteString as B

import System.Console.GetOpt
import System.Exit
import System.Environment

import Control.Monad

import AspParse
import FactRender
import TxtRender
import RdfRender
import DeReify

parsenrender :: String -> ((Either ParseError [Rules]) -> String) -> IO String
parsenrender fname renderer = 
    do {
      -- istr <- Data.Text.IO.readFile fname; 
      istr <- B.readFile fname; 
      let tree = parse rulebase "" (unpack (E.decodeUtf8With Err.lenientDecode istr)) in 
      let output = renderer tree in 
      return (show output)
    }

justparse fname = 
    do {
      istr <- B.readFile fname; 
      let tree = parse rulebase "" (removecomm (unpack (E.decodeUtf8With Err.lenientDecode istr))) in 
      return tree
    }

removecomm :: String -> String 
removecomm s = 
  List.unlines (List.reverse(List.foldl precomment [] (List.lines s)))
  where 
    precomment accu l = 
      if l == ""
      then "\n":accu 
      else
        case List.elemIndex '%' l of
          Just idx -> (List.take idx l):accu
          Nothing -> l:accu 

-- parsenrendernwrite "test2.lp" "mooh.lp" txtrender
-- parsenrendernwrite "test2.lp" "mooh.lp" rdfrender
-- parsenrendernwrite "maxsat_preproc.lp" "mooh.lp" txtrender
-- parsenrendernwrite "maxsat.lp" "mooh.lp" txtrender
parsenrendernwrite fname fname2 renderer = 
    do 
      -- istr <- Data.Text.IO.readFile fname
      istr <- B.readFile fname
      -- let tree = parse rulebase "" istr 
      -- let output = renderer tree 
      let ppstr = removecomm (unpack (E.decodeUtf8With Err.lenientDecode istr)) -- an ugly hack to remove the comments before parsing 
      let output = pack(renderer (parse rulebase "" ppstr ))
      outh <- openFile fname2 WriteMode
      Data.Text.IO.hPutStr outh output 
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
      -- inpstr <- Data.Text.IO.readFile fn2 
      inpstr <- B.readFile fn2 
      Data.Text.IO.writeFile fn3 (pack (prefix ++ (List.unlines(List.map ((++) lineprefix) (List.lines (unpack (E.decodeUtf8With Err.lenientDecode inpstr))))) ++ postfix))
    
backtolp fn1 fn2 =
    do 
      parsenrendernwrite fn1 fn2 txtrender

reify fn1 fn2 params =
    do 
      parsenrendernwrite fn1 fn2 (factrender ("% Inputfile: " ++ fn1 ++ "\n") params)

undoreify fn1 fn2 ground =
    do 
      parsenrendernwrite fn1 fn2 (dereify ground)

undoreify' fn1 fn2 baserls basehs =
    do 
      parsenrendernwrite fn1 fn2 (dereifywithbase baserls basehs)


data Flag
    = Lparse                -- -l (default)
    | Rdf                   -- -r
    | Test                  -- -t
    | Idreuse               -- -i
    | Dereify               -- -d 
    | Ground                -- -g
    | Base String           -- -b the basefilename for grounding 
    | Help                  -- --help
    -- deriving (Eq,Ord,Enum,Show,Bounded)
    deriving (Eq,Ord,Show)

flags =
   [Option ['l'] []       (NoArg Lparse)
        "Produces reified facts in ASP format (default)."
   ,Option ['r'] []       (NoArg Rdf)
        "Produces reified facts in RDF/N3 compatible format."
   ,Option ['t'] []       (NoArg Test)
        "Renders the parsetree back to text, useful for testing."
   ,Option ['i'] []       (NoArg Idreuse)
        "Assigns the same identifier for same variable in one rule."
   ,Option ['d'] []       (NoArg Dereify)
        "Reads in a reified set of facts and constructs reconstructs nonreified ruleset."
   ,Option ['g'] []       (NoArg Ground)
        "Reads in a reified set of facts along with variable assignments and performs related grounding."
   ,Option ['b'] []       (ReqArg Base "BASE") -- (NoArg Ground)
        "Reads in a reified set of facts along with variable assignments and performs related grounding."
   ,Option []    ["help"] (NoArg Help)
        "Print this help message"
   ]

parseopts argv = 
   case getOpt Permute flags argv of
   (args,fs,[]) -> do
        let files = if List.null fs then ["-"] else fs
        if Help `elem` args
            then do System.IO.hPutStrLn stderr (usageInfo header flags)
                    exitWith ExitSuccess
            else return (List.nub (List.concatMap set args), files)
   (_,_,errs)      -> do
        System.IO.hPutStrLn stderr (List.concat errs ++ usageInfo header flags)
        exitWith (ExitFailure 1)
   where header = "Usage: aspparse [-l|r|t|d|g|b] [file ...]"
         set Lparse      = [Lparse] 
         set Rdf      = [Rdf] 
         set Test      = [Test] 
         set Dereify      = [Dereify] 
         set Ground      = [Ground] 
         set (Base s)     = [Base s] 
         set f      = [f] 

handleafile otype other baserules basehs f = 
 case otype of 
 [Rdf] -> do 
       let tmpfname = (f ++ ".tmp") 
       let outfile = (f ++ ".ssls") 
       -- putStrLn ("tossls " ++ show(f) ++ " " ++ show(tmpfname) ++ " " ++ show(outfile))
       tossls f tmpfname outfile 
       -- return ""
 [Test] -> do
       let loopbackfile = (f ++ ".lp") 
       -- putStrLn ("backtolp " ++ show(f) ++ " " ++ show(loopbackfile))
       backtolp f loopbackfile
       -- return ""
 [Dereify] -> do 
      let dereifiedfile = (f ++ ".dereified") 
      undoreify f dereifiedfile False
      -- return ""
 [Ground] -> do 
      let dereifiedfile = (f ++ ".ground") 
      undoreify f dereifiedfile True
      -- return ""
 [Base s] -> do 
      let dereifiedfile = (f ++ ".ground") 
      undoreify' f dereifiedfile baserules basehs
      -- return ""
 _ -> do -- default is [Lparse]
      let reifiedfile = (f ++ ".reified") 
      -- putStrLn ("reify " ++ show(f) ++ " " ++ show(reifiedfile))
      let mkid = (List.elem Idreuse other)
      reify f reifiedfile mkid
      -- return ""

-- handleafile' :: [Flag] -> [Flag] -> (Bool, IO [t], t1) -> [Char] -> IO (t, t1)
-- There's an emptyset in 2nd elemnt of the triple, but as it is a 
-- IO Rules and we should be able to look inside IO to compare. 
-- Blargh, as a kludge we have a dedicated boolean element. 
handleafile' otype other (d,rls,hs) f = 
 do
   System.IO.hPutStrLn stderr ("BOO")
   case otype of 
    [Rdf] -> do 
       let tmpfname = (f ++ ".tmp") 
       let outfile = (f ++ ".ssls") 
       -- putStrLn ("tossls " ++ show(f) ++ " " ++ show(tmpfname) ++ " " ++ show(outfile))
       tossls f tmpfname outfile 
       return (d,rls,hs)
    [Test] -> do
       let loopbackfile = (f ++ ".lp") 
       -- putStrLn ("backtolp " ++ show(f) ++ " " ++ show(loopbackfile))
       backtolp f loopbackfile
       return (d,rls,hs)
    [Dereify] -> do 
      let dereifiedfile = (f ++ ".dereified") 
      undoreify f dereifiedfile False
      return (d,rls,hs)
    [Ground] -> do 
      let dereifiedfile = (f ++ ".ground") 
      undoreify f dereifiedfile True
      return (d,rls,hs)
    [Base s] -> do 
      let basefilename = List.head(List.words s)
      let baseparse = (justparse basefilename) 
      let (d,rls,hs) = if d then (d,rls,hs) 
                       else (True, (justparse basefilename), hs)
      -- rls::IO (Either ParseError [Rules])
      System.IO.hPutStrLn stderr ("Using " ++ s ++ " as base")
      -- let dereifiedfile = (s ++ ".ground") 
      let dereifiedfile = (basefilename ++ ".ground") 
      -- undoreify' f dereifiedfile True
      undoreify s f True
      return (d,rls,hs)
    _ -> do -- default is [Lparse]
      System.IO.hPutStrLn stderr ("Doing " ++ show(otype))
      let reifiedfile = (f ++ ".reified") 
      -- putStrLn ("reify " ++ show(f) ++ " " ++ show(reifiedfile))
      let mkid = (List.elem Idreuse other)
      reify f reifiedfile mkid
      return (d,rls,hs)

-- Should be as where underneath
isbase x = 
   case x of 
        Base s -> True
        _ -> False

-- Urgh, parseopts should be able to do this 
-- Separate between arguments for output type
separateargs args = 
  List.partition onlytypes args
  where onlytypes x | x == Rdf = True
                    | x == Lparse = True 
                    | x == Test = True
                    | x == Dereify = True
                    | x == Ground = True
                    | isbase x = True
                    | otherwise = False  

-- There must a better way of doing this without a function 
-- mkio :: Monad m => a -> m a
mkio i = 
     do 
        return i

groundbase :: [[Flag]] -> IO ([Rules], IntermediateR)
groundbase flags = 
     case flags of 
        h:rest -> do 
               (rls,hs) <- dobase h
               if rls == [] then (groundbase rest) else return (rls,hs)
        [] -> do 
               return ([],(DeReify.emptyIntermediate True))
{--
     -- : IO ([Rules], IntermediateR) -> IO ([Rules], IntermediateR)
     let a = List.foldr dobase files [] in 
     -- let a = List.foldl dobase files [] in  -- wont work?
       a
--}

-- We do two things; firstly, create the internal representation 
-- of the rules, the parsetree and mapping of IDs to elements.
-- Secondly, we dereify the basefile to rules. The former are used
-- as cache to avoid rereading the same rules for each answer set,
-- the latter is used as prefix when concatenating all results 
-- together. 
-- The the flag is not the basefile, nothing is done, we return 
-- empty rules and empty internal mappings. 
dobase :: [Flag] -> IO ([Rules], IntermediateR)
dobase i  = 
     case i of 
       [Base s] -> do 
                  let basefilename = List.head(List.words s)
                  baseparse <- (justparse basefilename) 
                  -- Next we dereify this parsed file 
                  let (rls,hs) = DeReify.basedreify True baseparse 
                  System.IO.hPutStrLn stderr ("Using " ++ s ++ " as base")
                  undoreify s (s ++ ".ground") True
                  {--
                  System.IO.hPutStrLn stderr (show(baseparse))
                  System.IO.hPutStrLn stderr ("-------------------------------------")
                  System.IO.hPutStrLn stderr (show(rls))
                  System.IO.hPutStrLn stderr ("-------------------------------------")
                  System.IO.hPutStrLn stderr (show(hs))
                  System.IO.hPutStrLn stderr ("-------------------------------------")
                  --}
                  return (rls,hs)
       otherwise -> return ([],(DeReify.emptyIntermediate True))

-- debugbase "/Users/vluukkal/src/aspreify/metaeval/hamilton/01212013_100859/output/tlist.lp.reified" "/Users/vluukkal/src/aspreify/metaeval/hamilton/01212013_100859/output/smres1.lp" 

-- debugbase "/Users/vluukkal/src/aspreify/metaeval/hamilton/01232013_225648/output/tlist.lp.reified" "/Users/vluukkal/src/aspreify/metaeval/hamilton/01232013_225648/output/smres1.lp" 

-- dereifywithbase = parsenrendernwrite fn1 fn2 (dereifywithbase baserls basehs)
debugbase basefile cfile = 
    do 
       baseparse <- (justparse basefile) 
       -- Next we dereify this parsed file 
       let (rls,hs) = DeReify.basedreify True baseparse 
       -- Now we do the actual dereify with the other file 
       cfileparse <- (justparse cfile) 
       -- Next we dereify this parsed file 
       let (rls2,hs2) = DeReify.basedreify True cfileparse 
       return (dereifywithbase' rls hs2 (Right rls2))

       
main = 
    do 
      (args,files) <- getArgs >>= parseopts
      let (outputtype,other) = separateargs args 
      -- System.IO.putStrLn ((show outputtype) ++ "," ++ (show other))
      -- The exclusivity must be somewhere in getopt though 
      if List.length outputtype > 1 
      then do System.IO.hPutStrLn stderr ("Only one output type permitted\n" ++ (usageInfo header flags))
              exitWith (ExitFailure 1)
      {-- --} 
      else do 
              -- System.IO.hPutStrLn stderr ("main: " ++ show(outputtype) ++ " : " ++ show(other) ++ " : " ++ show(files))
              (baserules,basehs) <- dobase outputtype
              mapM_ (handleafile outputtype other baserules basehs) files 
              exitWith ExitSuccess
       {-- --}
       {--
      else do 
              System.IO.hPutStrLn stderr ("main: " ++ show(outputtype) ++ " : " ++ show(other) ++ " : " ++ show(files))
              -- let (baserls,basehs,files) = groundbase files in 
              -- foldM_ (handleafile' outputtype other) ([],(DeReify.emptyIntermediate True)) files 
              -- (baserules,basehs) <- groundbase outputtype
              (baserules,basehs) <- dobase outputtype
              foldM_ (handleafile' outputtype other) (False, (mkio (Right [])),(mkio (DeReify.emptyIntermediate True))::IO DeReify.IntermediateR) files 
              -- foldM_ (handleafile' outputtype other) (False, (mkio ((Right [])),(DeReify.emptyIntermediate True))) files 
              exitWith ExitSuccess
         --}
      {--
         -- This does not work, but why?
         -- Do we need still to 'evaluate' all in the end?
      else do 
              let all = mapM (handleafile outputtype other) files 
              exitWith ExitSuccess
      --}
      where header = "Usage: aspparse [-l|r|t|d|g] [file ...]"
