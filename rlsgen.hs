--
-- Quickcheck based generator for pseudorandom rules according 
-- to the definitions in AspParse.
-- 
-- Create an executable
-- > ghc -o rlsgen rlsgen.hs aspparse.hs txtrender.hs 
-- > ./rlsgen 2 10 
-- 
-- Or in the interpreter:
-- ghci> :l testaspparse.hs 
-- ghci> runTestTT tests
-- 
-- 
-- Copyright 2014 Vesa Luukkala
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

import System.IO
import System.Environment (getArgs)
import qualified Data.List as List
import System.Console.GetOpt
import System.Exit
import Data.Text
import Data.Text.IO

import qualified Control.Exception as Ex


import Qcaspparse
import TxtRender
import AspParse 

-- Needed just to get the ParseError for Either ... 
import Text.ParserCombinators.Parsec

createrls :: Int -> Int -> [Char]
createrls seed len = 
   let rls = Qcaspparse.mkrls seed len in 
       TxtRender.txtrender ((Right rls) :: Either ParseError [Rules])

-- For getopts 
data Flag
    = 
    Help                  -- --help
    -- deriving (Eq,Ord,Enum,Show,Bounded)
    deriving (Eq,Ord,Show)

flags = []

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
   where header = "Usage: rlsgen seed len"
         set f      = [f] 

main = 
     do 
        (args,nums) <- getArgs >>= parseopts
        let txt = createrls (read (nums!!0)) (read (nums!!1))
        Data.Text.IO.hPutStr stdout (Data.Text.pack txt)
