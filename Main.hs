module Main where

-- Grzegorz B. Zaleski (418494) --

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Reader
import System.IO          ( hPutStrLn, stderr )
import System.Environment ( getArgs, getProgName )
import System.Exit        ( exitFailure, exitSuccess )
import System.Process     ( system )
import Data.List          ( isSuffixOf )

import qualified Latte.Abs as L
import Latte.Lex    ( Token )
import Latte.Par    ( pProgram, myLexer )
import Latte.Print  ( Print, printTree )
import TypeChecker  ( runTypeCheck )
import Compiler     ( runCompiler )
import ASTOpti      ( optimiseProgramme )

getFilePath :: String -> String
getFilePath fs = take (length fs - 4) fs -- 4 for ".lat"

runFile :: FilePath -> IO ()
runFile fs = readFile fs >>= runProgram (getFilePath fs)

runProgram :: String -> String -> IO ()
runProgram filepath s = case pProgram tokenised of
    Left parseError -> do
      hPutStrLn stderr "ERROR"
      hPutStrLn stderr $ "Programme parsing failure!\n" ++ parseError
      exitFailure
    Right programmeTree -> do
      let staticAnalysisResult = runTypeCheck programmeTree
      case staticAnalysisResult of
        Left staticError -> do
          hPutStrLn stderr "ERROR"
          hPutStrLn stderr $ "Frontend analysis failure!\n" ++ staticError
          exitFailure
        Right _ -> do 
          hPutStrLn stderr "OK"
          putStr "Fronted analysis passed!\n"
          code <- runCompiler $ optimiseProgramme programmeTree

          writeFile (filepath ++ ".ll") code
          _ <- system $ "llvm-as -o temporary.bc " ++ filepath ++ ".ll"
          _ <- system $ "llvm-link -o " ++ filepath ++ ".bc temporary.bc lib/runtime.bc"
          _ <- system $ "rm temporary.bc"

          return ()
  where
    tokenised = myLexer s

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> error "Latte file not provided!"
    fs | all (isSuffixOf ".lat") fs -> mapM_ runFile fs
    _ -> error "Wrong file format!"