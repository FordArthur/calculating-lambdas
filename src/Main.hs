module Main where

import Control.Monad

import System.IO
import System.Process
import System.Exit
import System.Environment

import Parser
import Typechecker
import Codegen

repl :: IO ()
repl = do
  putStr "λ< "
  hFlush stdout
  input <- getLine
  case parseExpression input of
    (Right p) -> case typecheck p of
      (Right t) -> putStr "δ> " >> putStrLn (unlines $ "" : codegen t)
      (Left e)  -> putStr "σ!> " >> print e
    (Left e)  -> putStr "λ!> " >> print e
  main

compile :: FilePath -> FilePath -> IO ()
compile input output = do
  inputFile <- readFile input
  p' <- exitIfError $ parseExpression inputFile
  t' <- exitIfError $ typecheck p'
  let c' = unlines $ codegen t'
  writeFile (output ++ ".s") c'
  objPhase <- system $ "nasm -f elf64 " ++ output ++ ".s -o " ++ output ++ ".o"
  when (objPhase == ExitSuccess) $ void $ system $ "ld -o " ++ output ++ " " ++ output ++ ".o"
  where
    exitIfError (Right x) = return x
    exitIfError (Left e)  = print e >> exitFailure

main :: IO ()
main = do
  flags <- getArgs
  case flags of
    ["repl"]       -> repl
    [iFile, oFile] -> compile iFile oFile
    _              -> putStrLn "Usage: repl | [input] [output]" >> exitFailure
