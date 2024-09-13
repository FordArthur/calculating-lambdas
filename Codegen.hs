{-# LANGUAGE TemplateHaskell #-}
module Codegen where

import Debug.Trace
import Control.Lens
import Control.Monad.State

import Parser
import Typechecker
import Control.Arrow

data Site = 
    RAX | RBX | RCX | RDX
  | RSP | RBP | RSI | RDI
  | R8  | R9  | R10 | R11 | R12 | R13 | R14 | R15
  | XMM0 | XMM1
  | XMM2 | XMM3 | XMM4  | XMM5  | XMM6  | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15
  | StackOffset Int
  deriving (Eq, Show)

emitSite :: Site -> String
emitSite (StackOffset n) = "[RBP - " ++ show n ++ "]"
emitSite r               = show r
  
  -- SystemV abi: RDI , RSI , RDX , RCX , R8 , R9
data CallingConvention = CallingConvention { _retReg :: Site, _freeCallSites :: [Site], _reservedCallSites :: [Site], _freeTempSites :: [Site], _reservedTempSites :: [Site] }
makeLenses ''CallingConvention

type RBPValue = Int

data Emit a = Emit { _machineState :: CallingConvention, _emitted :: a }
makeLenses ''Emit

emitFront :: Monoid a => a -> State (Emit a) ()
emitFront a = modify $ emitted `over` (a <>)

emit :: Monoid a => a -> State (Emit a) ()
emit a = modify $ emitted `over` (<> a)

allocSite :: Bool -> State (Emit a) Site
allocSite isTemp = do
  let (freeSites, reservedSites, _freeSites) = if isTemp then (freeTempSites, reservedTempSites, _freeTempSites) else (freeCallSites, reservedCallSites, _freeCallSites)
  freeSite' <- gets $ head . _freeSites . _machineState
  modify $ (machineState . freeSites) `over` alloc
  modify $ (machineState . reservedSites) `over` (freeSite' :)
  return freeSite'
  where alloc ((StackOffset n):xs) = StackOffset (n - 8) : xs
        alloc (_:xs)               = xs
        alloc _                    = undefined

freeSite :: (Eq a) => Site -> State (Emit a) ()
freeSite site = do
  isTemp <- gets $ elem site . _reservedTempSites . _machineState
  let (freeSites, reservedSites, _freeSites) = if isTemp then (freeTempSites, reservedTempSites, _freeTempSites) else (freeCallSites, reservedCallSites, _freeCallSites)
  modify $ (machineState . freeSites) `over` (site :)
  modify $ (machineState . reservedSites) `over` init

genExpr :: LambdaExpressionIndexedBy DeBrujin MonoType -> State (Emit [String]) Site

genExpr (Cnst c t) = do
  site <- allocSite True
  emit [ "mov " ++ emitSite site ++ ", " ++ numericConst ]
  return site
  where
    numericConst = case t of
      Nat -> c

genExpr (Var (BIndex i _)) = gets $ traceShowId . (!! i) . reverse . _reservedCallSites . _machineState

genExpr (Var (BFunc n _)) = do
  site <- allocSite True
  retReg' <- gets $ _retReg . _machineState
  emit [ 
      "call " ++ n,
      "mov " ++ show site ++ ", " ++ show retReg'
    ]
  return site

genExpr (Application e1 e2) = do
  arg' <- allocSite False
  argRes' <- genExpr e2
  emit [ "mov " ++ show arg' ++ ", " ++ show argRes' ]
  freeSite argRes'
  genExpr e1

genExpr (Abstraction _ e) = genExpr e

genExpr (LocalBind _ v e) = do
  varRes' <- genExpr v
  var' <- allocSite False
  emit [ "mov " ++ show var' ++ ", " ++ show varRes' ]
  genExpr e

genExpr _  = undefined

codegen :: LambdaExpressionIndexedBy DeBrujin MonoType -> [String]
codegen code = 
  let (lastSite, emitted') = second _emitted $ runState (genExpr code) systemVAbi
  in boilerplate ++ emitted' ++ [ "mov RDI, " ++ emitSite lastSite ] ++ exit
  where 
    systemVAbi = Emit (CallingConvention RAX [RDI, RSI, RDX, RCX, R8, R9, StackOffset 0] [] [RBX, R10, R11, R12, R13, R14, R15] []) []
    prelude = [ -- !! Asumes systemVAbi !!
        "plus:",
          "add RDI, RSI",
          "mov RAX, RDI",
          "ret"
      ]
    boilerplate = [ "[bits 64]", "section .text", "global _start" ] ++ prelude ++  [ "_start:" ]
    exit = [
        "mov RAX, 60",
        "syscall"
      ]
