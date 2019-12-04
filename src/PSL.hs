module PSL where

import UVMHS

import PSL.Interpreter
import PSL.TypeChecker

main ∷ IO ()
main = do
  testTypeChecker
  testInterpreter
