module PSL where

import UVMHS
import AddToUVMHS

import PSL.Interpreter

main ∷ IO ()
main = interpreterMain

mainDefaultArgs ∷ 𝐿 𝕊
mainDefaultArgs = 
  list ["test","--version","--help"]
  -- list ["example","qsort"]

mainDefault ∷ IO ()
mainDefault = localArgs mainDefaultArgs  interpreterMain
