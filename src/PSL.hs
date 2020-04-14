module PSL where

import UVMHS

import PSL.Interpreter

mainDefaultArgs ∷ 𝐿 𝕊
mainDefaultArgs = 
  -- list ["test","--version","--help"]
  list ["example","db-stats"]

main ∷ IO ()
main = do
  initUVMHS
  interpreterMain

mainDefault ∷ IO ()
mainDefault = do
  initUVMHS
  ilocalArgs mainDefaultArgs  interpreterMain
