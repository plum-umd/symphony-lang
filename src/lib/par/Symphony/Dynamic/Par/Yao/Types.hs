module Symphony.Dynamic.Par.Yao.Types where

import Symphony.Prelude

import Foreign.ForeignPtr

type CYao   = ()
newtype Yao = Yao { unYao ∷ ForeignPtr CYao }

type CYaoBool   = ()
newtype YaoBool = YaoBool { unYaoBool ∷ ForeignPtr CYaoBool }

type CYaoNat   = ()
newtype YaoNat = YaoNat { unYaoNat ∷ ForeignPtr CYaoNat }

type CYaoInt   = ()
newtype YaoInt = YaoInt { unYaoInt ∷ ForeignPtr CYaoInt }
