module Allyn.Interpreter.Pretty where

import UVMHS

levelIF,levelLAM,levelLET,levelPAR,levelUPDATE ∷ ℕ64
levelIF     = 𝕟64 10
levelLAM    = 𝕟64 10
levelLET    = 𝕟64 10
levelPAR    = 𝕟64 10
levelUPDATE = 𝕟64 15

levelCOMMA,levelASCR,levelCONS,levelREVEAL ∷ ℕ64

levelCOMMA   = 𝕟64 20
levelASCR    = 𝕟64 21
levelCONS    = 𝕟64 22
levelREVEAL  = 𝕟64 25

levelCOND,levelCOMPARE,levelARROW,levelPLUS,levelTIMES,levelEXP ∷ ℕ64
levelCOND    = 𝕟64 30
levelCOMPARE = 𝕟64 35
levelARROW   = 𝕟64 40
levelPLUS    = 𝕟64 50
levelTIMES   = 𝕟64 60
levelEXP     = 𝕟64 70

levelAPP ∷ ℕ64
levelAPP = 𝕟64 100

levelDEREF ∷ ℕ64
levelDEREF = 𝕟64 120

levelACCESS ∷ ℕ64
levelACCESS = 𝕟64 130

levelMODE ∷ ℕ64
levelMODE  = 𝕟64 200

ppPreF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc
ppPreF f i oM xM = ppGA $ ppLevel i $ f $ map ppAlign $ iter [oM,xM]

ppPostF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc
ppPostF f i oM xM = ppGA $ ppLevel i $ f $ map ppAlign $ iter [xM,oM]

ppInflF ∷ (𝐼 Doc → Doc) → ℕ64 → Doc → Doc → Doc → Doc
ppInflF f i oM x₁M x₂M = ppGA $ ppLevel i $ f $ map ppAlign $ iter [x₁M,oM,ppBump x₂M]

ppTight ∷ (ToIter Doc t) ⇒ t → Doc
ppTight = ppGroup ∘ concat ∘ inbetween ppNewlineIfBreak ∘ iter
