module Symphony.Dynamic.Par.GMW where

import Symphony.Prelude

import Symphony.Dynamic.Par.Error
import Symphony.Dynamic.Par.Send

import Symphony.Dynamic.Par.Types
import Symphony.Lang.Syntax

type Prg = ()

shareSendGmw ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → ClearBaseVal → IM Val ()
shareSendGmw _ρvsFr ρvsTo cbv = do
  prg   ← todoCxt
  chans ← getOrMkChannels ρvsTo
  todoCxt

reshareSendGmw ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → Gmw → IM Val ()
reshareSendGmw _ρvsFr ρvsTo sh = do
  prg   ← todoCxt
  chans ← getOrMkChannels ρvsTo
  todoCxt

shareRecvGmw ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → BaseType → IM Val Gmw
shareRecvGmw ρvsFr ρvsTo bτ = do
  π ← getOrMkSessionGmw ρvsTo
  chansFr ← getOrMkChannels ρvsFr
  todoCxt

reshareRecvGmw ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → BaseType → IM Val Gmw
reshareRecvGmw ρvsFr ρvsTo bτ = do
  π ← getOrMkSessionGmw ρvsTo
  chansFr ← getOrMkChannels ρvsFr
  todoCxt

revealSendGmw ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → Gmw → IM Val ()
revealSendGmw ρvsFr ρvsTo sh = do
  π ← getOrMkSessionGmw ρvsFr
  chansTo ← getOrMkChannels ρvsTo
  todoCxt

revealRecvGmw ∷ (STACK) ⇒ 𝑃 PrinVal → 𝑃 PrinVal → BaseType → IM Val ClearBaseVal
revealRecvGmw ρvsFr ρvsTo bτ = do
  chansFr ← getOrMkChannels ρvsFr
  todoCxt

embedGmw ∷ 𝑃 PrinVal → ClearBaseVal → IM Val Gmw
embedGmw ρvs cbv = do
  π ← getOrMkSessionGmw ρvs
  todoCxt

primGmw ∷ 𝑃 PrinVal → Op → 𝐿 Gmw → IM Val Gmw
primGmw ρvs op sh = do
  π ← getOrMkSessionGmw ρvs
  todoCxt
