open import IITWithoutK.Prelude

module IITWithoutK.OpenExample.Initial (X : Type) where

open import IITWithoutK.OpenExample.Algebra X
import IITWithoutK.OpenExample.Initial.Indexed X as H

record Con : Type where
  eta-equality
  constructor mkCon
  field
    {height} : ℕ
    {lbound} : 1 ≤ height
    value : H.Con height lbound

open Con public

record Ty (Γ : Con) : Type where
  eta-equality
  constructor mkTy
  private
    module Γ = Con Γ

  field
    {height} : ℕ
    {lbound} : 1 + Γ.height ≤ height
    value : H.Ty height lbound Γ.value

open Ty public

inc : X → Con
inc x = mkCon (H.inc x)

ext : (Γ : Con) → Ty Γ → Con
ext (mkCon Γ) (mkTy A) = mkCon (H.ext Γ A)

base : (Γ : Con) → Ty Γ
base (mkCon Γ) = mkTy (H.base Γ)

Init : Alg
Init .Alg.Con = Con
Init .Alg.Ty = Ty

Init .Alg.inc = inc
Init .Alg.ext = ext
Init .Alg.base = base
