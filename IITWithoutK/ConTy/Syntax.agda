module IITWithoutK.ConTy.Syntax where

open import IITWithoutK.Prelude
import IITWithoutK.ConTy.Syntax.Pre as P
import IITWithoutK.ConTy.Syntax.Wf as W

record Con : Type where
  eta-equality
  constructor mkCon
  field
    {pre} : P.Con
    wf : W.Con pre

open Con public

record Ty (Γ : Con) : Type where
  eta-equality
  constructor mkTy
  private
    module Γ = Con Γ

  field
    {pre} : P.Ty
    wf : W.Ty Γ.pre pre

open Ty public

nil : Con
nil = mkCon W.nil

ext : (Γ : Con) → Ty Γ → Con
ext (mkCon Γᵂ) (mkTy Aᵂ) = mkCon (W.ext Γᵂ Aᵂ)

univ : (Γ : Con) → Ty Γ
univ (mkCon Γᵂ) = mkTy (W.univ Γᵂ)

el : (Γ : Con) → Ty (ext Γ (univ Γ))
el (mkCon Γᵂ) = mkTy (W.el Γᵂ)

pi : (Γ : Con) (A : Ty Γ) → Ty (ext Γ A) → Ty Γ
pi (mkCon Γᵂ) (mkTy Aᵂ) (mkTy Bᵂ) = mkTy (W.pi Γᵂ Aᵂ Bᵂ)

heightCon : Con → ℕ
heightCon Γ = P.heightCon (Γ .pre)

heightTy : ∀ {Γ} → Ty Γ → ℕ
heightTy A = P.heightTy (A .pre)

lboundCon : (Γ : Con) → 1 ≤ heightCon Γ
lboundCon Γ = W.lboundCon (Γ .wf)

lboundTy : ∀ {Γ} (A : Ty Γ) → 1 + heightCon Γ ≤ heightTy A
lboundTy A = W.lboundTy (A .wf)
