module IITWithoutK.ConTy.Syntax.Wf where

open import IITWithoutK.Prelude
import IITWithoutK.ConTy.Syntax.Pre as P

data Con : P.Con → Type
data Ty : P.Con → P.Ty → Type

data Con where
  nil : Con P.nil
  ext : ∀ {Γ} → Con Γ → ∀ {A} → Ty Γ A → Con (P.ext Γ A)

data Ty where
  univ : ∀ {Γ} → Con Γ → Ty Γ (P.univ Γ)
  el : ∀ {Γ} → Con Γ → Ty (P.ext Γ (P.univ Γ)) (P.el Γ)
  pi :
    ∀ {Γ} → Con Γ → ∀ {A} → Ty Γ A → ∀ {B} → Ty (P.ext Γ A) B →
    Ty Γ (P.pi Γ A B)

Ty→Con : ∀ {Γ A} → Ty Γ A → Con Γ
Ty→Con (univ Γᵂ) = Γᵂ
Ty→Con (el Γᵂ) = ext Γᵂ (univ Γᵂ)
Ty→Con (pi Γᵂ Aᵂ Bᵂ) = Γᵂ

lboundCon : ∀ {Γ} → Con Γ → 1 ≤ P.heightCon Γ
lboundTy : ∀ {Γ A} → Ty Γ A → 1 + P.heightCon Γ ≤ P.heightTy A

lboundCon nil = ≤-refl
lboundCon (ext Γᵂ Aᵂ) = lboundCon Γᵂ ◂ ≤-step ◂ lboundTy Aᵂ ◂ ≤-step

lboundTy (univ Γᵂ) = ≤-refl
lboundTy (el Γᵂ) = ≤-refl
lboundTy (pi Γᵂ Aᵂ Bᵂ) = lboundTy Aᵂ ◂ ≤-steps 2 ◂ lboundTy Bᵂ ◂ ≤-step

opaque
  isPropCon : ∀ {Γ} → isProp (Con Γ)
  isPropTy : ∀ {Γ A} → isProp (Ty Γ A)
  isPropTy* : ∀ {A} → isProp (Σ[ Γ ∈ P.Con ] Ty Γ A)

  isPropCon nil nil i = nil
  isPropCon (ext Γᵂ₀ Aᵂ₀) (ext Γᵂ₁ Aᵂ₁) i =
    ext (isPropCon Γᵂ₀ Γᵂ₁ i) (isPropTy Aᵂ₀ Aᵂ₁ i)

  isPropTy = isPropΣ→isProp-snd P.isSetCon isPropTy* _

  isPropTy* (_ , univ Γᵂ₀) (_ , univ Γᵂ₁) i = _ , univ (isPropCon Γᵂ₀ Γᵂ₁ i)
  isPropTy* (_ , el Γᵂ₀) (_ , el Γᵂ₁) i = _ , el (isPropCon Γᵂ₀ Γᵂ₁ i)
  isPropTy* (_ , pi Γᵂ₀ Aᵂ₀ Bᵂ₀) (_ , pi Γᵂ₁ Aᵂ₁ Bᵂ₁) i =
    _ , pi (isPropCon Γᵂ₀ Γᵂ₁ i) (isPropTy Aᵂ₀ Aᵂ₁ i) (isPropTy Bᵂ₀ Bᵂ₁ i)
