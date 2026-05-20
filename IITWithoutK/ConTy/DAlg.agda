module IITWithoutK.ConTy.DAlg where

open import IITWithoutK.Prelude
import IITWithoutK.ConTy.Syntax as S

record DAlg : Type₁ where
  field
    Con : S.Con → Type
    Ty : ∀ {Γ} → Con Γ → S.Ty Γ → Type

    nil : Con S.nil
    ext : ∀ {Γ} (Γᴹ : Con Γ) {A} → Ty Γᴹ A → Con (S.ext Γ A)

    univ : ∀ {Γ} (Γᴹ : Con Γ) → Ty Γᴹ (S.univ Γ)
    el : ∀ {Γ} (Γᴹ : Con Γ) → Ty (ext Γᴹ (univ Γᴹ)) (S.el Γ)
    pi :
      ∀ {Γ} (Γᴹ : Con Γ) {A} (Aᴹ : Ty Γᴹ A) {B} → Ty (ext Γᴹ Aᴹ) B →
      Ty Γᴹ (S.pi Γ A B)

  el# : ∀ {Γ} (Γᴹ : Con Γ) {Ωᴹ} → Ωᴹ ≡ ext Γᴹ (univ Γᴹ) → Ty Ωᴹ (S.el Γ)
  el# {Γ} Γᴹ p = transport (λ i → Ty (p (~ i)) (S.el Γ)) (el Γᴹ)

record Ind (M : DAlg) : Type where
  open S
  private
    module M = DAlg M

  field
    indCon : (Γ : Con) → M.Con Γ
    indTy : ∀ {Γ} (A : Ty Γ) → M.Ty (indCon Γ) A

    nil-β : indCon nil ≡ M.nil
    ext-β : ∀ Γ A → indCon (ext Γ A) ≡ M.ext (indCon Γ) (indTy A)
    univ-β : ∀ Γ → indTy (univ Γ) ≡ M.univ (indCon Γ)

  ext-univ-β :
    ∀ Γ → indCon (ext Γ (univ Γ)) ≡ M.ext (indCon Γ) (M.univ (indCon Γ))
  ext-univ-β Γ i =
    hcomp
      (λ where
        j (i = i0) → indCon (ext Γ (univ Γ))
        j (i = i1) → M.ext (indCon Γ) (univ-β Γ j))
      (ext-β Γ (univ Γ) i)

  field
    el-β : ∀ Γ → indTy (el Γ) ≡ M.el# (indCon Γ) (ext-univ-β Γ)

  indTy-ext : ∀ {Γ A} (B : Ty (ext Γ A)) → M.Ty (M.ext (indCon Γ) (indTy A)) B
  indTy-ext {Γ} {A} B = transport (λ i → M.Ty (ext-β Γ A i) B) (indTy B)

  field
    pi-β : ∀ Γ A B → indTy (pi Γ A B) ≡ M.pi (indCon Γ) (indTy A) (indTy-ext B)
