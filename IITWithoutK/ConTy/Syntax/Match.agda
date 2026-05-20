module IITWithoutK.ConTy.Syntax.Match where

open import IITWithoutK.Prelude
import IITWithoutK.ConTy.Syntax.Pre as P
import IITWithoutK.ConTy.Syntax.Wf as W
import IITWithoutK.ConTy.Syntax as S

record MAlg : Type₁ where
  field
    Con : S.Con → Type
    Ty : ∀ {Γ} → S.Ty Γ → Type

    nil : Con S.nil
    ext : ∀ Γ A → Con (S.ext Γ A)

    univ : ∀ Γ → Ty (S.univ Γ)
    el : ∀ Γ → Ty (S.el Γ)
    pi : ∀ Γ A B → Ty (S.pi Γ A B)

module Match (M : MAlg) where
  open S
  private
    module M = MAlg M

  opaque
    matchCon* : ∀ {Γ} (Γᵂ : W.Con Γ) → M.Con (mkCon Γᵂ)
    matchCon* W.nil = M.nil
    matchCon* (W.ext Γᵂ Aᵂ) = M.ext (mkCon Γᵂ) (mkTy Aᵂ)

    matchCon : (Γ : Con) → M.Con Γ
    matchCon Γ = matchCon* (Γ .wf)

    matchTy* : ∀ {Γ A} (Aᵂ : W.Ty Γ A) → M.Ty {mkCon (W.Ty→Con Aᵂ)} (mkTy Aᵂ)
    matchTy* (W.univ Γᵂ) = M.univ (mkCon Γᵂ)
    matchTy* (W.el Γᵂ) = M.el (mkCon Γᵂ)
    matchTy* (W.pi Γᵂ Aᵂ Bᵂ) = M.pi (mkCon Γᵂ) (mkTy Aᵂ) (mkTy Bᵂ)

    matchTy : ∀ {Γ} (A : Ty Γ) → M.Ty A
    matchTy A = filler i1
      module matchTy where
      open substProp
        W.isPropCon
        (λ Γᵂ → M.Ty {mkCon Γᵂ} (mkTy (A .wf)))
        (matchTy* (A .wf))
        public

    nil-β : matchCon nil ≡ M.nil
    nil-β i = matchCon nil

    ext-β : ∀ Γ A → matchCon (ext Γ A) ≡ M.ext Γ A
    ext-β Γ A i = matchCon (ext Γ A)

    univ-β : ∀ Γ → matchTy (univ Γ) ≡ M.univ Γ
    univ-β Γ i = matchTy.filler# (univ Γ) refl (~ i)

    el-β : ∀ Γ → matchTy (el Γ) ≡ M.el Γ
    el-β Γ i = matchTy.filler# (el Γ) refl (~ i)

    pi-β : ∀ Γ A B → matchTy (pi Γ A B) ≡ M.pi Γ A B
    pi-β Γ A B i = matchTy.filler# (pi Γ A B) refl (~ i)
