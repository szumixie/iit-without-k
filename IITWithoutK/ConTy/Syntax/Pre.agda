module IITWithoutK.ConTy.Syntax.Pre where

open import IITWithoutK.Prelude
open import IITWithoutK.Prelude.EncodeDecode

data Con : Type
data Ty : Type

data Con where
  nil : Con
  ext : Con → Ty → Con

data Ty where
  univ : Con → Ty
  el : Con → Ty
  pi : Con → Ty → Ty → Ty

heightCon : Con → ℕ
heightTy : Ty → ℕ

heightCon nil = 1
heightCon (ext Γ A) = 1 + heightTy A

heightTy (univ Γ) = 1 + heightCon Γ
heightTy (el Γ) = 3 + heightCon Γ
heightTy (pi Γ A B) = 1 + heightTy B

module ConTyPath where
  module _ where
    open ≟-Ap

    coverCon : (Γ₀ Γ₁ : Con) → Γ₀ ≟ Γ₁
    coverTy : (A₀ A₁ : Ty) → A₀ ≟ A₁

    coverCon nil nil = ⦇ nil ⦈
    coverCon (ext Γ₀ A₀) (ext Γ₁ A₁) = ⦇ ext (coverCon Γ₀ Γ₁) (coverTy A₀ A₁) ⦈
    {-# CATCHALL #-}
    coverCon _ _ = never

    coverTy (univ Γ₀) (univ Γ₁) = ⦇ univ (coverCon Γ₀ Γ₁) ⦈
    coverTy (el Γ₀) (el Γ₁) = ⦇ el (coverCon Γ₀ Γ₁) ⦈
    coverTy (pi Γ₀ A₀ B₀) (pi Γ₁ A₁ B₁) =
      ⦇ pi (coverCon Γ₀ Γ₁) (coverTy A₀ A₁) (coverTy B₀ B₁) ⦈
    {-# CATCHALL #-}
    coverTy _ _ = never

  module _ where
    open ↓-Ap

    reflCodeCon : (Γ : Con) → coverCon Γ Γ ↓ refl
    reflCodeTy : (A : Ty) → coverTy A A ↓ refl

    reflCodeCon nil = ⦇ nil ⦈
    reflCodeCon (ext Γ A) = ⦇ ext (reflCodeCon Γ) (reflCodeTy A) ⦈

    reflCodeTy (univ Γ) = ⦇ univ (reflCodeCon Γ) ⦈
    reflCodeTy (el Γ) = ⦇ el (reflCodeCon Γ) ⦈
    reflCodeTy (pi Γ A B) = ⦇ pi (reflCodeCon Γ) (reflCodeTy A) (reflCodeTy B) ⦈

module _ where
  open ConTyPath

  opaque
    isSetCon : isSet Con
    isSetCon = isSetCover coverCon reflCodeCon

    isSetTy : isSet Ty
    isSetTy = isSetCover coverTy reflCodeTy
