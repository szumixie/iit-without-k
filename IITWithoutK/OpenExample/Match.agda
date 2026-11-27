open import IITWithoutK.Prelude

module IITWithoutK.OpenExample.Match (X : Type) where

open import IITWithoutK.OpenExample.Algebra X
import IITWithoutK.OpenExample.Initial.Bounded X as B
import IITWithoutK.OpenExample.Initial.Indexed X as H
import IITWithoutK.OpenExample.Initial X as S

record Cases : Type where
  field
    Con : S.Con → Type
    Ty : ∀ {Γ} → S.Ty Γ → Type

    inc : ∀ x → Con (S.inc x)
    ext : ∀ Γ A → Con (S.ext Γ A)
    base : ∀ Γ → Ty (S.base Γ)

module Match (M : Cases) where
  private
    module M = Cases M

  module Mᴴ where
    Con : ∀ {i 1≤i} → H.Con i 1≤i → Type
    Con Γ = M.Con (S.mkCon Γ)

    Ty : ∀ {i 1≤i j 1+i≤j} {Γ : H.Con i 1≤i} → H.Ty j 1+i≤j Γ → Type
    Ty A = M.Ty (S.mkTy A)

    inc : ∀ x → Con (H.inc x)
    inc x = M.inc x

    ext :
      ∀ {i 1≤i j 1+i≤j} (Γ : H.Con i 1≤i) (A : H.Ty j 1+i≤j Γ) → Con (H.ext Γ A)
    ext Γ A = M.ext (S.mkCon Γ) (S.mkTy A)

    base : ∀ {i 1≤i} (Γ : H.Con i 1≤i) → Ty (H.base Γ)
    base Γ = M.base (S.mkCon Γ)

  module Mᴮ where
    module Con {i 1≤i} where
      line : I → Type
      line 𝑖 = H.proj.Con i 𝑖 i 1≤i ≤-refl → Type

      opaque
        tr : TransportFiller line Mᴴ.Con
        tr = transport-fill line Mᴴ.Con

      open TransportFiller tr public renaming (end to Con)

    open Con public using (Con)

    module Ty {i 1≤i j 1+i≤j} where
      line : I → Type
      line 𝑖 =
        {Γ : H.proj.Con j 𝑖 i 1≤i (≤-step ◂ 1+i≤j)} →
        H.proj.Ty j 𝑖 j 1+i≤j ≤-refl Γ →
        Type

      opaque
        tr : TransportFiller line Mᴴ.Ty
        tr = transport-fill line Mᴴ.Ty

      open TransportFiller tr public renaming (end to Ty)

    open Ty public using (Ty)

    module inc where
      line : I → Type
      line 𝑖 = ∀ x → Con.filler 𝑖 (H.proj.inc 1 𝑖 ≤-refl x)

      opaque
        tr : TransportFiller line Mᴴ.inc
        tr = transport-fill line Mᴴ.inc

      open TransportFiller tr public renaming (end to inc)

    open inc public using (inc)

    module ext {i 1≤i j 1+i≤j} where
      line : I → Type
      line 𝑖 =
        (Γ : H.proj.Con (1 + j) 𝑖 i 1≤i (≤-step ◂ 1+i≤j ◂ ≤-step)) →
        (A : H.proj.Ty (1 + j) 𝑖 j 1+i≤j ≤-step Γ) →
        Con.filler 𝑖 (H.proj.ext (1 + j) 𝑖 ≤-refl Γ A)

      opaque
        tr : TransportFiller line Mᴴ.ext
        tr = transport-fill line Mᴴ.ext

      open TransportFiller tr public renaming (end to ext)

    open ext public using (ext)

    module base {i 1≤i} where
      line : I → Type
      line 𝑖 =
        (Γ : H.proj.Con (1 + i) 𝑖 i 1≤i ≤-step) →
        Ty.filler 𝑖 (H.proj.base (1 + i) 𝑖 ≤-refl Γ)

      opaque
        tr : TransportFiller line Mᴴ.base
        tr = transport-fill line Mᴴ.base

      open TransportFiller tr public renaming (end to base)

    open base public using (base)

  module Mᴮ* where
    module Con {i 1≤1+i} where
      line : I → Type
      line 𝑖 = B.unroll.Con i 𝑖 (1 + i) 1≤1+i ≐-refl → Type

      opaque
        tr : TransportFiller line Mᴮ.Con
        tr = transport-fill line Mᴮ.Con

      open TransportFiller tr public renaming (end to Con)

    open Con public using (Con)

    module Ty {i 1≤i j 1+i≤1+j} where
      line : I → Type
      line 𝑖 =
        {Γ : B.lower.Con j 𝑖 i 1≤i (≤-unsuc 1+i≤1+j)} →
        B.unroll.Ty j 𝑖 (1 + j) 1+i≤1+j ≐-refl Γ →
        Type

      opaque
        tr : TransportFiller line Mᴮ.Ty
        tr = transport-fill line Mᴮ.Ty

      open TransportFiller tr public renaming (end to Ty)

    open Ty public using (Ty)

    module inc where
      line : I → Type
      line 𝑖 = ∀ x → Con.filler 𝑖 (B.unroll.inc 0 𝑖 ≐-refl x)

      opaque
        tr : TransportFiller line Mᴮ.inc
        tr = transport-fill line Mᴮ.inc

      open TransportFiller tr public renaming (end to inc)

    open inc public using (inc)

    module ext {i 1≤i j 1+i≤j} where
      line : I → Type
      line 𝑖 =
        (Γ : B.lower.Con j 𝑖 i 1≤i (≤-step ◂ 1+i≤j)) →
        (A : B.lower.Ty j 𝑖 j 1+i≤j ≤-refl Γ) →
        Con.filler 𝑖 (B.unroll.ext j 𝑖 ≐-refl Γ A)

      opaque
        tr : TransportFiller line Mᴮ.ext
        tr = transport-fill line Mᴮ.ext

      open TransportFiller tr public renaming (end to ext)

    open ext public using (ext)

    module base {i 1≤i} where
      line : I → Type
      line 𝑖 =
        (Γ : B.lower.Con i 𝑖 i 1≤i ≤-refl) →
        Ty.filler 𝑖 (B.unroll.base i 𝑖 ≐-refl Γ)

      opaque
        tr : TransportFiller line Mᴮ.base
        tr = transport-fill line Mᴮ.base

      open TransportFiller tr public renaming (end to base)

    open base public using (base)

  matchConᴮ* : ∀ {i 1≤1+i} (Γ : B.*.Con i (1 + i) 1≤1+i ≐-refl) → Mᴮ*.Con Γ
  matchConᴮ* (B.*.inc 1≐1 x) = Mᴮ*.inc x
  matchConᴮ* (B.*.ext 1+j≐1+j Γ A) = Mᴮ*.ext Γ A

  matchTyᴮ* :
    ∀ {i 1≤i j 1+i≤1+j} →
    {Γ : B.Con j i 1≤i (≤-unsuc 1+i≤1+j)} →
    (A : B.*.Ty j (1 + j) 1+i≤1+j ≐-refl Γ) →
    Mᴮ*.Ty A
  matchTyᴮ* (B.*.base 1+i≐1+i Γ) = Mᴮ*.base Γ

  module matchConᴮ₊ {i 1≤1+i} where
    line : I → Type
    line 𝑖 =
      (Γ : B.unroll.Con i (~ 𝑖) (1 + i) 1≤1+i ≐-refl) → Mᴮ*.Con.filler (~ 𝑖) Γ

    opaque
      tr : TransportFiller line matchConᴮ*
      tr = transport-fill line matchConᴮ*

    open TransportFiller tr public renaming (end to matchConᴮ₊)

  open matchConᴮ₊ public using (matchConᴮ₊)

  matchConᴮ : ∀ {i 1≤i} (Γ : B.Con i i 1≤i ≤-refl) → Mᴮ.Con Γ
  matchConᴮ {i = suc i} = matchConᴮ₊

  module matchTyᴮ₊ {i 1≤i j 1+i≤1+j} where
    line : I → Type
    line 𝑖 =
      {Γ : B.lower.Con j (~ 𝑖) i 1≤i (≤-unsuc 1+i≤1+j)} →
      (A : B.unroll.Ty j (~ 𝑖) (1 + j) 1+i≤1+j ≐-refl Γ) →
      Mᴮ*.Ty.filler (~ 𝑖) A

    opaque
      tr : TransportFiller line matchTyᴮ*
      tr = transport-fill line matchTyᴮ*

    open TransportFiller tr public renaming (end to matchTyᴮ₊)

  open matchTyᴮ₊ public using (matchTyᴮ₊)

  matchTyᴮ :
    ∀ {i 1≤i j 1+i≤j} →
    {Γ : B.Con j i 1≤i (≤-step ◂ 1+i≤j)} →
    (A : B.Ty j j 1+i≤j ≤-refl Γ) →
    Mᴮ.Ty A
  matchTyᴮ {j = suc j} = matchTyᴮ₊

  module inc-βᴮ where
    line : I → Type
    line 𝑖 =
      ∀ x →
      matchConᴮ₊.filler 𝑖 (B.unroll.inc 0 (~ 𝑖) ≐-refl x) ≡
      Mᴮ*.inc.filler (~ 𝑖) x

    opaque
      tr : TransportFiller line λ x → refl
      tr = transport-fill line λ x → refl

    open TransportFiller tr public renaming (end to inc-βᴮ)

  open inc-βᴮ public using (inc-βᴮ)

  module ext-βᴮ {i 1≤i j 1+i≤j} where
    line : I → Type
    line 𝑖 =
      (Γ : B.lower.Con j (~ 𝑖) i 1≤i (≤-step ◂ 1+i≤j)) →
      (A : B.lower.Ty j (~ 𝑖) j 1+i≤j ≤-refl Γ) →
      matchConᴮ₊.filler 𝑖 (B.unroll.ext j (~ 𝑖) ≐-refl Γ A) ≡
      Mᴮ*.ext.filler (~ 𝑖) Γ A

    opaque
      tr : TransportFiller line λ Γ A → refl
      tr = transport-fill line λ Γ A → refl

    open TransportFiller tr public renaming (end to ext-βᴮ)

  open ext-βᴮ public using (ext-βᴮ)

  module base-βᴮ {i 1≤i} where
    line : I → Type
    line 𝑖 =
      (Γ : B.lower.Con i (~ 𝑖) i 1≤i ≤-refl) →
      matchTyᴮ₊.filler 𝑖 (B.unroll.base i (~ 𝑖) ≐-refl Γ) ≡
      Mᴮ*.base.filler (~ 𝑖) Γ

    opaque
      tr : TransportFiller line λ Γ → refl
      tr = transport-fill line λ Γ → refl

    open TransportFiller tr public renaming (end to base-βᴮ)

  open base-βᴮ public using (base-βᴮ)

  module matchConᴴ {i 1≤i} where
    line : I → Type
    line 𝑖 = (Γ : H.proj.Con i (~ 𝑖) i 1≤i ≤-refl) → Mᴮ.Con.filler (~ 𝑖) Γ

    opaque
      tr : TransportFiller line matchConᴮ
      tr = transport-fill line matchConᴮ

    open TransportFiller tr public renaming (end to matchConᴴ)

  open matchConᴴ public using (matchConᴴ)

  module matchTyᴴ {i 1≤i j 1+i≤j} where
    line : I → Type
    line 𝑖 =
      {Γ : H.proj.Con j (~ 𝑖) i 1≤i (≤-step ◂ 1+i≤j)} →
      (A : H.proj.Ty j (~ 𝑖) j 1+i≤j ≤-refl Γ) →
      Mᴮ.Ty.filler (~ 𝑖) A

    opaque
      tr : TransportFiller line matchTyᴮ
      tr = transport-fill line matchTyᴮ

    open TransportFiller tr public renaming (end to matchTyᴴ)

  open matchTyᴴ public using (matchTyᴴ)

  module inc-βᴴ where
    line : I → Type
    line 𝑖 =
      ∀ x → matchConᴴ.filler 𝑖 (H.proj.inc 1 (~ 𝑖) ≤-refl x) ≡
      Mᴮ.inc.filler (~ 𝑖) x

    opaque
      tr : TransportFiller line inc-βᴮ
      tr = transport-fill line inc-βᴮ

    open TransportFiller tr public renaming (end to inc-βᴴ)

  open inc-βᴴ public using (inc-βᴴ)

  module ext-βᴴ {i 1≤i j 1+i≤j} where
    line : I → Type
    line 𝑖 =
      (Γ : H.proj.Con (1 + j) (~ 𝑖) i 1≤i (≤-step ◂ 1+i≤j ◂ ≤-step)) →
      (A : H.proj.Ty (1 + j) (~ 𝑖) j 1+i≤j ≤-step Γ) →
      matchConᴴ.filler 𝑖 (H.proj.ext (1 + j) (~ 𝑖) ≤-refl Γ A) ≡
      Mᴮ.ext.filler (~ 𝑖) Γ A

    opaque
      tr : TransportFiller line ext-βᴮ
      tr = transport-fill line ext-βᴮ

    open TransportFiller tr public renaming (end to ext-βᴴ)

  open ext-βᴴ public using (ext-βᴴ)

  module base-βᴴ {i 1≤i} where
    line : I → Type
    line 𝑖 =
      (Γ : H.proj.Con (1 + i) (~ 𝑖) i 1≤i ≤-step) →
      matchTyᴴ.filler 𝑖 (H.proj.base (1 + i) (~ 𝑖) ≤-refl Γ) ≡
      Mᴮ.base.filler (~ 𝑖) Γ

    opaque
      tr : TransportFiller line base-βᴮ
      tr = transport-fill line base-βᴮ

    open TransportFiller tr public renaming (end to base-βᴴ)

  open base-βᴴ public using (base-βᴴ)

  opaque
    matchCon : (Γ : S.Con) → M.Con Γ
    matchCon (S.mkCon Γ) = matchConᴴ Γ

    matchTy : ∀ {Γ} (A : S.Ty Γ) → M.Ty A
    matchTy (S.mkTy A) = matchTyᴴ A

    inc-β : ∀ x → matchCon (S.inc x) ≡ M.inc x
    inc-β x = inc-βᴴ x

    ext-β : ∀ Γ A → matchCon (S.ext Γ A) ≡ M.ext Γ A
    ext-β (S.mkCon Γ) (S.mkTy A) = ext-βᴴ Γ A

    base-β : ∀ Γ → matchTy (S.base Γ) ≡ M.base Γ
    base-β (S.mkCon Γ) = base-βᴴ Γ
