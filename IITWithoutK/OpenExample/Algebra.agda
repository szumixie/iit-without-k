open import IITWithoutK.Prelude

module IITWithoutK.OpenExample.Algebra (X : Type) where

record Alg : Type where
  field
    Con : Type
    Ty : Con → Type

    inc : X → Con
    ext : (Γ : Con) → Ty Γ → Con
    base : (Γ : Con) → Ty Γ

record IAlg : Type where
  field
    Con : ∀ i → 1 ≤ i → Type
    Ty : ∀ {i 1≤i} j → 1 + i ≤ j → Con i 1≤i → Type

    inc : X → Con 1 ≤-refl
    ext :
      ∀ {i 1≤i j 1+i≤j} →
      (Γ : Con i 1≤i) → Ty j 1+i≤j Γ →
      Con (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step)
    base : ∀ {i 1≤i} (Γ : Con i 1≤i) → Ty (1 + i) ≤-refl Γ

record BAlg (n : ℕ) : Type where
  field
    Con : ∀ i → 1 ≤ i → i ≤ n → Type
    Ty :
      ∀ {i 1≤i} j (1+i≤j : 1 + i ≤ j) (j≤n : j ≤ n) →
      Con i 1≤i (≤-step ◂ 1+i≤j ◂ j≤n) → Type

    inc : ∀ 1≤n → X → Con 1 ≤-refl 1≤n
    ext :
      ∀ {i 1≤i j 1+i≤j} 1+j≤n →
      (Γ : Con i 1≤i (≤-step ◂ 1+i≤j ◂ ≤-step ◂ 1+j≤n)) →
      Ty j 1+i≤j (≤-step ◂ 1+j≤n) Γ →
      Con (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step) 1+j≤n
    base :
      ∀ {i 1≤i} 1+i≤n →
      (Γ : Con i 1≤i (≤-step ◂ 1+i≤n)) → Ty (1 + i) ≤-refl 1+i≤n Γ

record B*Alg {n} (M : BAlg n) : Type where
  private
    module M = BAlg M

  field
    Con : ∀ i → 1 ≤ i → i ≐ 1 + n → Type
    Ty :
      ∀ {i 1≤i} j (1+i≤j : 1 + i ≤ j) (j≤1+n : j ≐ 1 + n) →
      M.Con i 1≤i (≤-unsuc (1+i≤j ◂ ≐→≤ j≤1+n)) → Type

    inc : ∀ 1≐1+n → X → Con 1 ≤-refl 1≐1+n
    ext :
      ∀ {i 1≤i j 1+i≤j} 1+j≐1+n →
      (Γ : M.Con i 1≤i (≤-step ◂ 1+i≤j ◂ ≤-unsuc (≐→≤ 1+j≐1+n))) →
      M.Ty j 1+i≤j (≤-unsuc (≐→≤ 1+j≐1+n)) Γ →
      Con (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step) 1+j≐1+n
    base :
      ∀ {i 1≤i} 1+i≐1+n →
      (Γ : M.Con i 1≤i (≤-unsuc (≐→≤ 1+i≐1+n))) → Ty (1 + i) ≤-refl 1+i≐1+n Γ

module _ {n} (M : BAlg (1 + n)) where
  private
    module M = BAlg M

  lower-BAlg : BAlg n
  lower-BAlg .BAlg.Con i 1≤i i≤n = M.Con i 1≤i (i≤n ◂ ≤-step)
  lower-BAlg .BAlg.Ty j 1+i≤j j≤n = M.Ty j 1+i≤j (j≤n ◂ ≤-step)

  lower-BAlg .BAlg.inc 1≤n = M.inc (1≤n ◂ ≤-step)
  lower-BAlg .BAlg.ext 1+j≤n = M.ext (1+j≤n ◂ ≤-step)
  lower-BAlg .BAlg.base 1+i≤n = M.base (1+i≤n ◂ ≤-step)

module _ {n} (M : BAlg (1 + n)) where
  private
    module M = BAlg M

  unroll-BAlg : B*Alg (lower-BAlg M)
  unroll-BAlg .B*Alg.Con i 1≤i i≐1+n = M.Con i 1≤i (≐→≤ i≐1+n)
  unroll-BAlg .B*Alg.Ty j 1+i≤j j≐1+n = M.Ty j 1+i≤j (≐→≤ j≐1+n)

  unroll-BAlg .B*Alg.inc 1≐1+n = M.inc (≐→≤ 1≐1+n)
  unroll-BAlg .B*Alg.ext 1+j≐1+n = M.ext (≐→≤ 1+j≐1+n)
  unroll-BAlg .B*Alg.base 1+i≐1+n = M.base (≐→≤ 1+i≐1+n)

module _ (n : ℕ) (M : IAlg) where
  private
    module M = IAlg M

  proj-BAlg : BAlg n
  proj-BAlg .BAlg.Con i 1≤i i≤n = M.Con i 1≤i
  proj-BAlg .BAlg.Ty j 1+i≤j j≤n = M.Ty j 1+i≤j

  proj-BAlg .BAlg.inc 1≤n = M.inc
  proj-BAlg .BAlg.ext 1+j≤n = M.ext
  proj-BAlg .BAlg.base 1+i≤n = M.base

module _ (n : ℕ) (M : IAlg) where
  private
    module M = IAlg M

  lower-proj-BAlg : lower-BAlg (proj-BAlg (1 + n) M) ≡ proj-BAlg n M
  lower-proj-BAlg 𝑖 .BAlg.Con i 1≤i i≤n = M.Con i 1≤i
  lower-proj-BAlg 𝑖 .BAlg.Ty j 1+i≤j j≤n = M.Ty j 1+i≤j

  lower-proj-BAlg 𝑖 .BAlg.inc 1≤n = M.inc
  lower-proj-BAlg 𝑖 .BAlg.ext 1+j≤n = M.ext
  lower-proj-BAlg 𝑖 .BAlg.base 1+i≤n = M.base
