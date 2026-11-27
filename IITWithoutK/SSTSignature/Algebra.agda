module IITWithoutK.SSTSignature.Algebra where

open import IITWithoutK.Prelude

record Alg : Type where
  field
    Con : Type
    Tel : Con → Type

    nilC : Con

record IAlg : Type where
  field
    Con : ∀ i → 1 ≤ i → Type
    Tel : ∀ {i 1≤i} j → 1 + i ≤ j → Con i 1≤i → Type

    nilC : Con 1 ≤-refl

record BAlg (n : ℕ) : Type where
  field
    Con : ∀ i → 1 ≤ i → i ≤ n → Type
    Tel :
      ∀ {i 1≤i} j (1+i≤j : 1 + i ≤ j) (j≤n : j ≤ n) →
      Con i 1≤i (≤-step ◂ 1+i≤j ◂ j≤n) → Type

    nilC : ∀ 1≤n → Con 1 ≤-refl 1≤n

record B*Alg {n} (M : BAlg n) : Type where
  private
    module M = BAlg M

  field
    Con : ∀ i → 1 ≤ i → i ≐ 1 + n → Type
    Tel :
      ∀ {i 1≤i} j (1+i≤j : 1 + i ≤ j) (j≤1+n : j ≐ 1 + n) →
      M.Con i 1≤i (≤-unsuc (1+i≤j ◂ ≐→≤ j≤1+n)) → Type

    nilC : ∀ 1≐1+n → Con 1 ≤-refl 1≐1+n

module _ {n} (M : BAlg (1 + n)) where
  private
    module M = BAlg M

  lower-BAlg : BAlg n
  lower-BAlg .BAlg.Con i 1≤i i≤n = M.Con i 1≤i (i≤n ◂ ≤-step)
  lower-BAlg .BAlg.Tel j 1+i≤j j≤n = M.Tel j 1+i≤j (j≤n ◂ ≤-step)

  lower-BAlg .BAlg.nilC 1≤n = M.nilC (1≤n ◂ ≤-step)

module _ {n} (M : BAlg (1 + n)) where
  private
    module M = BAlg M

  unroll-BAlg : B*Alg (lower-BAlg M)
  unroll-BAlg .B*Alg.Con i 1≤i i≐1+n = M.Con i 1≤i (≐→≤ i≐1+n)
  unroll-BAlg .B*Alg.Tel j 1+i≤j j≐1+n = M.Tel j 1+i≤j (≐→≤ j≐1+n)

  unroll-BAlg .B*Alg.nilC 1≐1+n = M.nilC (≐→≤ 1≐1+n)

module _ (n : ℕ) (M : IAlg) where
  private
    module M = IAlg M

  proj-BAlg : BAlg n
  proj-BAlg .BAlg.Con i 1≤i i≤n = M.Con i 1≤i
  proj-BAlg .BAlg.Tel j 1+i≤j j≤n = M.Tel j 1+i≤j

  proj-BAlg .BAlg.nilC 1≤n = M.nilC

module _ (n : ℕ) (M : IAlg) where
  private
    module M = IAlg M

  lower-proj-BAlg : lower-BAlg (proj-BAlg (1 + n) M) ≡ proj-BAlg n M
  lower-proj-BAlg 𝑖 .BAlg.Con i 1≤i i≤n = M.Con i 1≤i
  lower-proj-BAlg 𝑖 .BAlg.Tel j 1+i≤j j≤n = M.Tel j 1+i≤j

  lower-proj-BAlg 𝑖 .BAlg.nilC 1≤n = M.nilC

---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}
