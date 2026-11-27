open import IITWithoutK.Prelude

module IITWithoutK.OpenExample.Initial.Bounded (X : Type) where

open import IITWithoutK.OpenExample.Algebra X

Init₀ : BAlg 0
Init₀ .BAlg.Con i 1≤i i≤0 = ⊥-rec (¬suc≤0 (1≤i ◂ i≤0))
Init₀ .BAlg.Ty j 1+i≤j j≤n = ⊥-rec (¬suc≤0 (1+i≤j ◂ j≤n))

module Init₊ {n} (M : BAlg n) where
  private
    module M = BAlg M

  module * where
    data Con : ∀ i → 1 ≤ i → i ≐ 1 + n → Type where
      inc : ∀ 1≐1+n → X → Con 1 ≤-refl 1≐1+n
      ext :
        ∀ {i 1≤i j 1+i≤j} 1+j≐1+n →
        (Γ : M.Con i 1≤i (≤-step ◂ 1+i≤j ◂ ≤-unsuc (≐→≤ 1+j≐1+n))) →
        M.Ty j 1+i≤j (≤-unsuc (≐→≤ 1+j≐1+n)) Γ →
        Con (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step) 1+j≐1+n

    data Ty :
      ∀ {i 1≤i} j (1+i≤j : 1 + i ≤ j) (j≐1+n : j ≐ 1 + n) →
      M.Con i 1≤i (≤-unsuc (1+i≤j ◂ ≐→≤ j≐1+n)) → Type
      where
      base :
        ∀ {i 1≤i} 1+i≐1+n →
        (Γ : M.Con i 1≤i (≤-unsuc (≐→≤ 1+i≐1+n))) → Ty (1 + i) ≤-refl 1+i≐1+n Γ

  module Con i (1≤i : 1 ≤ i) where
    cases : ≤-CasesP i n
    cases =
      mk-≤-CasesP
        (λ i≤1+n → Type)
        (λ i≤n 𝑖 → Type)
        (λ i≐1+n 𝑖 → Type)
        (M.Con i 1≤i)
        (*.Con i 1≤i)

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to Con)

  open Con public using (Con)

  module Ty {i 1≤i} j (1+i≤j : 1 + i ≤ j) where
    cases : ≤-CasesP j n
    cases =
      mk-≤-CasesP
        (λ j≤1+n → Con i 1≤i (≤-step ◂ 1+i≤j ◂ j≤1+n) → Type)
        (λ j≤n 𝑖 → Con.lt-β i 1≤i (≤-step ◂ 1+i≤j ◂ j≤n) 𝑖 → Type)
        (λ j≐1+n 𝑖 → Con.lt-β i 1≤i (≤-unsuc (1+i≤j ◂ ≐→≤ j≐1+n)) 𝑖 → Type)
        (M.Ty j 1+i≤j)
        (*.Ty j 1+i≤j)

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to Ty)

  open Ty public using (Ty)

  module inc where
    cases : ≤-CasesP 1 n
    cases =
      mk-≤-CasesP
        (λ 1≤1+n → X → Con 1 ≤-refl 1≤1+n)
        (λ 1≤n 𝑖 → X → Con.lt-β 1 ≤-refl 1≤n 𝑖)
        (λ 1≐1+n 𝑖 → X → Con.eq-β 1 ≤-refl 1≐1+n 𝑖)
        M.inc
        *.inc

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to inc)

  open inc public using (inc)

  module ext {i 1≤i j 1+i≤j} where
    cases : ≤-CasesP (1 + j) n
    cases =
      mk-≤-CasesP
        (λ 1+j≤1+n →
          (Γ : Con i 1≤i (≤-step ◂ 1+i≤j ◂ ≤-step ◂ 1+j≤1+n)) →
          Ty j 1+i≤j (≤-step ◂ 1+j≤1+n) Γ →
          Con (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step) 1+j≤1+n)
        (λ 1+j≤n 𝑖 →
          (Γ : Con.lt-β i 1≤i (≤-step ◂ 1+i≤j ◂ ≤-step ◂ 1+j≤n) 𝑖) →
          Ty.lt-β j 1+i≤j (≤-step ◂ 1+j≤n) 𝑖 Γ →
          Con.lt-β (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step) 1+j≤n 𝑖)
        (λ 1+j≐1+n 𝑖 →
          (Γ : Con.lt-β i 1≤i (≤-step ◂ 1+i≤j ◂ ≤-unsuc (≐→≤ 1+j≐1+n)) 𝑖) →
          Ty.lt-β j 1+i≤j (≤-unsuc (≐→≤ 1+j≐1+n)) 𝑖 Γ →
          Con.eq-β (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step) 1+j≐1+n 𝑖)
        M.ext
        *.ext

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to ext)

  open ext public using (ext)

  module base {i 1≤i} where
    cases : ≤-CasesP (1 + i) n
    cases =
      mk-≤-CasesP
        (λ 1+i≤1+n →
          (Γ : Con i 1≤i (≤-step ◂ 1+i≤1+n)) →
          Ty (1 + i) ≤-refl 1+i≤1+n Γ)
        (λ 1+i≤n 𝑖 →
          (Γ : Con.lt-β i 1≤i (≤-step ◂ 1+i≤n) 𝑖) →
          Ty.lt-β (1 + i) ≤-refl 1+i≤n 𝑖 Γ)
        (λ 1+i≐1+n 𝑖 →
          (Γ : Con.lt-β i 1≤i (≤-unsuc (≐→≤ 1+i≐1+n)) 𝑖) →
          Ty.eq-β (1 + i) ≤-refl 1+i≐1+n 𝑖 Γ)
        M.base
        *.base

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to base)

  open base public using (base)

  Init₊ : BAlg (1 + n)
  Init₊ .BAlg.Con i 1≤i i≤n = Con i 1≤i i≤n
  Init₊ .BAlg.Ty j 1+i≤j j≤n = Ty j 1+i≤j j≤n

  Init₊ .BAlg.inc 1≤n = inc 1≤n
  Init₊ .BAlg.ext 1+j≤n = ext 1+j≤n
  Init₊ .BAlg.base 1+i≤n = base 1+i≤n

  Init₊* : B*Alg M
  Init₊* .B*Alg.Con i 1≤i i≐1+n = *.Con i 1≤i i≐1+n
  Init₊* .B*Alg.Ty j 1+i≤j j≐1+n = *.Ty j 1+i≤j j≐1+n

  Init₊* .B*Alg.inc 1≐1+n = *.inc 1≐1+n
  Init₊* .B*Alg.ext 1+j≐1+n = *.ext 1+j≐1+n
  Init₊* .B*Alg.base 1+i≐1+n = *.base 1+i≐1+n

  Init₊-lower : lower-BAlg Init₊ ≡ M
  Init₊-lower 𝑖 .BAlg.Con i 1≤i i≤n = Con.lt-β i 1≤i i≤n 𝑖
  Init₊-lower 𝑖 .BAlg.Ty j 1+i≤j j≤n = Ty.lt-β j 1+i≤j j≤n 𝑖

  Init₊-lower 𝑖 .BAlg.inc 1≤n = inc.lt-β 1≤n 𝑖
  Init₊-lower 𝑖 .BAlg.ext 1+j≤n = ext.lt-β 1+j≤n 𝑖
  Init₊-lower 𝑖 .BAlg.base 1+i≤n = base.lt-β 1+i≤n 𝑖

  Init₊-unroll : PathP (λ 𝑖 → B*Alg (Init₊-lower 𝑖)) (unroll-BAlg Init₊) Init₊*
  Init₊-unroll 𝑖 .B*Alg.Con i 1≤i i≐1+n = Con.eq-β i 1≤i i≐1+n 𝑖
  Init₊-unroll 𝑖 .B*Alg.Ty j 1+i≤j j≐1+n = Ty.eq-β j 1+i≤j j≐1+n 𝑖

  Init₊-unroll 𝑖 .B*Alg.inc 1≐1+n = inc.eq-β 1≐1+n 𝑖
  Init₊-unroll 𝑖 .B*Alg.ext 1+j≐1+n = ext.eq-β 1+j≐1+n 𝑖
  Init₊-unroll 𝑖 .B*Alg.base 1+i≐1+n = base.eq-β 1+i≐1+n 𝑖

open Init₊ using (Init₊; Init₊*; Init₊-lower; Init₊-unroll)

opaque
  Init : ∀ n → BAlg n
  Init zero = Init₀
  Init (suc n) = Init₊ (Init n)

Init* : ∀ n → B*Alg (Init n)
Init* n = Init₊* (Init n)

opaque
  unfolding Init

  Init-lower : ∀ n → lower-BAlg (Init (1 + n)) ≡ Init n
  Init-lower n = Init₊-lower (Init n)

  Init-unroll :
    ∀ n →
    PathP (λ 𝑖 → B*Alg (Init-lower n 𝑖)) (unroll-BAlg (Init (1 + n))) (Init* n)
  Init-unroll n = Init₊-unroll (Init n)

module _ n where
  open BAlg (Init n) public
  module * = Init₊.* (Init n)
  module lower 𝑖 = BAlg (Init-lower n 𝑖)
  module unroll 𝑖 = B*Alg (Init-unroll n 𝑖)
