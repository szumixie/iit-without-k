module IITWithoutK.SSTSignature.Initial.Bounded where

open import IITWithoutK.Prelude
open import IITWithoutK.SSTSignature.Algebra

Init₀ : BAlg 0
Init₀ .BAlg.Con i 1≤i i≤0 = ⊥-rec (¬suc≤0 (1≤i ◂ i≤0))
Init₀ .BAlg.Tel j 1+i≤j j≤0 = ⊥-rec (¬suc≤0 (1+i≤j ◂ j≤0))

module Init₊ {n} (M : BAlg n) where
  private
    module M = BAlg M

  module * where
    data Con : ∀ i → 1 ≤ i → i ≐ 1 + n → Type where
      nilC : ∀ 1≐1+n → Con 1 ≤-refl 1≐1+n

    data Tel :
      ∀ {i 1≤i} j (1+i≤j : 1 + i ≤ j) (j≐1+n : j ≐ 1 + n) →
      M.Con i 1≤i (≤-unsuc (1+i≤j ◂ ≐→≤ j≐1+n)) → Type
      where

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

  module Tel {i 1≤i} j (1+i≤j : 1 + i ≤ j) where
    cases : ≤-CasesP j n
    cases =
      mk-≤-CasesP
        (λ j≤1+n → Con i 1≤i (≤-step ◂ 1+i≤j ◂ j≤1+n) → Type)
        (λ j≤n 𝑖 → Con.lt-β i 1≤i (≤-step ◂ 1+i≤j ◂ j≤n) 𝑖 → Type)
        (λ j≐1+n 𝑖 → Con.lt-β i 1≤i (≤-unsuc (1+i≤j ◂ ≐→≤ j≐1+n)) 𝑖 → Type)
        (M.Tel j 1+i≤j)
        (*.Tel j 1+i≤j)

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to Tel)

  open Tel public using (Tel)

  module nilC where
    cases : ≤-CasesP 1 n
    cases =
      mk-≤-CasesP
        (λ 1≤1+n → Con 1 ≤-refl 1≤1+n)
        (λ 1≤n 𝑖 → Con.lt-β 1 ≤-refl 1≤n 𝑖)
        (λ 1≐1+n 𝑖 → Con.eq-β 1 ≤-refl 1≐1+n 𝑖)
        M.nilC
        *.nilC

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to nilC)

  open nilC public using (nilC)

  Init₊ : BAlg (1 + n)
  Init₊ .BAlg.Con i 1≤i i≤n = Con i 1≤i i≤n
  Init₊ .BAlg.Tel j 1+i≤j j≤n = Tel j 1+i≤j j≤n

  Init₊ .BAlg.nilC 1≤n = nilC 1≤n

  Init₊* : B*Alg M
  Init₊* .B*Alg.Con i 1≤i i≐1+n = *.Con i 1≤i i≐1+n

  Init₊* .B*Alg.nilC 1≐1+n = *.nilC 1≐1+n

{-}
  Init₊-lower : lower-BAlg Init₊ ≡ M
  Init₊-lower 𝑖 .BAlg.Con i 1≤i i≤n = Con.lt-β i 1≤i i≤n 𝑖
  Init₊-lower 𝑖 .BAlg.nilC 1≤n = nilC.lt-β 1≤n 𝑖

  Init₊-unroll : PathP (λ 𝑖 → B*Alg (Init₊-lower 𝑖)) (unroll-BAlg Init₊) Init₊*
  Init₊-unroll 𝑖 .B*Alg.Con i 1≤i i≐1+n = Con.eq-β i 1≤i i≐1+n 𝑖
  Init₊-unroll 𝑖 .B*Alg.nilC 1≐1+n = nilC.eq-β 1≐1+n 𝑖

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

---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}---}
