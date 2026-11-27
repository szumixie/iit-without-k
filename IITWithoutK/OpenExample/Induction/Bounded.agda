open import IITWithoutK.Prelude
import IITWithoutK.OpenExample.DAlgebra as DAlgebra

module IITWithoutK.OpenExample.Induction.Bounded X (M : DAlgebra.DAlg X) where

open DAlgebra X
open import IITWithoutK.OpenExample.Initial X
open import IITWithoutK.OpenExample.Match X

private
  module M = DAlg M

ind₀ : Ind (Bounded 0 M)
ind₀ .DAlgebra.Ind.indCon Γ Γ≤0 = ⊥-rec (¬suc≤0 (Γ .lbound ◂ Γ≤0))
ind₀ .DAlgebra.Ind.indTy A A≤0 = ⊥-rec (¬suc≤0 (A .lbound ◂ A≤0))

ind₀ .DAlgebra.Ind.inc-β x 𝑖 ()
ind₀ .DAlgebra.Ind.ext-β Γ A 𝑖 ()
ind₀ .DAlgebra.Ind.base-β Γ 𝑖 ()

module ind₊ {n} (F : Ind (Bounded n M)) where
  private
    module F = Ind F

  *-cases : Cases
  *-cases .Cases.Con Γ = Γ .height ≐ 1 + n → M.Con Γ
  *-cases .Cases.Ty {Γ} A =
    (A≐1+n : A .height ≐ 1 + n) →
    M.Ty (F.indCon Γ (≤-unsuc (A .lbound ◂ ≐→≤ A≐1+n))) A

  *-cases .Cases.inc x 1≐1+n = M.inc x
  *-cases .Cases.ext Γ A 1+A≐1+n =
    M.ext
      (F.indCon Γ (≤-step ◂ A .lbound ◂ ≤-unsuc (≐→≤ 1+A≐1+n)))
      (F.indTy A (≤-unsuc (≐→≤ 1+A≐1+n)))
  *-cases .Cases.base Γ 1+Γ≐1+n = M.base (F.indCon Γ (≤-unsuc (≐→≤ 1+Γ≐1+n)))

  module * = Match *-cases

  module indCon (Γ : Con) where
    cases : ≤-CasesP (Γ .height) n
    cases =
      mk-≤-CasesP
        (λ Γ≤1+n → M.Con Γ)
        (λ Γ≤n 𝑖 → M.Con Γ)
        (λ Γ≐1+n 𝑖 → M.Con Γ)
        (λ Γ≤n → F.indCon Γ Γ≤n)
        (λ Γ≐1+n → *.matchCon Γ Γ≐1+n)

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to indCon)

  open indCon public using (indCon)

  module indTy {Γ} (A : Ty Γ) where
    cases : ≤-CasesP (A .height) n
    cases =
      mk-≤-CasesP
        (λ A≤1+n → M.Ty (indCon Γ (≤-step ◂ A .lbound ◂ A≤1+n)) A)
        (λ A≤n 𝑖 → M.Ty (indCon.lt-β Γ (≤-step ◂ A .lbound ◂ A≤n) 𝑖) A)
        (λ A≐1+n 𝑖 → M.Ty (indCon.lt-β Γ (≤-unsuc (A .lbound ◂ ≐→≤ A≐1+n)) 𝑖) A)
        (λ A≤n → F.indTy A A≤n)
        (λ A≐1+n → *.matchTy A A≐1+n)

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to indTy)

  open indTy public using (indTy)

  module inc-β (x : X) where
    cases : ≤-CasesP 1 n
    cases =
      mk-≤-CasesP
        (λ 1≤1+n → indCon (inc x) 1≤1+n ≡ M.inc x)
        (λ 1≤n 𝑖 → indCon.lt-β (inc x) 1≤n 𝑖 ≡ M.inc x)
        (λ 1≐1+n 𝑖 → indCon.eq-β (inc x) 1≐1+n 𝑖 ≡ M.inc x)
        (λ 1≤n 𝑖 → F.inc-β x 𝑖 1≤n)
        (λ 1≐1+n 𝑖 → *.inc-β x 𝑖 1≐1+n)

    opaque
      match : ≤-MatchP cases
      match = ≤-matchP cases

    open ≤-MatchP match public renaming (match to inc-β)

  open inc-β public using (inc-β)

  module ext-β (Γ : Con) (A : Ty Γ) where
    cases : ≤-CasesP (1 + A .height) n
    cases =
      mk-≤-CasesP
        (λ 1+A≤1+n →
          indCon (ext Γ A) 1+A≤1+n ≡
          M.ext
            (indCon Γ (≤-step ◂ A .lbound ◂ ≤-step ◂ 1+A≤1+n))
            (indTy A (≤-step ◂ 1+A≤1+n)))
        {!!}
        {!!}
        {!!}
        {!!}
