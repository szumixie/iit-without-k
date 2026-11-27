open import IITWithoutK.Prelude

module IITWithoutK.OpenExample.Initial.Indexed (X : Type) where

open import IITWithoutK.OpenExample.Algebra X
import IITWithoutK.OpenExample.Initial.Bounded X as B

module Con i (1≤i : 1 ≤ i) where
  diag : ≤-LimDiagP
  diag =
    mk-≤-LimDiagP
      i
      (λ i≤0 → ¬suc≤0 (1≤i ◂ i≤0))
      Type
      (λ n i≤n 𝑖 𝑗 → Type)
      (λ n i≤n 𝑖 → B.lower.Con n 𝑖 i 1≤i i≤n)

  opaque
    lim : ≤-LimP diag
    lim = ≤-limP diag

  open ≤-LimP lim public renaming (lim to Con)

open Con public using (Con)

module Ty {i 1≤i} j (1+i≤j : 1 + i ≤ j) where
  diag : ≤-LimDiagP
  diag =
    mk-≤-LimDiagP
      j
      (λ j≤0 → ¬suc≤0 (1+i≤j ◂ j≤0))
      (Con i 1≤i → Type)
      (λ n j≤n 𝑖 𝑗 → Con.lower-proj i 1≤i n (≤-step ◂ 1+i≤j ◂ j≤n) 𝑖 𝑗 → Type)
      (λ n j≤n 𝑖 → B.lower.Ty n 𝑖 j 1+i≤j j≤n)

  opaque
    lim : ≤-LimP diag
    lim = ≤-limP diag

  open ≤-LimP lim public renaming (lim to Ty)

open Ty public using (Ty)

module inc where
  diag : ≤-LimDiagP
  diag =
    mk-≤-LimDiagP
      1
      (λ ())
      (X → Con 1 ≤-refl)
      (λ n 1≤n 𝑖 𝑗 → X → Con.lower-proj 1 ≤-refl n 1≤n 𝑖 𝑗)
      (λ n 1≤n 𝑖 → B.lower.inc n 𝑖 1≤n)

  opaque
    lim : ≤-LimP diag
    lim = ≤-limP diag

  open ≤-LimP lim public renaming (lim to inc)

open inc public using (inc)

module ext {i 1≤i j 1+i≤j} where
  diag : ≤-LimDiagP
  diag =
    mk-≤-LimDiagP
      (1 + j)
      (λ ())
      ( (Γ : Con i 1≤i) → Ty j 1+i≤j Γ →
        Con (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step))
      (λ n 1+j≤n 𝑖 𝑗 →
        (Γ : Con.lower-proj i 1≤i n (≤-step ◂ 1+i≤j ◂ ≤-step ◂ 1+j≤n) 𝑖 𝑗) →
        Ty.lower-proj j 1+i≤j n (≤-step ◂ 1+j≤n) 𝑖 𝑗 Γ →
        Con.lower-proj (1 + j) (1≤i ◂ ≤-step ◂ 1+i≤j ◂ ≤-step) n 1+j≤n 𝑖 𝑗)
      (λ n 1+j≤n 𝑖 → B.lower.ext n 𝑖 1+j≤n)

  opaque
    lim : ≤-LimP diag
    lim = ≤-limP diag

  open ≤-LimP lim public renaming (lim to ext)

open ext public using (ext)

module base {i 1≤i} where
  diag : ≤-LimDiagP
  diag =
    mk-≤-LimDiagP
      (1 + i)
      (λ ())
      ((Γ : Con i 1≤i) → Ty (1 + i) ≤-refl Γ)
      (λ n 1+i≤n 𝑖 𝑗 →
        (Γ : Con.lower-proj i 1≤i n (≤-step ◂ 1+i≤n) 𝑖 𝑗) →
        Ty.lower-proj (1 + i) ≤-refl n 1+i≤n 𝑖 𝑗 Γ)
      (λ n 1+i≤n 𝑖 → B.lower.base n 𝑖 1+i≤n)

  opaque
    lim : ≤-LimP diag
    lim = ≤-limP diag

  open ≤-LimP lim public renaming (lim to base)

open base public using (base)

Init : IAlg
Init .IAlg.Con i 1≤i = Con i 1≤i
Init .IAlg.Ty j 1+i≤j = Ty j 1+i≤j

Init .IAlg.inc = inc
Init .IAlg.ext = ext
Init .IAlg.base = base

Init-proj : ∀ n → proj-BAlg n Init ≡ B.Init n
Init-proj n 𝑖 .BAlg.Con i 1≤i i≤n = Con.proj i 1≤i n i≤n 𝑖
Init-proj n 𝑖 .BAlg.Ty j 1+i≤j j≤n = Ty.proj j 1+i≤j n j≤n 𝑖

Init-proj n 𝑖 .BAlg.inc 1≤n = inc.proj n 1≤n 𝑖
Init-proj n 𝑖 .BAlg.ext 1+j≤n = ext.proj n 1+j≤n 𝑖
Init-proj n 𝑖 .BAlg.base 1+i≤n = base.proj n 1+i≤n 𝑖

Init-lower-proj :
  ∀ n →
    Square
      (λ 𝑗 → lower-BAlg (Init-proj (1 + n) 𝑗))
      (λ 𝑗 → Init-proj n 𝑗)
      (lower-proj-BAlg n Init)
      (B.Init-lower n)
Init-lower-proj n 𝑖 𝑗 .BAlg.Con i 1≤i i≤n = Con.lower-proj i 1≤i n i≤n 𝑖 𝑗
Init-lower-proj n 𝑖 𝑗 .BAlg.Ty j 1+i≤j j≤n = Ty.lower-proj j 1+i≤j n j≤n 𝑖 𝑗

Init-lower-proj n 𝑖 𝑗 .BAlg.inc 1≤n = inc.lower-proj n 1≤n 𝑖 𝑗
Init-lower-proj n 𝑖 𝑗 .BAlg.ext 1+j≤n = ext.lower-proj n 1+j≤n 𝑖 𝑗
Init-lower-proj n 𝑖 𝑗 .BAlg.base 1+i≤n = base.lower-proj n 1+i≤n 𝑖 𝑗

module proj n 𝑖 = BAlg (Init-proj n 𝑖)
module lower-proj n 𝑖 𝑗 = BAlg (Init-lower-proj n 𝑖 𝑗)
