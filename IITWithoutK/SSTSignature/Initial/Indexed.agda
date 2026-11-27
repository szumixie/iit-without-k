module IITWithoutK.SSTSignature.Initial.Indexed where

open import IITWithoutK.Prelude
open import IITWithoutK.SSTSignature.Algebra
import IITWithoutK.SSTSignature.Initial.Bounded as B

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

module nilC where
  diag : ≤-LimDiagP
  diag =
    mk-≤-LimDiagP
      1
      (λ ())
      (Con 1 ≤-refl)
      (λ n 1≤n 𝑖 𝑗 → Con.lower-proj 1 ≤-refl n 1≤n 𝑖 𝑗)
      (λ n 1≤n 𝑖 → B.lower.nilC n 𝑖 1≤n)

  opaque
    lim : ≤-LimP diag
    lim = ≤-limP diag

  open ≤-LimP lim public renaming (lim to nilC)

open nilC public using (nilC)

Init : IAlg
Init .IAlg.Con i 1≤i = Con i 1≤i
Init .IAlg.nilC = nilC

Init-proj : ∀ n → proj-BAlg n Init ≡ B.Init n
Init-proj n 𝑖 .BAlg.Con i 1≤i i≤n = Con.proj i 1≤i n i≤n 𝑖
Init-proj n 𝑖 .BAlg.nilC 1≤n = nilC.proj n 1≤n 𝑖
