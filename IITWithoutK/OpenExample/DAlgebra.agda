open import IITWithoutK.Prelude

module IITWithoutK.OpenExample.DAlgebra (X : Type) where

import IITWithoutK.OpenExample.Initial X as S

record DAlg : Type where
  field
    Con : S.Con → Type
    Ty : ∀ {Γ} → Con Γ → S.Ty Γ → Type

    inc : ∀ x → Con (S.inc x)
    ext : ∀ {Γ} (Γᴹ : Con Γ) {A} → Ty Γᴹ A → Con (S.ext Γ A)
    base : ∀ {Γ} (Γᴹ : Con Γ) → Ty Γᴹ (S.base Γ)

record Ind (M : DAlg) : Type where
  open S
  private
    module M = DAlg M

  field
    indCon : (Γ : Con) → M.Con Γ
    indTy : ∀ {Γ} (A : Ty Γ) → M.Ty (indCon Γ) A

    inc-β : ∀ x → indCon (inc x) ≡ M.inc x
    ext-β : ∀ Γ A → indCon (ext Γ A) ≡ M.ext (indCon Γ) (indTy A)
    base-β : ∀ Γ → indTy (base Γ) ≡ M.base (indCon Γ)

module _ (n : ℕ) (M : DAlg) where
  open S
  private
    module M = DAlg M

  Bounded : DAlg
  Bounded .DAlg.Con Γ = Γ .height ≤ n → M.Con Γ
  Bounded .DAlg.Ty {Γ} Γᴹ A =
    (A≤n : A .height ≤ n) → M.Ty (Γᴹ (≤-step ◂ A .lbound ◂ A≤n)) A

  Bounded .DAlg.inc x 1≤n = M.inc x
  Bounded .DAlg.ext {Γ} Γᴹ {A} Aᴹ 1+A≤n =
    M.ext (Γᴹ (≤-step ◂ A .lbound ◂ ≤-step ◂ 1+A≤n)) (Aᴹ (≤-step ◂ 1+A≤n))
  Bounded .DAlg.base {Γ} Γᴹ 1+Γ≤n = M.base (Γᴹ (≤-step ◂ 1+Γ≤n))

module _ {n} {M : DAlg} (F : Ind (Bounded (1 + n) M)) where
  private
    module F = Ind F

  lower-Bounded : Ind (Bounded n M)
  lower-Bounded .Ind.indCon Γ Γ≤n = F.indCon Γ (Γ≤n ◂ ≤-step)
  lower-Bounded .Ind.indTy A A≤n = F.indTy A (A≤n ◂ ≤-step)

  lower-Bounded .Ind.inc-β x 𝑖 1≤n = F.inc-β x 𝑖 (1≤n ◂ ≤-step)
  lower-Bounded .Ind.ext-β Γ A 𝑖 1+A≤n = F.ext-β Γ A 𝑖 (1+A≤n ◂ ≤-step)
  lower-Bounded .Ind.base-β Γ 𝑖 1+Γ≤n = F.base-β Γ 𝑖 (1+Γ≤n ◂ ≤-step)

module _ (n : ℕ) {M : DAlg} (F : Ind M) where
  private
    module F = Ind F

  proj-Bounded : Ind (Bounded n M)
  proj-Bounded .Ind.indCon Γ Γ≤n = F.indCon Γ
  proj-Bounded .Ind.indTy A A≤n = F.indTy A

  proj-Bounded .Ind.inc-β x 𝑖 1≤n = F.inc-β x 𝑖
  proj-Bounded .Ind.ext-β Γ A 𝑖 1+A≤n = F.ext-β Γ A 𝑖
  proj-Bounded .Ind.base-β Γ 𝑖 1+Γ≤n = F.base-β Γ 𝑖

module _ (n : ℕ) {M : DAlg} (F : Ind M) where
  private
    module F = Ind F

  lower-proj-Bounded : lower-Bounded (proj-Bounded (1 + n) F) ≡ proj-Bounded n F
  lower-proj-Bounded 𝑖 .Ind.indCon Γ Γ≤n = F.indCon Γ
  lower-proj-Bounded 𝑖 .Ind.indTy A A≤n = F.indTy A

  lower-proj-Bounded 𝑖 .Ind.inc-β x 𝑗 1≤n = F.inc-β x 𝑗
  lower-proj-Bounded 𝑖 .Ind.ext-β Γ A 𝑗 1+A≤n = F.ext-β Γ A 𝑗
  lower-proj-Bounded 𝑖 .Ind.base-β Γ 𝑗 1+Γ≤n = F.base-β Γ 𝑗
