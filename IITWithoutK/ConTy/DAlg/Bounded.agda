module IITWithoutK.ConTy.DAlg.Bounded where

open import IITWithoutK.Prelude
open import IITWithoutK.ConTy.Syntax
open import IITWithoutK.ConTy.DAlg

module _ (n : ℕ) (M : DAlg) where
  private
    module M = DAlg M

  Bounded : DAlg
  Bounded .DAlg.Con Γ = heightCon Γ ≤ n → M.Con Γ
  Bounded .DAlg.Ty Γᴹ A =
    (p : heightTy A ≤ n) → M.Ty (Γᴹ (≤-step ◂ lboundTy A ◂ p)) A

  Bounded .DAlg.nil p = M.nil
  Bounded .DAlg.ext Γᴹ {A} Aᴹ p =
    M.ext (Γᴹ (≤-step ◂ lboundTy A ◂ ≤-step ◂ p)) (Aᴹ (≤-step ◂ p))

  Bounded .DAlg.univ Γᴹ p = M.univ (Γᴹ (≤-step ◂ p))
  Bounded .DAlg.el Γᴹ p = M.el (Γᴹ (≤-steps 3 ◂ p))
  Bounded .DAlg.pi Γᴹ {A} Aᴹ {B} Bᴹ p =
    M.pi
      (Γᴹ (≤-step ◂ lboundTy A ◂ ≤-steps 2 ◂ lboundTy B ◂ ≤-step ◂ p))
      (Aᴹ (≤-steps 2 ◂ lboundTy B ◂ ≤-step ◂ p))
      (Bᴹ (≤-step ◂ p))

module _ {n} {M : DAlg} (B₊ : Ind (Bounded (1 + n) M)) where
  private
    module B₊ = Ind B₊

  lowerBounded : Ind (Bounded n M)
  lowerBounded .Ind.indCon Γ p = B₊.indCon Γ (p ◂ ≤-step)
  lowerBounded .Ind.indTy A p = B₊.indTy A (p ◂ ≤-step)

  lowerBounded .Ind.nil-β i p = B₊.nil-β i (p ◂ ≤-step)
  lowerBounded .Ind.ext-β Γ A i p = B₊.ext-β Γ A i (p ◂ ≤-step)

  lowerBounded .Ind.univ-β Γ i p = B₊.univ-β Γ i (p ◂ ≤-step)
  lowerBounded .Ind.el-β Γ i p = B₊.el-β Γ i (p ◂ ≤-step)
  lowerBounded .Ind.pi-β Γ A B i p = B₊.pi-β Γ A B i (p ◂ ≤-step)

module _ (n : ℕ) {M : DAlg} (F : Ind M) where
  private
    module F = Ind F

  projBounded : Ind (Bounded n M)
  projBounded .Ind.indCon Γ p = F.indCon Γ
  projBounded .Ind.indTy A p = F.indTy A

  projBounded .Ind.nil-β i p = F.nil-β i
  projBounded .Ind.ext-β Γ A i p = F.ext-β Γ A i

  projBounded .Ind.univ-β Γ i p = F.univ-β Γ i
  projBounded .Ind.el-β Γ i p = F.el-β Γ i
  projBounded .Ind.pi-β Γ A B i p = F.pi-β Γ A B i

module _ (n : ℕ) {M : DAlg} (F : Ind M) where
  private
    module F = Ind F

  lowerProjBounded : lowerBounded (projBounded (1 + n) F) ≡ projBounded n F
  lowerProjBounded i .Ind.indCon Γ p = F.indCon Γ
  lowerProjBounded i .Ind.indTy A p = F.indTy A

  lowerProjBounded i .Ind.nil-β j p = F.nil-β j
  lowerProjBounded i .Ind.ext-β Γ A j p = F.ext-β Γ A j

  lowerProjBounded i .Ind.univ-β Γ j p = F.univ-β Γ j
  lowerProjBounded i .Ind.el-β Γ j p = F.el-β Γ j
  lowerProjBounded i .Ind.pi-β Γ A B j p = F.pi-β Γ A B j
