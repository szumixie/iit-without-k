open import IITWithoutK.Prelude
open import IITWithoutK.ConTy.Syntax
open import IITWithoutK.ConTy.DAlg
open import IITWithoutK.ConTy.DAlg.Bounded

module IITWithoutK.ConTy.Ind (M : DAlg) where

import IITWithoutK.ConTy.Ind.Bounded M as B

private
  module M = DAlg M

module indCon (Γ : Con) where
  alg : ≤-Lim-AlgP
  alg =
    mk-≤-Lim-Alg
      (heightCon Γ)
      (λ p → ¬suc≤0 (lboundCon Γ ◂ p))
      (M.Con Γ)
      (λ n p i j → M.Con Γ)
      (λ n p i → B.lower.indCon n i Γ p)

  opaque
    lim : ≤-LimP alg
    lim = ≤-limP alg

  open ≤-LimP lim public renaming (lim to indCon)

open indCon public using (indCon)

module indTy {Γ} (A : Ty Γ) where
  alg : ≤-Lim-AlgP
  alg =
    mk-≤-Lim-Alg
      (heightTy A)
      (λ p → ¬suc≤0 (lboundTy A ◂ p))
      (M.Ty (indCon Γ) A)
      (λ n p i j → M.Ty (indCon.proj-lower Γ n (≤-step ◂ lboundTy A ◂ p) i j) A)
      (λ n p i → B.lower.indTy n i A p)

  opaque
    lim : ≤-LimP alg
    lim = ≤-limP alg

  open ≤-LimP lim public renaming (lim to indTy)

open indTy public using (indTy)

module nil-β where
  alg : ≤-Lim-AlgP
  alg =
    mk-≤-Lim-Alg
      1
      (λ ())
      (indCon nil ≡ M.nil)
      (λ n p i j → indCon.proj-lower nil n p i j ≡ M.nil)
      (λ n p i j → B.lower.nil-β n i j p)

  opaque
    lim : ≤-LimP alg
    lim = ≤-limP alg

  open ≤-LimP lim public renaming (lim to nil-β)

open nil-β public using (nil-β)

module ext-β (Γ : Con) (A : Ty Γ) where
  alg : ≤-Lim-AlgP
  alg =
    mk-≤-Lim-Alg
      (1 + heightTy A)
      (λ ())
      (indCon (ext Γ A) ≡ M.ext (indCon Γ) (indTy A))
      (λ n p i j →
        indCon.proj-lower (ext Γ A) n p i j ≡
        M.ext
          (indCon.proj-lower Γ n (≤-step ◂ lboundTy A ◂ ≤-step ◂ p) i j)
          (indTy.proj-lower A n (≤-step ◂ p) i j))
      (λ n p i j → B.lower.ext-β n i Γ A j p)

  opaque
    lim : ≤-LimP alg
    lim = ≤-limP alg

  open ≤-LimP lim public renaming (lim to ext-β)

open ext-β public using (ext-β)

module univ-β (Γ : Con) where
  alg : ≤-Lim-AlgP
  alg =
    mk-≤-Lim-Alg
      (1 + heightCon Γ)
      (λ ())
      (indTy (univ Γ) ≡ M.univ (indCon Γ))
      (λ n p i j →
        indTy.proj-lower (univ Γ) n p i j ≡
        M.univ (indCon.proj-lower Γ n (≤-step ◂ p) i j))
      (λ n p i j → B.lower.univ-β n i Γ j p)

  opaque
    lim : ≤-LimP alg
    lim = ≤-limP alg

  open ≤-LimP lim public renaming (lim to univ-β)

open univ-β public using (univ-β)

ext-univ-β : ∀ Γ i → _
ext-univ-β Γ i =
  hcomp
    (λ where
      j (i = i0) → indCon (ext Γ (univ Γ))
      j (i = i1) → M.ext (indCon Γ) (univ-β Γ j))
    (ext-β Γ (univ Γ) i)

ext-univ-β-proj-lower : ∀ Γ n p i j k → _
ext-univ-β-proj-lower Γ n p i j k =
  hcomp
    (λ where
      l (k = i0) → indCon.proj-lower (ext Γ (univ Γ)) n p i j
      l (k = i1) →
        M.ext
          (indCon.proj-lower Γ n (≤-steps 2 ◂ p) i j)
          (univ-β.proj-lower Γ n (≤-step ◂ p) i j l))
    (ext-β.proj-lower Γ (univ Γ) n p i j k)

module el-β (Γ : Con) where
  alg : ≤-Lim-AlgP
  alg =
    mk-≤-Lim-Alg
      (3 + heightCon Γ)
      (λ ())
      (indTy (el Γ) ≡ M.el# (indCon Γ) (λ i → ext-univ-β Γ i))
      (λ n p i j →
        indTy.proj-lower (el Γ) n p i j ≡
        M.el#
          (indCon.proj-lower Γ n (≤-steps 3 ◂ p) i j)
          (λ k → ext-univ-β-proj-lower Γ n (≤-step ◂ p) i j k))
      (λ n p i j → B.lower.el-β n i Γ j p)

  opaque
    lim : ≤-LimP alg
    lim = ≤-limP alg

  open ≤-LimP lim public renaming (lim to el-β)

open el-β public using (el-β)

indTy-ext : ∀ {Γ A} B → _
indTy-ext {Γ} {A} B = transport (λ i → M.Ty (ext-β Γ A i) B) (indTy B)

indTy-ext-proj-lower : ∀ {Γ A} B n p i j → _
indTy-ext-proj-lower {Γ} {A} B n p i j =
  transport
    (λ k → M.Ty (ext-β.proj-lower Γ A n (≤-step ◂ lboundTy B ◂ p) i j k) B)
    (indTy.proj-lower B n p i j)

module pi-β (Γ : Con) (A : Ty Γ) (B : Ty (ext Γ A)) where
  alg : ≤-Lim-AlgP
  alg =
    mk-≤-Lim-Alg
      (1 + heightTy B)
      (λ ())
      (indTy (pi Γ A B) ≡ M.pi (indCon Γ) (indTy A) (indTy-ext B))
      (λ n p i j →
        indTy.proj-lower (pi Γ A B) n p i j ≡
        M.pi
          (indCon.proj-lower Γ n
            (≤-step ◂ lboundTy A ◂ ≤-steps 2 ◂ lboundTy B ◂ ≤-step ◂ p)
            i j)
          (indTy.proj-lower A n (≤-steps 2 ◂ lboundTy B ◂ ≤-step ◂ p) i j)
          (indTy-ext-proj-lower B n (≤-step ◂ p) i j))
      (λ n p i j → B.lower.pi-β n i Γ A B j p)

  opaque
    lim : ≤-LimP alg
    lim = ≤-limP alg

  open ≤-LimP lim public renaming (lim to pi-β)

open pi-β public using (pi-β)

ind : Ind M
ind .Ind.indCon = indCon
ind .Ind.indTy = indTy

ind .Ind.nil-β = nil-β
ind .Ind.ext-β = ext-β

ind .Ind.univ-β = univ-β
ind .Ind.el-β = el-β
ind .Ind.pi-β = pi-β

proj-ind : ∀ n → projBounded n ind ≡ B.ind n
proj-ind n i .Ind.indCon Γ p = indCon.proj Γ n p i
proj-ind n i .Ind.indTy A p = indTy.proj A n p i

proj-ind n i .Ind.nil-β j p = nil-β.proj n p i j
proj-ind n i .Ind.ext-β Γ A j p = ext-β.proj Γ A n p i j

proj-ind n i .Ind.univ-β Γ j p = univ-β.proj Γ n p i j
proj-ind n i .Ind.el-β Γ j p = el-β.proj Γ n p i j
proj-ind n i .Ind.pi-β Γ A B j p = pi-β.proj Γ A B n p i j

lower-proj-ind :
  ∀ n →
  Square
    (λ j → lowerBounded (proj-ind (1 + n) j))
    (λ j → proj-ind n j)
    (lowerProjBounded n ind)
    (B.lower-ind n)
lower-proj-ind n i j .Ind.indCon Γ p = indCon.proj-lower Γ n p i j
lower-proj-ind n i j .Ind.indTy A p = indTy.proj-lower A n p i j

lower-proj-ind n i j .Ind.nil-β k p = nil-β.proj-lower n p i j k
lower-proj-ind n i j .Ind.ext-β Γ A k p = ext-β.proj-lower Γ A n p i j k

lower-proj-ind n i j .Ind.univ-β Γ k p = univ-β.proj-lower Γ n p i j k
lower-proj-ind n i j .Ind.el-β Γ k p = el-β.proj-lower Γ n p i j k
lower-proj-ind n i j .Ind.pi-β Γ A B k p = pi-β.proj-lower Γ A B n p i j k
