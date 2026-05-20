open import IITWithoutK.Prelude
open import IITWithoutK.ConTy.Syntax
open import IITWithoutK.ConTy.Syntax.Match
open import IITWithoutK.ConTy.DAlg
open import IITWithoutK.ConTy.DAlg.Bounded

module IITWithoutK.ConTy.Ind.Bounded (M : DAlg) where

private
  module M = DAlg M

ind₀ : Ind (Bounded 0 M)
ind₀ .Ind.indCon Γ p = ⊥-rec (¬suc≤0 (lboundCon Γ ◂ p))
ind₀ .Ind.indTy A p = ⊥-rec (¬suc≤0 (lboundTy A ◂ p))

ind₀ .Ind.nil-β i ()
ind₀ .Ind.ext-β Γ A i ()

ind₀ .Ind.univ-β Γ i ()
ind₀ .Ind.el-β Γ i ()
ind₀ .Ind.pi-β Γ A B i ()

module Ind₊ {n} (B : Ind (Bounded n M)) where
  private
    module B = Ind B

  E : MAlg
  E .MAlg.Con Γ = heightCon Γ ≐ 1 + n → M.Con Γ
  E .MAlg.Ty {Γ} A =
    (p : heightTy A ≐ 1 + n) →
    M.Ty (B.indCon Γ (≤-unsuc (lboundTy A ◂ ≐→≤ p))) A

  E .MAlg.nil p = M.nil
  E .MAlg.ext Γ A p =
    M.ext
      (B.indCon Γ (≤-step ◂ lboundTy A ◂ ≤-unsuc (≐→≤ p)))
      (B.indTy A (≤-unsuc (≐→≤ p)))

  E .MAlg.univ Γ p = M.univ (B.indCon Γ (≤-unsuc (≐→≤ p)))
  E .MAlg.el Γ p =
    M.el#
      (B.indCon Γ (≤-steps 2 ◂ ≤-unsuc (≐→≤ p)))
      (λ i → B.ext-univ-β Γ i (≤-unsuc (≐→≤ p)))
  E .MAlg.pi Γ A B p =
    M.pi
      (B.indCon Γ
        (≤-step ◂ lboundTy A ◂ ≤-steps 2 ◂ lboundTy B ◂ ≤-unsuc (≐→≤ p)))
      (B.indTy A (≤-steps 2 ◂ lboundTy B ◂ ≤-unsuc (≐→≤ p)))
      (B.indTy-ext B (≤-unsuc (≐→≤ p)))

  module E = Match E

  module indCon (Γ : Con) where
    alg : ≤-MAlgP (heightCon Γ) n
    alg =
      mk-≤-MAlgP
        (λ p → M.Con Γ)
        (λ p i → M.Con Γ)
        (λ p i → M.Con Γ)
        (λ p → B.indCon Γ p)
        (λ p → E.matchCon Γ p)

    opaque
      match : ≤-MatchP alg
      match = ≤-matchP alg

    open ≤-MatchP match public renaming (match to indCon)

  open indCon public using (indCon)

  module indTy {Γ} (A : Ty Γ) where
    alg : ≤-MAlgP (heightTy A) n
    alg =
      mk-≤-MAlgP
        (λ p → M.Ty (indCon Γ (≤-step ◂ lboundTy A ◂ p)) A)
        (λ p i → M.Ty (indCon.lt-β Γ (≤-step ◂ lboundTy A ◂ p) i) A)
        (λ p i → M.Ty (indCon.lt-β Γ (≤-unsuc (lboundTy A ◂ ≐→≤ p)) i) A)
        (λ p → B.indTy A p)
        (λ p → E.matchTy A p)

    opaque
      match : ≤-MatchP alg
      match = ≤-matchP alg

    open ≤-MatchP match public renaming (match to indTy)

  open indTy public using (indTy)

  module nil-β where
    alg : ≤-MAlgP 1 n
    alg =
      mk-≤-MAlgP
        (λ p → indCon nil p ≡ M.nil)
        (λ p i → indCon.lt-β nil p i ≡ M.nil)
        (λ p i → indCon.eq-β nil p i ≡ M.nil)
        (λ p i → B.nil-β i p)
        (λ p i → E.nil-β i p)

    opaque
      match : ≤-MatchP alg
      match = ≤-matchP alg

    open ≤-MatchP match public renaming (match to nil-β)

  open nil-β public using (nil-β)

  module ext-β (Γ : Con) (A : Ty Γ) where
    alg : ≤-MAlgP (1 + heightTy A) n
    alg =
      mk-≤-MAlgP
        (λ p →
          indCon (ext Γ A) p ≡
          M.ext
            (indCon Γ (≤-step ◂ lboundTy A ◂ ≤-step ◂ p))
            (indTy A (≤-step ◂ p)))
        (λ p i →
          indCon.lt-β (ext Γ A) p i ≡
          M.ext
            (indCon.lt-β Γ (≤-step ◂ lboundTy A ◂ ≤-step ◂ p) i)
            (indTy.lt-β A (≤-step ◂ p) i))
        (λ p i →
          indCon.eq-β (ext Γ A) p i ≡
          M.ext
            (indCon.lt-β Γ (≤-step ◂ lboundTy A ◂ ≤-unsuc (≐→≤ p)) i)
            (indTy.lt-β A (≤-unsuc (≐→≤ p)) i))
        (λ p i → B.ext-β Γ A i p)
        (λ p i → E.ext-β Γ A i p)

    opaque
      match : ≤-MatchP alg
      match = ≤-matchP alg

    open ≤-MatchP match public renaming (match to ext-β)

  open ext-β public using (ext-β)

  module univ-β (Γ : Con) where
    alg : ≤-MAlgP (1 + heightCon Γ) n
    alg =
      mk-≤-MAlgP
        (λ p →
          indTy (univ Γ) p ≡ M.univ (indCon Γ (≤-step ◂ p)))
        (λ p i →
          indTy.lt-β (univ Γ) p i ≡ M.univ (indCon.lt-β Γ (≤-step ◂ p) i))
        (λ p i →
          indTy.eq-β (univ Γ) p i ≡ M.univ (indCon.lt-β Γ (≤-unsuc (≐→≤ p)) i))
        (λ p i → B.univ-β Γ i p)
        (λ p i → E.univ-β Γ i p)

    opaque
      match : ≤-MatchP alg
      match = ≤-matchP alg

    open ≤-MatchP match public renaming (match to univ-β)

  open univ-β public using (univ-β)

  ext-univ-β : ∀ Γ p i → _
  ext-univ-β Γ p i =
    hcomp
      (λ where
        j (i = i0) → indCon (ext Γ (univ Γ)) p
        j (i = i1) →
          M.ext (indCon Γ (≤-steps 2 ◂ p)) (univ-β Γ (≤-step ◂ p) j))
      (ext-β Γ (univ Γ) p i)

  ext-univ-β-lt-β : ∀ Γ p i j → _
  ext-univ-β-lt-β Γ p i j =
    hcomp
      (λ where
        k (j = i0) → indCon.lt-β (ext Γ (univ Γ)) p i
        k (j = i1) →
          M.ext
            (indCon.lt-β Γ (≤-steps 2 ◂ p) i)
            (univ-β.lt-β Γ (≤-step ◂ p) i k))
      (ext-β.lt-β Γ (univ Γ) p i j)

  module el-β (Γ : Con) where
    alg : ≤-MAlgP (3 + heightCon Γ) n
    alg =
      mk-≤-MAlgP
        (λ p →
          indTy (el Γ) p ≡
          M.el#
            (indCon Γ (≤-steps 3 ◂ p))
            (λ i → ext-univ-β Γ (≤-step ◂ p) i))
        (λ p i →
          indTy.lt-β (el Γ) p i ≡
          M.el#
            (indCon.lt-β Γ (≤-steps 3 ◂ p) i)
            (λ j → ext-univ-β-lt-β Γ (≤-step ◂ p) i j))
        (λ p i →
          indTy.eq-β (el Γ) p i ≡
          M.el#
            (indCon.lt-β Γ (≤-steps 2 ◂ ≤-unsuc (≐→≤ p)) i)
            (λ j → ext-univ-β-lt-β Γ (≤-unsuc (≐→≤ p)) i j))
        (λ p i → B.el-β Γ i p)
        (λ p i → E.el-β Γ i p)

    opaque
      match : ≤-MatchP alg
      match = ≤-matchP alg

    open ≤-MatchP match public renaming (match to el-β)

  open el-β public using (el-β)

  indTy-ext : ∀ {Γ A} B p → _
  indTy-ext {Γ} {A} B p =
    transport
      (λ i → M.Ty (ext-β Γ A (≤-step ◂ lboundTy B ◂ p) i) B)
      (indTy B p)

  indTy-ext-lt-β : ∀ {Γ A} B p i → _
  indTy-ext-lt-β {Γ} {A} B p i =
    transport
      (λ j → M.Ty (ext-β.lt-β Γ A (≤-step ◂ lboundTy B ◂ p) i j) B)
      (indTy.lt-β B p i)

  module pi-β (Γ : Con) (A : Ty Γ) (B : Ty (ext Γ A)) where
    alg : ≤-MAlgP (1 + heightTy B) n
    alg =
      mk-≤-MAlgP
        (λ p →
          indTy (pi Γ A B) p ≡
          M.pi
            (indCon Γ
              (≤-step ◂ lboundTy A ◂ ≤-steps 2 ◂ lboundTy B ◂ ≤-step ◂ p))
            (indTy A (≤-steps 2 ◂ lboundTy B ◂ ≤-step ◂ p))
            (indTy-ext B (≤-step ◂ p)))
        (λ p i →
          indTy.lt-β (pi Γ A B) p i ≡
          M.pi
            (indCon.lt-β Γ
              (≤-step ◂ lboundTy A ◂ ≤-steps 2 ◂ lboundTy B ◂ ≤-step ◂ p)
              i)
            (indTy.lt-β A (≤-steps 2 ◂ lboundTy B ◂ ≤-step ◂ p) i)
            (indTy-ext-lt-β B (≤-step ◂ p) i))
        (λ p i →
          indTy.eq-β (pi Γ A B) p i ≡
          M.pi
            (indCon.lt-β Γ
              (≤-step ◂ lboundTy A ◂ ≤-steps 2 ◂ lboundTy B ◂ ≤-unsuc (≐→≤ p))
              i)
            (indTy.lt-β A (≤-steps 2 ◂ lboundTy B ◂ ≤-unsuc (≐→≤ p)) i)
            (indTy-ext-lt-β B (≤-unsuc (≐→≤ p)) i))
        (λ p i → B.pi-β Γ A B i p)
        (λ p i → E.pi-β Γ A B i p)

    opaque
      match : ≤-MatchP alg
      match = ≤-matchP alg

    open ≤-MatchP match public renaming (match to pi-β)

  open pi-β public using (pi-β)

  ind₊ : Ind (Bounded (1 + n) M)
  ind₊ .Ind.indCon Γ p = indCon Γ p
  ind₊ .Ind.indTy A p = indTy A p

  ind₊ .Ind.nil-β i p = nil-β p i
  ind₊ .Ind.ext-β Γ A i p = ext-β Γ A p i

  ind₊ .Ind.univ-β Γ i p = univ-β Γ p i
  ind₊ .Ind.el-β Γ i p = el-β Γ p i
  ind₊ .Ind.pi-β Γ A B i p = pi-β Γ A B p i

  lower-ind₊ : lowerBounded ind₊ ≡ B
  lower-ind₊ i .Ind.indCon Γ p = indCon.lt-β Γ p i
  lower-ind₊ i .Ind.indTy A p = indTy.lt-β A p i

  lower-ind₊ i .Ind.nil-β j p = nil-β.lt-β p i j
  lower-ind₊ i .Ind.ext-β Γ A j p = ext-β.lt-β Γ A p i j

  lower-ind₊ i .Ind.univ-β Γ j p = univ-β.lt-β Γ p i j
  lower-ind₊ i .Ind.el-β Γ j p = el-β.lt-β Γ p i j
  lower-ind₊ i .Ind.pi-β Γ A B j p = pi-β.lt-β Γ A B p i j

open Ind₊ public using (ind₊; lower-ind₊)

opaque
  ind : ∀ n → Ind (Bounded n M)
  ind zero = ind₀
  ind (suc n) = ind₊ (ind n)

  lower-ind : ∀ n → lowerBounded (ind (1 + n)) ≡ ind n
  lower-ind n = lower-ind₊ (ind n)

module _ n where
  open Ind (ind n) public
  module lower i = Ind (lower-ind n i)
