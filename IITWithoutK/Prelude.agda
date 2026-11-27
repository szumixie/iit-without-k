module IITWithoutK.Prelude where

open import Cubical.Foundations.Prelude public hiding (lower)
open import Cubical.Data.Unit public using (tt) renaming (Unit to ⊤)
open import Cubical.Data.Empty public using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Nat public using (ℕ; zero; suc; _+_)

record TransportFiller (A : I → Type) (a₀ : A i0) : Type where
  field
    {end} : A i1
    filler : PathP A a₀ end

transport-fill : ∀ A a₀ → TransportFiller A a₀
transport-fill A a₀ = record { filler = transport-filler (λ 𝑖 → A 𝑖) a₀ }

_≤ᵣ_ : ℕ → ℕ → Type
zero ≤ᵣ n = ⊤
suc m ≤ᵣ zero = ⊥
suc m ≤ᵣ suc n = m ≤ᵣ n

infix 4 _≤_
record _≤_ (m n : ℕ) : Type where
  eta-equality
  constructor mk-≤
  field
    .witness : m ≤ᵣ n

open _≤_

0-least : ∀ {n} → zero ≤ n
0-least = mk-≤ tt

≤-suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
≤-suc (mk-≤ m≤n) = mk-≤ m≤n

¬suc≤0 : ∀ {n} → suc n ≤ zero → ⊥
¬suc≤0 ()

≤-unsuc : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-unsuc (mk-≤ m≤n) = mk-≤ m≤n

≤-refl : ∀ {n} → n ≤ n
≤-refl {(zero)} = 0-least
≤-refl {suc n} = ≤-suc ≤-refl

infixr 30 _◂_
_◂_ : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
_◂_ {(zero)} {m} {n} 0≤m m≤n = 0-least
_◂_ {suc l} {suc m} {suc n} 1+l≤1+m 1+m≤1+n =
  ≤-suc (≤-unsuc 1+l≤1+m ◂ ≤-unsuc 1+m≤1+n)

≤-step : ∀ {n} → n ≤ suc n
≤-step {(zero)} = 0-least
≤-step {suc n} = ≤-suc ≤-step

≤-steps : ∀ m {n} → n ≤ m + n
≤-steps zero = ≤-refl
≤-steps (suc m) = ≤-steps m ◂ ≤-step

infixl 6 _⊔_
_⊔_ : ℕ → ℕ → ℕ
zero ⊔ zero = zero
zero ⊔ suc n = suc n
suc m ⊔ zero = suc m
suc m ⊔ suc n = suc (m ⊔ n)

⊔-inₗ : ∀ m n → m ≤ m ⊔ n
⊔-inₗ zero zero = 0-least
⊔-inₗ zero (suc n) = 0-least
⊔-inₗ (suc m) zero = ≤-refl
⊔-inₗ (suc m) (suc n) = ≤-suc (⊔-inₗ _ _)

⊔-inᵣ : ∀ m n → n ≤ m ⊔ n
⊔-inᵣ zero zero = 0-least
⊔-inᵣ zero (suc n) = ≤-refl
⊔-inᵣ (suc m) zero = 0-least
⊔-inᵣ (suc m) (suc n) = ≤-suc (⊔-inᵣ _ _)

⊔-least : ∀ {k m n} → k ≤ n → m ≤ n → k ⊔ m ≤ n
⊔-least {(zero)} {(zero)} p q = 0-least
⊔-least {(zero)} {suc m} p q = q
⊔-least {suc k} {(zero)} p q = p
⊔-least {suc k} {suc m} {suc n} p q = ≤-suc (⊔-least (≤-unsuc p) (≤-unsuc q))

infix 4 _≐_
record _≐_ (m n : ℕ) : Type where
  eta-equality
  constructor mk-≐
  field
    le : m ≤ n
    ge : n ≤ m

≐-suc : ∀ {m n} → m ≐ n → suc m ≐ suc n
≐-suc (mk-≐ m≤n n≤m) = mk-≐ (≤-suc m≤n) (≤-suc n≤m)

≐-unsuc : ∀ {m n} → suc m ≐ suc n → m ≐ n
≐-unsuc (mk-≐ 1+m≤1+n 1+n≤1+m) = mk-≐ (≤-unsuc 1+m≤1+n) (≤-unsuc 1+n≤1+m)

≐-refl : ∀ {n} → n ≐ n
≐-refl = mk-≐ ≤-refl ≤-refl

≐→≤ : ∀ {m n} → m ≐ n → m ≤ n
≐→≤ (mk-≐ m≤n n≤m) = m≤n

≐→≡ : ∀ {m n} → m ≐ n → m ≡ n
≐→≡ {(zero)} {(zero)} 0≐0 𝑖 = zero
≐→≡ {suc m} {suc n} 1+m≐1+n 𝑖 = suc (≐→≡ (≐-unsuc 1+m≐1+n) 𝑖)

≐→≤-filler : ∀ {m n} (m≐n : m ≐ n) 𝑖 → m ≤ ≐→≡ m≐n 𝑖
≐→≤-filler {m} m≐n 𝑖 = transport-filler (λ 𝑖 → m ≤ ≐→≡ m≐n 𝑖) ≤-refl 𝑖

record ≤-Cases (m n : ℕ) : Type where
  constructor mk-≤-Cases
  field
    T : m ≤ suc n → Type
    lt : (m≤n : m ≤ n) → T (m≤n ◂ ≤-step)
    eq : (m≐1+n : m ≐ suc n) → T (≐→≤ m≐1+n)

module _ {m n} (M : ≤-Cases (suc m) (suc n)) where
  open ≤-Cases M

  lower-≤-Cases : ≤-Cases m n
  lower-≤-Cases .≤-Cases.T m≤1+n = T (≤-suc m≤1+n)
  lower-≤-Cases .≤-Cases.lt m≤n = lt (≤-suc m≤n)
  lower-≤-Cases .≤-Cases.eq m≤1+n = eq (≐-suc m≤1+n)

record ≤-Match {m n} (M : ≤-Cases m n) : Type where
  open ≤-Cases M
  field
    match : ∀ m≤1+n → T m≤1+n
    lt-β : ∀ m≤n → match (m≤n ◂ ≤-step) ≡ lt m≤n
    eq-β : ∀ m≐1+n → match (≐→≤ m≐1+n) ≡ eq m≐1+n

module _ {m n} (M : ≤-Cases (suc m) (suc n)) (F : ≤-Match (lower-≤-Cases M))
  where
  open ≤-Match F

  unlower-≤-Match : ≤-Match M
  unlower-≤-Match .≤-Match.match m≤1+n = match (≤-unsuc m≤1+n)
  unlower-≤-Match .≤-Match.lt-β m≤n = lt-β (≤-unsuc m≤n)
  unlower-≤-Match .≤-Match.eq-β m≐1+n = eq-β (≐-unsuc m≐1+n)

≤-match : ∀ {m n} (M : ≤-Cases m n) → ≤-Match M
≤-match {suc m} {suc n} M = unlower-≤-Match M (≤-match (lower-≤-Cases M))
≤-match {suc (suc m)} {(zero)} M = λ where .≤-Match.match ()
≤-match {suc zero} {(zero)} M =
  λ where
    .≤-Match.match 1≤1 → eq ≐-refl
    .≤-Match.eq-β 1≐1 → refl
  where
  open ≤-Cases M
≤-match {(zero)} {(n)} M =
  λ where
    .≤-Match.match 0≤1+n → lt 0-least
    .≤-Match.lt-β 0≤n → refl
  where
  open ≤-Cases M

record ≤-CasesP (m n : ℕ) : Type where
  constructor mk-≤-CasesP
  field
    {T-lt} : m ≤ n → Type
    {T-eq} : m ≐ suc n → Type

    T : m ≤ suc n → Type
    T-lt-β : ∀ m≤n → T (m≤n ◂ ≤-step) ≡ T-lt m≤n
    T-eq-β : ∀ m≐1+n → T (≐→≤ m≐1+n) ≡ T-eq m≐1+n

    lt : ∀ m≤n → T-lt m≤n
    eq : ∀ m≐1+n → T-eq m≐1+n

record ≤-MatchP {m n} (M : ≤-CasesP m n) : Type where
  open ≤-CasesP M
  field
    match : ∀ m≤1+n → T m≤1+n
    lt-β : ∀ m≤n → PathP (λ 𝑖 → T-lt-β m≤n 𝑖) (match (m≤n ◂ ≤-step)) (lt m≤n)
    eq-β : ∀ m≐1+n → PathP (λ 𝑖 → T-eq-β m≐1+n 𝑖) (match (≐→≤ m≐1+n)) (eq m≐1+n)

module ≤-matchP {m n} (M : ≤-CasesP m n) where
  open ≤-CasesP M

  match-lt : (m≤n : m ≤ n) → T (m≤n ◂ ≤-step)
  match-lt m≤n = filler i1
    module match-lt where
    filler : ∀ 𝑖 → _
    filler 𝑖 = transport-filler (λ 𝑖 → T-lt-β m≤n (~ 𝑖)) (lt m≤n) 𝑖

  match-eq : (m≐1+n : m ≐ suc n) → T (≐→≤ m≐1+n)
  match-eq m≐1+n = filler i1
    module match-eq where
    filler : ∀ 𝑖 → _
    filler 𝑖 = transport-filler (λ 𝑖 → T-eq-β m≐1+n (~ 𝑖)) (eq m≐1+n) 𝑖

  module match = ≤-Match (≤-match (mk-≤-Cases T match-lt match-eq))
  open match using (match)

  ≤-matchP : ≤-MatchP M
  ≤-matchP .≤-MatchP.match = match
  ≤-matchP .≤-MatchP.lt-β m≤n 𝑖 =
    comp
      (λ 𝑗 → T-lt-β m≤n (𝑖 ∧ 𝑗))
      (λ where
        𝑗 (𝑖 = i0) → match (m≤n ◂ ≤-step)
        𝑗 (𝑖 = i1) → match-lt.filler m≤n (~ 𝑗))
      (match.lt-β m≤n 𝑖)
  ≤-matchP .≤-MatchP.eq-β m≐1+n 𝑖 =
    comp
      (λ 𝑗 → T-eq-β m≐1+n (𝑖 ∧ 𝑗))
      (λ where
        𝑗 (𝑖 = i0) → match (≐→≤ m≐1+n)
        𝑗 (𝑖 = i1) → match-eq.filler m≐1+n (~ 𝑗))
      (match.eq-β m≐1+n 𝑖)

open ≤-matchP public using (≤-matchP)

record ≤-LimDiagP : Type where
  constructor mk-≤-LimDiagP
  field
    h : ℕ
    ¬h≤0 : h ≤ 0 → ⊥

    {Tᴮ} : ∀ n → h ≤ n → Type
    {T-lower} : ∀ n h≤n → Tᴮ (suc n) (h≤n ◂ ≤-step) ≡ Tᴮ n h≤n

    T : Type
    {T-proj} : ∀ n h≤n → T ≡ Tᴮ n h≤n
    T-lower-proj :
      ∀ n h≤n →
      Square (T-proj (suc n) (h≤n ◂ ≤-step)) (T-proj n h≤n) refl (T-lower n h≤n)

    {tᴮ} : ∀ n h≤n → Tᴮ n h≤n
    lower :
      ∀ n h≤n →
      PathP (λ 𝑖 → T-lower n h≤n 𝑖) (tᴮ (suc n) (h≤n ◂ ≤-step)) (tᴮ n h≤n)

record ≤-LimP (M : ≤-LimDiagP) : Type where
  open ≤-LimDiagP M
  field
    lim : T
    proj : ∀ n h≤n → PathP (λ 𝑖 → T-proj n h≤n 𝑖) lim (tᴮ n h≤n)
    lower-proj :
      ∀ n h≤n →
      SquareP
        (λ 𝑖 𝑗 → T-lower-proj n h≤n 𝑖 𝑗)
        (proj (suc n) (h≤n ◂ ≤-step))
        (proj n h≤n)
        refl
        (lower n h≤n)

module ≤-limP (M : ≤-LimDiagP) where
  open ≤-LimDiagP M

  lim : T
  lim = filler i1
    module lim where
    filler : ∀ 𝑖 → _
    filler 𝑖 = transport-filler (λ 𝑖 → T-proj h ≤-refl (~ 𝑖)) (tᴮ h ≤-refl) 𝑖

  proj₊-eq :
    ∀ n h≐1+n →
    PathP (λ 𝑖 → T-proj (suc n) (≐→≤ h≐1+n) 𝑖) lim (tᴮ (suc n) (≐→≤ h≐1+n))
  proj₊-eq n h≐1+n 𝑖 =
    comp
      (λ 𝑗 → T-proj (≐→≡ h≐1+n 𝑗) (≐→≤-filler h≐1+n 𝑗) 𝑖)
      (λ where
        𝑗 (𝑖 = i0) → lim
        𝑗 (𝑖 = i1) → tᴮ (≐→≡ h≐1+n 𝑗) (≐→≤-filler h≐1+n 𝑗))
      (lim.filler (~ 𝑖))

  proj : ∀ n h≤n → PathP (λ 𝑖 → T-proj n h≤n 𝑖) lim (tᴮ n h≤n)
  proj₊ :
    ∀ n h≤1+n → PathP (λ 𝑖 → T-proj (suc n) h≤1+n 𝑖) lim (tᴮ (suc n) h≤1+n)
  proj₊-lt :
    ∀ n h≤n →
    PathP (λ 𝑖 → T-proj (suc n) (h≤n ◂ ≤-step) 𝑖)
      lim (tᴮ (suc n) (h≤n ◂ ≤-step))

  proj zero h≤0 = ⊥-rec (¬h≤0 h≤0)
  proj (suc n) h≤1+n = proj₊ n h≤1+n

  proj₊ n = match
    module proj₊ where
    open ≤-Match
      (≤-match
        (mk-≤-Cases
          (λ h≤1+n →
            PathP (λ 𝑖 → T-proj (suc n) h≤1+n 𝑖) lim (tᴮ (suc n) h≤1+n))
          (proj₊-lt n)
          (proj₊-eq n)))
      public

  proj₊-lt n h≤n = λ 𝑖 → filler i1 𝑖
    module proj₊-lt where
    filler : ∀ 𝑗 𝑖 → _
    filler 𝑗 𝑖 =
      fill
        (λ 𝑗 → T-lower-proj n h≤n (~ 𝑗) 𝑖)
        (λ where
          𝑗 (𝑖 = i0) → lim
          𝑗 (𝑖 = i1) → lower n h≤n (~ 𝑗))
        (inS (proj n h≤n 𝑖))
        𝑗

  lower-proj :
    ∀ n h≤n →
    SquareP
      (λ 𝑖 𝑗 → T-lower-proj n h≤n 𝑖 𝑗)
      (proj (suc n) (h≤n ◂ ≤-step))
      (proj n h≤n)
      refl
      (lower n h≤n)
  lower-proj n h≤n 𝑖 𝑗 =
    comp
      (λ 𝑘 → T-lower-proj n h≤n (𝑖 ∧ 𝑘) 𝑗)
      (λ where
        𝑘 (𝑖 = i0) → proj (suc n) (h≤n ◂ ≤-step) 𝑗
        𝑘 (𝑖 = i1) → proj₊-lt.filler n h≤n (~ 𝑘) 𝑗
        𝑘 (𝑗 = i0) → lim
        𝑘 (𝑗 = i1) → lower n h≤n (𝑖 ∧ 𝑘))
      (proj₊.lt-β n h≤n 𝑖 𝑗)

  ≤-limP : ≤-LimP M
  ≤-limP .≤-LimP.lim = lim
  ≤-limP .≤-LimP.proj = proj
  ≤-limP .≤-LimP.lower-proj = lower-proj

open ≤-limP public using (≤-limP)
