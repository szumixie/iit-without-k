module IITWithoutK.Prelude where

open import Cubical.Foundations.Prelude public hiding (lower)
open import Cubical.Foundations.HLevels public
open import Cubical.Data.Sigma public using (_×_)
open import Cubical.Data.Unit public
  using (tt) renaming (Unit to ⊤; isPropUnit to isProp⊤)
open import Cubical.Data.Empty public using (⊥; isProp⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Nat public using (ℕ; zero; suc; _+_)

isPropΣ→isProp-snd :
  {A : Type} {B : A → Type} → isSet A → isProp (Σ A B) → ∀ a → isProp (B a)
isPropΣ→isProp-snd {B} isSetA isPropΣ a b₀ b₁ i =
  comp
    (λ j → B (isSetA a a (λ i → isPropΣ (a , b₀) (a , b₁) i .fst) refl j i))
    (λ where
      j (i = i0) → b₀
      j (i = i1) → b₁)
    (isPropΣ (a , b₀) (a , b₁) i .snd)

substProp : {A : Type} → isProp A → (B : A → Type) → ∀ {a₀ a₁} → B a₀ → B a₁
substProp isPropA B {a₀} {a₁} b₀ = filler i1
  module substProp where
  filler : ∀ i → _
  filler i = transport-filler (λ i → B (isPropA a₀ a₁ i)) b₀ i

  filler# : (aᵖ : a₀ ≡ a₁) → PathP (λ i → B (aᵖ i)) b₀ (filler i1)
  filler# aᵖ i =
    comp
      (λ j → B (isProp→isSet isPropA _ _ (isPropA a₀ a₁) aᵖ j i))
      (λ where
        j (i = i0) → b₀
        j (i = i1) → filler i1)
      (filler i)

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
≤-suc (mk-≤ p) = mk-≤ p

¬suc≤0 : ∀ {n} → suc n ≤ zero → ⊥
¬suc≤0 ()

≤-unsuc : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-unsuc (mk-≤ p) = mk-≤ p

≤-refl : ∀ {n} → n ≤ n
≤-refl {(zero)} = 0-least
≤-refl {suc n} = ≤-suc ≤-refl

infixr 30 _◂_
_◂_ : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
_◂_ {(zero)} {m} {n} p q = 0-least
_◂_ {suc l} {suc m} {suc n} p q = ≤-suc (≤-unsuc p ◂ ≤-unsuc q)

≤-step : ∀ {n} → n ≤ suc n
≤-step {(zero)} = 0-least
≤-step {suc n} = ≤-suc ≤-step

≤-steps : ∀ m {n} → n ≤ m + n
≤-steps zero = ≤-refl
≤-steps (suc m) = ≤-steps m ◂ ≤-step

infix 4 _≐_
record _≐_ (m n : ℕ) : Type where
  eta-equality
  constructor mk-≐
  field
    le : m ≤ n
    ge : n ≤ m

≐-suc : ∀ {m n} → m ≐ n → suc m ≐ suc n
≐-suc (mk-≐ p q) = mk-≐ (≤-suc p) (≤-suc q)

≐-unsuc : ∀ {m n} → suc m ≐ suc n → m ≐ n
≐-unsuc (mk-≐ p q) = mk-≐ (≤-unsuc p) (≤-unsuc q)

≐-refl : ∀ {n} → n ≐ n
≐-refl = mk-≐ ≤-refl ≤-refl

≐→≤ : ∀ {m n} → m ≐ n → m ≤ n
≐→≤ (mk-≐ p q) = p

≐→≡ : ∀ {m n} → m ≐ n → m ≡ n
≐→≡ {(zero)} {(zero)} p i = zero
≐→≡ {suc m} {suc n} p i = suc (≐→≡ (≐-unsuc p) i)

≐→≤-filler : ∀ {m n} (p : m ≐ n) i → m ≤ ≐→≡ p i
≐→≤-filler {m} p i = transport-filler (λ i → m ≤ ≐→≡ p i) ≤-refl i

record ≤-MAlg (m n : ℕ) : Type₁ where
  constructor mk-≤-MAlg
  field
    T : m ≤ suc n → Type
    lt : (p : m ≤ n) → T (p ◂ ≤-step)
    eq : (p : m ≐ suc n) → T (≐→≤ p)

lower-≤-MAlg : ∀ {m n} → ≤-MAlg (suc m) (suc n) → ≤-MAlg m n
lower-≤-MAlg M =
  λ where
    .≤-MAlg.T p → T (≤-suc p)
    .≤-MAlg.lt p → lt (≤-suc p)
    .≤-MAlg.eq p → eq (≐-suc p)
  where
  open ≤-MAlg M

record ≤-Match {m n} (M : ≤-MAlg m n) : Type where
  open ≤-MAlg M
  field
    match : ∀ p → T p
    lt-β : (p : m ≤ n) → match (p ◂ ≤-step) ≡ lt p
    eq-β : (p : m ≐ suc n) → match (≐→≤ p) ≡ eq p

unlower-≤-Match :
  ∀ {m n} (M : ≤-MAlg (suc m) (suc n)) → ≤-Match (lower-≤-MAlg M) → ≤-Match M
unlower-≤-Match M F =
  λ where
    .≤-Match.match p → match (≤-unsuc p)
    .≤-Match.lt-β p → lt-β (≤-unsuc p)
    .≤-Match.eq-β p → eq-β (≐-unsuc p)
  where
  open ≤-Match F

≤-match : ∀ {m n} (M : ≤-MAlg m n) → ≤-Match M
≤-match {suc m} {suc n} M = unlower-≤-Match M (≤-match (lower-≤-MAlg M))
≤-match {suc (suc m)} {(zero)} M = λ where .≤-Match.match ()
≤-match {suc zero} {(zero)} M =
  λ where
    .≤-Match.match p → eq ≐-refl
    .≤-Match.eq-β p → refl
  where
  open ≤-MAlg M
≤-match {(zero)} {(n)} M =
  λ where
    .≤-Match.match p → lt 0-least
    .≤-Match.lt-β p → refl
  where
  open ≤-MAlg M

record ≤-MAlgP (m n : ℕ) : Type₁ where
  constructor mk-≤-MAlgP
  field
    {T-lt} : m ≤ n → Type
    {T-eq} : m ≐ 1 + n → Type

    T : m ≤ 1 + n → Type
    T-lt-β : ∀ p → T (p ◂ ≤-step) ≡ T-lt p
    T-eq-β : ∀ p → T (≐→≤ p) ≡ T-eq p

    lt : ∀ p → T-lt p
    eq : ∀ p → T-eq p

record ≤-MatchP {m n} (M : ≤-MAlgP m n) : Type where
  open ≤-MAlgP M
  field
    match : ∀ p → T p
    lt-β : ∀ p → PathP (λ i → T-lt-β p i) (match (p ◂ ≤-step)) (lt p)
    eq-β : ∀ p → PathP (λ i → T-eq-β p i) (match (≐→≤ p)) (eq p)

≤-matchP : ∀ {m n} (M : ≤-MAlgP m n) → ≤-MatchP M
≤-matchP {m} {n} M =
  λ where
    .≤-MatchP.match → match
    .≤-MatchP.lt-β p i →
      comp
        (λ j → T-lt-β p (i ∧ j))
        (λ where
          j (i = i0) → match (p ◂ ≤-step)
          j (i = i1) → match-lt.filler p (~ j))
        (match.lt-β p i)
    .≤-MatchP.eq-β p i →
      comp
        (λ j → T-eq-β p (i ∧ j))
        (λ where
          j (i = i0) → match (≐→≤ p)
          j (i = i1) → match-eq.filler p (~ j))
        (match.eq-β p i)
  where
  open ≤-MAlgP M

  match-lt : (p : m ≤ n) → T (p ◂ ≤-step)
  match-lt p = filler i1
    module match-lt where
    filler : ∀ i → _
    filler i = transport-filler (λ i → T-lt-β p (~ i)) (lt p) i

  match-eq : (p : m ≐ 1 + n) → T (≐→≤ p)
  match-eq p = filler i1
    module match-eq where
    filler : ∀ i → _
    filler i = transport-filler (λ i → T-eq-β p (~ i)) (eq p) i

  module match = ≤-Match (≤-match (mk-≤-MAlg T match-lt match-eq))
  open match using (match)

record ≤-Lim-AlgP : Type₁ where
  constructor mk-≤-Lim-Alg
  field
    h : ℕ
    ¬h≤0 : h ≤ 0 → ⊥

    {Tᴮ} : ∀ n → h ≤ n → Type
    {T-lower} : ∀ n p → Tᴮ (1 + n) (p ◂ ≤-step) ≡ Tᴮ n p

    T : Type
    {T-proj} : ∀ n p → T ≡ Tᴮ n p
    T-proj-lower :
      ∀ n p →
      Square (T-proj (1 + n) (p ◂ ≤-step)) (T-proj n p) refl (T-lower n p)

    {tᴮ} : ∀ n p → Tᴮ n p
    lower :
      ∀ n p → PathP (λ i → T-lower n p i) (tᴮ (1 + n) (p ◂ ≤-step)) (tᴮ n p)

record ≤-LimP (M : ≤-Lim-AlgP) : Type where
  open ≤-Lim-AlgP M
  field
    lim : T
    proj : ∀ n p → PathP (λ i → T-proj n p i) lim (tᴮ n p)
    proj-lower :
      ∀ n p →
      SquareP
        (λ i j → T-proj-lower n p i j)
        (proj (1 + n) (p ◂ ≤-step))
        (proj n p)
        refl
        (lower n p)

≤-limP : (M : ≤-Lim-AlgP) → ≤-LimP M
≤-limP M =
  λ where
    .≤-LimP.lim → lim
    .≤-LimP.proj → proj
    .≤-LimP.proj-lower → proj-lower
  where
  open ≤-Lim-AlgP M

  lim : T
  lim = filler i1
    module lim where
    filler : ∀ i → _
    filler i = transport-filler (λ i → T-proj h ≤-refl (~ i)) (tᴮ h ≤-refl) i

  proj₊-eq :
    ∀ n p → PathP (λ i → T-proj (1 + n) (≐→≤ p) i) lim (tᴮ (1 + n) (≐→≤ p))
  proj₊-eq n p i =
    comp
      (λ j → T-proj (≐→≡ p j) (≐→≤-filler p j) i)
      (λ where
        j (i = i0) → lim
        j (i = i1) → tᴮ (≐→≡ p j) (≐→≤-filler p j))
      (lim.filler (~ i))

  proj : ∀ n p → PathP (λ i → T-proj n p i) lim (tᴮ n p)
  proj₊ : ∀ n p → PathP (λ i → T-proj (1 + n) p i) lim (tᴮ (1 + n) p)
  proj₊-lt :
    ∀ n p →
    PathP (λ i → T-proj (1 + n) (p ◂ ≤-step) i) lim (tᴮ (1 + n) (p ◂ ≤-step))

  proj zero p = ⊥-rec (¬h≤0 p)
  proj (suc n) p = proj₊ n p

  proj₊ n = match
    module proj₊ where
    open ≤-Match
      (≤-match
        (mk-≤-MAlg
          (λ p → PathP (λ i → T-proj (1 + n) p i) lim (tᴮ (1 + n) p))
          (proj₊-lt n)
          (proj₊-eq n)))
      public

  proj₊-lt n p = λ i → filler i1 i
    module proj₊-lt where
    filler : ∀ j i → _
    filler j i =
      fill
        (λ j → T-proj-lower n p (~ j) i)
        (λ where
          j (i = i0) → lim
          j (i = i1) → lower n p (~ j))
        (inS (proj n p i))
        j

  proj-lower :
    ∀ n p →
    SquareP
      (λ i j → T-proj-lower n p i j)
      (proj (1 + n) (p ◂ ≤-step))
      (proj n p)
      refl
      (lower n p)
  proj-lower n p i j =
    comp
      (λ k → T-proj-lower n p (i ∧ k) j)
      (λ where
        k (i = i0) → proj (1 + n) (p ◂ ≤-step) j
        k (i = i1) → proj₊-lt.filler n p (~ k) j
        k (j = i0) → lim
        k (j = i1) → lower n p (i ∧ k))
      (proj₊.lt-β n p i j)
