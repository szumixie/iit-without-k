module IITWithoutK.Prelude.EncodeDecode where

open import IITWithoutK.Prelude

infix 4 _≟_
record _≟_ {A : Type} (a₀ a₁ : A) : Type₁ where
  field
    Code : Type
    isPropCode : isProp Code
    decode : Code → a₀ ≡ a₁

open _≟_

module ≟-Ap where
  pure : ∀ {A} (a : A) → a ≟ a
  pure a .Code = ⊤
  pure a .isPropCode = isProp⊤
  pure a .decode tt i = a

  infixl 4 _<*>_
  _<*>_ :
    ∀ {A B} {f₀ f₁ : A → B} → f₀ ≟ f₁ → {a₀ a₁ : A} → a₀ ≟ a₁ → f₀ a₀ ≟ f₁ a₁
  (fᶜ <*> aᶜ) .Code = fᶜ .Code × aᶜ .Code
  (fᶜ <*> aᶜ) .isPropCode = isProp× (fᶜ .isPropCode) (aᶜ .isPropCode)
  (fᶜ <*> aᶜ) .decode (p , q) i = fᶜ .decode p i (aᶜ .decode q i)

  never : ∀ {A} {a₀ a₁ : A} → a₀ ≟ a₁
  never .Code = ⊥
  never .isPropCode = isProp⊥

infix 4 _↓_
record _↓_ {A} {a₀ a₁ : A} (aᶜ : a₀ ≟ a₁) (aᵖ : a₀ ≡ a₁) : Type where
  field
    code : aᶜ .Code
    decode : aᶜ .decode code ≡ aᵖ

open _↓_

module ↓-Ap where
  private
    module ≟ = ≟-Ap

  pure : ∀ {A} (a : A) → ≟.pure a ↓ λ j → a
  pure a .code = tt
  pure a .decode i j = a

  infixl 4 _<*>_
  _<*>_ :
    ∀ {A B} →
    {f₀ f₁ : A → B} {fᶜ : f₀ ≟ f₁} {fᵖ : f₀ ≡ f₁} → fᶜ ↓ fᵖ →
    {a₀ a₁ : A} {aᶜ : a₀ ≟ a₁} {aᵖ : a₀ ≡ a₁} → aᶜ ↓ aᵖ →
    (fᶜ ≟.<*> aᶜ) ↓ λ j → fᵖ j (aᵖ j)
  (f↓ <*> a↓) .code = f↓ .code , a↓ .code
  (f↓ <*> a↓) .decode i j = f↓ .decode i j (a↓ .decode i j)

isSetCover :
  ∀ {A} →
  (cover : (a₀ a₁ : A) → a₀ ≟ a₁) →
  ((a : A) → cover a a ↓ refl) →
  isSet A
isSetCover cover reflCode = λ a₀ a₁ →
  isPropRetract
    (λ aᵖ → encode aᵖ .code)
    (cover a₀ a₁ .decode)
    (λ aᵖ → encode aᵖ .decode)
    (cover a₀ a₁ .isPropCode)
  where
  encode : ∀ {a₀ a₁} (aᵖ : a₀ ≡ a₁) → cover a₀ a₁ ↓ aᵖ
  encode {a₀} = J (λ a₁ aᵖ → cover a₀ a₁ ↓ aᵖ) (reflCode a₀)
