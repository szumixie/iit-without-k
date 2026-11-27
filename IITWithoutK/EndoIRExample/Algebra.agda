module IITWithoutK.EndoIRExample.Algebra where

open import IITWithoutK.Prelude

record Alg : Type where
  field
    Tree : Type
    fun : Tree → Tree

    leaf : Tree
    node : Tree → Tree → Tree

    fun-leaf : fun leaf ≡ node leaf leaf
    fun-node : ∀ {l r} → fun (node l r) ≡ node l (node r (fun r))

record IAlg : Type where
  field
    Tree : ∀ i → 1 ≤ i → Type
    fun-height : ∀ {i 1≤i} → Tree i 1≤i → ℕ
    fun-lbound : ∀ {i 1≤i} (t : Tree i 1≤i) → 1 ≤ fun-height t
    fun : ∀ {i 1≤i} (t : Tree i 1≤i) → Tree (fun-height t) (fun-lbound t)

    leaf : Tree 1 ≤-refl
    node :
      ∀ {i 1≤i j 1≤j} →
      Tree i 1≤i →
      Tree j 1≤j →
      Tree (1 + (i ⊔ j)) (⊔-least (1≤i ◂ ⊔-inₗ i j) (1≤j ◂ ⊔-inᵣ i j) ◂ ≤-step)

    fun-height-leaf : fun-height leaf ≡ 2
    fun-height-node :
      ∀ {i 1≤i j 1≤j} →
      (l : Tree i 1≤i) (r : Tree j 1≤j) →
      fun-height (node l r) ≡ 1 + (i ⊔ (1 + (j ⊔ fun-height r)))

    fun-leaf : fun leaf ≡ {!node leaf leaf!}
