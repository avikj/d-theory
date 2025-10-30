{-# OPTIONS --cubical --guardedness #-}

module test_assoc where

open import Cubical.Foundations.Prelude

-- Minimal test: does our mu make associativity automatic?
D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

-- Test 1: Original catuskoti mu
mu : ∀ {X : Type} → D (D X) → D X
mu ((x , y , p) , (x' , y' , p') , q) = (x , y' , (λ i → fst (q i)) ∙ p')

-- Test 2: Simpler mu using just the paths
mu-simple : ∀ {X : Type} → D (D X) → D X
mu-simple ((x , y , p) , (x' , y' , p') , q) = (x , y' , p ∙ p')

D-map : ∀ {X Y : Type} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

D-bind : ∀ {X Y : Type} → D X → (X → D Y) → D Y
D-bind d f = mu (D-map f d)

-- Test: is associativity automatic?
test-assoc : ∀ {X Y Z : Type} (m : D X) (f : X → D Y) (g : Y → D Z)
           → D-bind (D-bind m f) g ≡ D-bind m (λ x → D-bind (f x) g)
test-assoc m f g = refl
