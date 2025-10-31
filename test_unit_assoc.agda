{-# OPTIONS --cubical --guardedness #-}

module test_unit_assoc where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit

D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

mu : ∀ {X : Type} → D (D X) → D X
mu ((x , y , p) , (x' , y' , p') , q) = (x , y' , (λ i → fst (q i)) ∙ p')

D-map : ∀ {X Y : Type} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

D-bind : ∀ {X Y : Type} → D X → (X → D Y) → D Y
D-bind d f = mu (D-map f d)

-- Test: Is associativity automatic for Unit?
test-unit-assoc : (m : D Unit) (f : Unit → D Unit) (g : Unit → D Unit)
                → D-bind (D-bind m f) g ≡ D-bind m (λ w → D-bind (f w) g)
test-unit-assoc m f g = refl
