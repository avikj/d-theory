{-# OPTIONS --cubical --guardedness #-}

module test_refl_case where

open import Cubical.Foundations.Prelude

D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

mu : ∀ {X : Type} → D (D X) → D X
mu ((x , y , p) , (x' , y' , p') , q) = (x , y' , (λ i → fst (q i)) ∙ p')

D-map : ∀ {X Y : Type} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

D-bind : ∀ {X Y : Type} → D X → (X → D Y) → D Y
D-bind d f = mu (D-map f d)

-- Test JUST the refl case for path equality
test-refl-paths : ∀ {X Y Z : Type} (x : X) (f : X → D Y) (g : Y → D Z)
                → snd (snd (D-bind (D-bind (x , x , refl) f) g))
                ≡ snd (snd (D-bind (x , x , refl) (λ w → D-bind (f w) g)))
test-refl-paths x f g = refl
