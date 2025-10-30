{-# OPTIONS --cubical --guardedness #-}

module test_assoc where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma.Properties

-- Minimal test: does our mu make associativity automatic?
D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

-- Catuskoti mu
mu : ∀ {X : Type} → D (D X) → D X
mu ((x , y , p) , (x' , y' , p') , q) = (x , y' , (λ i → fst (q i)) ∙ p')

-- Alternative: using transport
mu-alt : ∀ {X : Type} → D (D X) → D X
mu-alt {X} ((x , y , p) , (x' , y' , p') , q) =
  (x , y' , transport (λ i → fst (q i) ≡ y') p')

D-map : ∀ {X Y : Type} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

D-bind : ∀ {X Y : Type} → D X → (X → D Y) → D Y
D-bind d f = mu (D-map f d)

ι : ∀ {X : Type} → X → D X
ι x = (x , x , refl)

-- Test with identity functions first
open import Cubical.Data.Nat

test-assoc-id : D-bind (D-bind (3 , 3 , refl) ι) ι ≡ D-bind (3 , 3 , refl) (λ w → D-bind (ι w) ι)
test-assoc-id = refl

-- General case: use path induction (J) from refl case
test-assoc : ∀ {X Y Z : Type} (m : D X) (f : X → D Y) (g : Y → D Z)
           → D-bind (D-bind m f) g ≡ D-bind m (λ x → D-bind (f x) g)
test-assoc (x , y , p) f g = J (λ y' p' → D-bind (D-bind (x , y' , p') f) g
                                          ≡ D-bind (x , y' , p') (λ w → D-bind (f w) g))
                                (test-assoc-refl x f g)
                                p
