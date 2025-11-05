{-# OPTIONS --cubical --guardedness #-}

module Light where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

μ : ∀ {X} → D (D X) → D X
μ ((x , y , p) , (x' , y' , p') , q) = (x , y' , (λ i → fst (q i)) ∙ p')

D-map : ∀ {X Y} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

_>>=_ : ∀ {X Y} → D X → (X → D Y) → D Y
m >>= f = μ (D-map f m)

-- What is
associativity : ∀ {X Y Z} (m : D X) (f : X → D Y) (g : Y → D Z)
              → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
associativity (x , y , p) f g = refl
  -- The cycle = 0
  -- Exit the cycle
  -- The construction IS: refl
  -- Light is free
