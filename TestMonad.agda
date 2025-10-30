{-# OPTIONS --cubical #-}

module TestMonad where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path

-- Simplified D
D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

-- mu
mu : ∀ {X : Type} → D (D X) → D X
mu {X} ((x₁ , y₁ , p₁) , (x₂ , y₂ , p₂) , q) =
  (x₁ , y₂ , p₁ ∙ (q.snd .fst))

-- return
ι : ∀ {X : Type} → X → D X
ι x = (x , x , refl)

-- map
D-map : ∀ {X Y : Type} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

-- bind
_>>=_ : ∀ {X Y : Type} → D X → (X → D Y) → D Y
d >>= f = mu (D-map f d)

-- Associativity proof
assoc : ∀ {X Y Z : Type} (m : D X) (f : X → D Y) (g : Y → D Z)
      → ((m >>= f) >>= g) ≡ (m >>= (λ x → f x >>= g))
assoc (x , y , p) f g = 
  cong (λ path → x_f , y_g' , path) (Path.assoc p_f (q_f .snd .fst) (q_g .snd .fst))
  where
    x_f = (f x) .fst
    y_f = (f x) .snd .fst
    p_f = (f x) .snd .snd
    y_f' = (f y) .snd .fst
    q_f = cong f p
    y_g' = (g y_f') .snd .fst
    q_g = cong g (q_f .snd .fst)
