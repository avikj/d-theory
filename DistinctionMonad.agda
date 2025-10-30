{-# OPTIONS --cubical --guardedness #-}

module DistinctionMonad where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

-- The Distinction Operator
D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

-- D(⊥) ≃ ⊥  
D-Empty : D ⊥ ≃ ⊥
D-Empty = isoToEquiv (iso (λ (x , _ , _) → x) (λ ()) (λ ()) (λ ()))

-- D(Unit) ≃ Unit
D-Unit : D Unit ≃ Unit
D-Unit = isoToEquiv (iso (λ _ → tt) (λ tt → (tt , tt , refl)) (λ tt → refl) 
                         (λ (tt , tt , p) i → tt , tt , isSetUnit tt tt p refl i))

-- D(Unit) ≡ Unit (by univalence)
D-Unit-Path : D Unit ≡ Unit
D-Unit-Path = ua D-Unit

-- Functoriality
D-map : ∀ {X Y : Type} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

-- Canonical embedding (return)
ι : ∀ {X : Type} → X → D X
ι x = (x , x , refl)

-- Monad join (mu)
mu : ∀ {X : Type} → D (D X) → D X
mu ((x₁ , y₁ , p₁) , (x₂ , y₂ , p₂) , q) = (x₁ , y₂ , p₁ ∙ (q .snd .fst))

-- Monad laws

left-identity : ∀ {X Y : Type} (x : X) (f : X → D Y) → mu (D-map f (ι x)) ≡ f x
left-identity x f = 
  let (x_f , y_f , p_f) = f x in
  cong (λ p' → x_f , y_f , p') (sym (rUnit p_f))

right-identity : ∀ {X : Type} (m : D X) → mu (D-map ι m) ≡ m  
right-identity (x , y , p) = cong (λ p' → x , y , p') (sym (lUnit p))

associativity : ∀ {X Y Z : Type} (m : D X) (f : X → D Y) (g : Y → D Z) 
              → mu (D-map g (mu (D-map f m))) ≡ mu (D-map (λ x → mu (D-map g (f x))) m)
associativity (x , y , p) f g =
  let x_f = (f x) .fst
      y_f' = (f y) .snd .fst  
      p_f = (f x) .snd .snd
      q_f = cong f p .snd .fst
      y_g' = (g y_f') .snd .fst
      q_g = cong g q_f .snd .fst
  in cong (λ path → x_f , y_g' , path) (assoc p_f q_f q_g)
