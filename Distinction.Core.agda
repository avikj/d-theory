{-# OPTIONS --cubical --guardedness #-}

module Distinction.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Data.Nat

-- The Distinction Operator
-- In Cubical, (x ≡ y) is a TYPE, not a Prop
D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

-- D(⊥) ≃ ⊥ (emptiness stable)
D-Empty : D ⊥ ≃ ⊥
D-Empty = isoToEquiv (iso from to (λ ()) (λ ()))
  where
    from : D ⊥ → ⊥
    from (x , _ , _) = x

    to : ⊥ → D ⊥
    to ()

-- D(Unit) ≃ Unit (unity stable)
D-Unit : D Unit ≃ Unit
D-Unit = isoToEquiv (iso from to ret sec)
  where
    from : D Unit → Unit
    from _ = tt

    to : Unit → D Unit
    to tt = (tt , tt , refl)

    ret : ∀ x → from (to x) ≡ x
    ret tt = refl

    sec : ∀ x → to (from x) ≡ x
    sec (tt , tt , p) = Σ≡Prop (λ _ → Σ≡Prop (λ _ → isProp→PathP (λ _ → isSetUnit _ _) _ _) refl) refl

-- D(Unit) ≡ Unit (by univalence)
D-Unit-Path : D Unit ≡ Unit
D-Unit-Path = ua D-Unit

-- Iteration of D
D^_ : ℕ → Type → Type
D^ zero = λ X → X
D^ suc n = λ X → D (D^ n X)

-- For Unit, all iterations equal Unit
D^n-Unit : ∀ n → D^ n Unit ≡ Unit
D^n-Unit zero = refl
D^n-Unit (suc n) =
  D^ suc n Unit    ≡⟨ refl ⟩
  D (D^ n Unit)    ≡⟨ cong D (D^n-Unit n) ⟩
  D Unit           ≡⟨ D-Unit-Path ⟩
  Unit             ∎

D-map : ∀ {X Y : Type} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)
