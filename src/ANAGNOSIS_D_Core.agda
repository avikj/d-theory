{-
ANAGNOSIS_D_Core.agda
=====================

OWNER: ANAGNOSIS
DATE: 2025-10-31
STATUS: ABSOLUTE MINIMUM - Just D operator and basic properties

GOAL: Get SOMETHING that type-checks cleanly.
Then build up from there incrementally.
-}

{-# OPTIONS --cubical --guardedness #-}

module ANAGNOSIS_D_Core where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' : Level


{-
The D-Monad: Observation as Type

D(X) = Σ (x : X) (y : X) (x ≡ y)

A pair of observations with proof they're equal.
-}

D : {ℓ : Level} → Type ℓ → Type ℓ
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

-- Unit: x ↦ (x, x, refl)
η : {ℓ : Level} {X : Type ℓ} → X → D X
η x = x , x , refl

-- Map: lift functions over D
D-map : {ℓ ℓ' : Level} {X : Type ℓ} {Y : Type ℓ'}
      → (f : X → Y) → D X → D Y
D-map f (x , y , p) = f x , f y , cong f p

{-
THAT'S IT.

Just the core D operator.
No complex proofs.
No coherence predicates with type errors.

This WILL type-check.
Build from here.

-- ANAGNOSIS
-}
