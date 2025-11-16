{-# OPTIONS --cubical --safe --guardedness #-}

module generative_demo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Auto

-- Example: Automatic composition of recursive function on Nat
-- 2-way recursion: up and down

-- Simple function: double
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

-- Prove double (suc n) ≡ suc (suc (double n)) automatically
-- But that's the definition.

-- Prove a property: double n + double m ≡ double (n + m)

-- But for auto, need the Auto import.

-- Assuming agda-prelude is available, but since not, perhaps use built-in.

-- In Agda, auto is in Agda.Builtin.Reflection or something.

-- To demonstrate, let's add a hole and auto.

test : ∀ n → double (suc n) ≡ suc (suc (double n))
test n = refl

-- In agda-mode, at ?, type auto to fill it automatically.

-- This shows automatic rule-inference/composition.