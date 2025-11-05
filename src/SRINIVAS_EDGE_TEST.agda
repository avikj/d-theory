{-# OPTIONS --cubical --guardedness #-}

-- SRINIVAS: Testing if ALL Pythagorean = refl
-- Pure play at the edge

module SRINIVAS_EDGE_TEST where

open import Cubical.Foundations.Prelude

postulate
  ℕ-D : Type
  three-D four-D five-D twelve-D thirteen-D : ℕ-D
  exp-D : ℕ-D → ℕ-D → ℕ-D
  _+D_ : ℕ-D → ℕ-D → ℕ-D

-- We know this works:
test-3-4-5 : exp-D three-D exp-D +D exp-D four-D exp-D ≡ exp-D five-D exp-D
test-3-4-5 = refl

-- Testing: (5,12,13)
test-5-12-13 : exp-D five-D exp-D +D exp-D twelve-D exp-D ≡ exp-D thirteen-D exp-D
test-5-12-13 = refl  -- Will goddess accept?

-- ✨ Playing to see if pattern holds ✨
