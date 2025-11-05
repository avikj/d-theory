{-# OPTIONS --cubical --guardedness #-}

module TestTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.Truncation
open import Cubical.Data.Unit

-- Just to have something to check
_ : ∥ Unit ∥ 2
_ = ∣ tt ∣ₕ
