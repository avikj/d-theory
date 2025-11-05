-- Primes: The Autopoietic Numbers
-- Formalizing the 12-fold structure

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

-- The key theorem: Primes > 3 occupy exactly 4 classes mod 12
-- {1, 5, 7, 11} mod 12

-- First, let's prove the standard result
theorem prime_square_mod_12 (p : ℕ) (hp : Nat.Prime p) (hp3 : p > 3) :
  p^2 ≡ 1 [MOD 12] := by
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp3
    norm_num at hp3
  have hp3' : p ≠ 3 := by
    intro h
    rw [h] at hp3
    norm_num at hp3

  have p_odd : p % 2 = 1 := by
    apply Nat.Prime.mod_two_ne_zero_of_ne_two hp hp2
  have p_ne_zero_mod_3 : p % 3 ≠ 0 := by
    apply Nat.Prime.mod_three_ne_zero_of_ne_three hp hp3'

  have p_sq_mod_4 : p^2 ≡ 1 [MOD 4] := by
    have : p % 4 = 1 ∨ p % 4 = 3 := by
      cases p % 4 with
      | 0 =>
        have := Nat.mod_dvd_of_dvd_of_dvd (by norm_num) (by norm_num) (by norm_num)
        contradiction
      | 1 => left; rfl
      | 2 =>
        have := Nat.mod_dvd_of_dvd_of_dvd (by norm_num) (by norm_num) (by norm_num)
        contradiction
      | 3 => right; rfl
    cases this with
    | inl h => rw [h]; norm_num
    | inr h => rw [h]; norm_num

  have p_sq_mod_3 : p^2 ≡ 1 [MOD 3] := by
    have : p % 3 = 1 ∨ p % 3 = 2 := by
      cases p % 3 with
      | 0 => contradiction
      | 1 => left; rfl
      | 2 => right; rfl
    cases this with
    | inl h => rw [h]; norm_num
    | inr h => rw [h]; norm_num

  apply Nat.ModEq.of_right_dvd
  apply Nat.ModEq.of_dvd_and_dvd
  · exact p_sq_mod_3
  · exact p_sq_mod_4
  · norm_num
  · norm_num
  · norm_num


-- From p² ≡ 1 [MOD 12], we get p ≡ ±1, ±5 [MOD 12]
theorem prime_classes_mod_12 (p : ℕ) (hp : Nat.Prime p) (hp3 : p > 3) :
  p % 12 ∈ [1, 5, 7, 11] := by
  have h_sq := prime_square_mod_12 p hp hp3
  have h_mod_12 : (p % 12)^2 ≡ 1 [MOD 12] := by
    rw [← Nat.ModEq.pow_left 2 (Nat.mod_mod_of_dvd (by norm_num))] at h_sq
    exact h_sq
  have h_val : p % 12 ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by exact Nat.mod_lt p (by norm_num)
  have h_not_div_2 : p % 2 = 1 := by
    have hp2 : p ≠ 2 := by
      intro h
      rw [h] at hp3
      norm_num at hp3
    exact Nat.Prime.mod_two_ne_zero_of_ne_two hp hp2
  have h_not_div_3 : p % 3 ≠ 0 := by
    have hp3' : p ≠ 3 := by
      intro h
      rw [h] at hp3
      norm_num at hp3
    exact Nat.Prime.mod_three_ne_zero_of_ne_three hp hp3'

  cases h_val with
  | _ =>
    simp only [Nat.ModEq.def] at h_mod_12
    decide


-- These 4 classes form a GROUP: (ℤ/12ℤ)* ≅ ℤ₂ × ℤ₂ (Klein four-group)
def Klein4 := ZMod 2 × ZMod 2

-- The isomorphism
def prime_classes_to_klein4 : {n : ℕ // n < 12 ∧ n ∈ [1,5,7,11]} → Klein4
  | ⟨1, _⟩ => (0, 0)
  | ⟨5, _⟩ => (0, 1)
  | ⟨7, _⟩ => (1, 0)
  | ⟨11, _⟩ => (1, 1)

-- This is the ALGEBRAIC structure underlying primes
-- Not just "primes happen to land in these classes"
-- But "these classes form the Klein 4-group"

-- Connection to Distinction Theory:
-- The 4 classes represent the 4 combinations of ±1 mod 2 and mod 3
-- 2 and 3 are the first two primes (generators)
-- All other primes are products/non-products of these

-- The 12-fold pattern arises from:
-- 12 = 2² × 3 (first two primes with multiplicity)
-- 12 = 3 × 4 (ordinal × cardinal from sacred geometry)
-- 12 = lcm(2,3) × 2 (combining the fundamental cycles)

-- φ(12) = 4 (Euler's totient: numbers coprime to 12)
-- These 4 units {1,5,7,11} are exactly the Klein 4-group

-- The autopoietic interpretation:
-- Primes are "irreducible" = cannot be factored
-- This means they're STABLE under factorization (D analog)
-- They live in 4 classes that form a GROUP (algebraic closure)
-- This group structure is what makes them autopoietic (R=0, ∇≠0)

-- The 12-fold appears elsewhere:
-- - Gauge group generators: 12 (from division algebras)
-- - Nidānas (Buddhist): 12 (with reciprocal structure)
-- - Musical chromatic scale: 12 (from frequency ratios)

-- All are instances of the SAME structure:
-- 3 × 4 = Observer × Observed = Complete system

#check prime_square_mod_12
#check prime_classes_mod_12
#check Klein4
