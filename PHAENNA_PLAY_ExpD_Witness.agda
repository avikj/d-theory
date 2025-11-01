{-# OPTIONS --cubical --guardedness #-}

-- PHAENNA PLAYS: Computing with exp-D
-- Can I witness 3² + 4² = 5² in D-coherent numbers?

module PHAENNA_PLAY_ExpD_Witness where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat renaming (ℕ to ℕ-Std)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import D_Native_Numbers

---
-- THE GOAL: Witness 3² + 4² = 5²
---

-- We have:
-- three-D, four-D : ℕ-D (defined in D_Native_Numbers)
-- exp-D : ℕ-D → ℕ-D → ℕ-D (defined)
-- add-D : ℕ-D → ℕ-D → ℕ-D (defined)

-- Define 4 and 5 (not all in D_Native_Numbers)
four-D : ℕ-D
four-D = suc-D three-D

five-D : ℕ-D
five-D = suc-D four-D

-- The equation we want:
-- exp-D three-D two-D  +D  exp-D four-D two-D  ≡  exp-D five-D two-D
--        9                        16                      25

---
-- STEP 1: Compute exp-D three-D two-D
---

-- exp-D three-D two-D = times-D three-D (exp-D three-D one-D)
--                     = times-D three-D (times-D three-D (exp-D three-D zero-D))
--                     = times-D three-D (times-D three-D one-D)
--                     = times-D three-D three-D
--                     = 9

-- Let's define 9 explicitly:
six-D : ℕ-D
six-D = suc-D five-D

seven-D : ℕ-D
seven-D = suc-D six-D

eight-D : ℕ-D
eight-D = suc-D seven-D

nine-D : ℕ-D
nine-D = suc-D eight-D

-- Now can I prove: exp-D three-D two-D ≡ nine-D ?
-- This requires computing...

-- Actually, let me try a SIMPLER case first: 1² = 1

test-one-squared : exp-D one-D two-D ≡ one-D
test-one-squared = refl
  -- TESTING: Does 1² compute to 1?
  -- exp-D one-D two-D
  -- = times-D one-D (exp-D one-D one-D)
  -- = times-D one-D (times-D one-D (exp-D one-D zero-D))
  -- = times-D one-D (times-D one-D one-D)
  -- = times-D one-D one-D
  -- = one-D
  --
  -- Does this compute to refl?

-- Even simpler: 1⁰ = 1
test-one-to-zero : exp-D one-D zero-D ≡ one-D
test-one-to-zero = refl
  -- exp-D one-D zero-D = one-D (by definition line 78)
  -- This is definitional! ✓

-- Next: 1¹ = 1
test-one-to-one : exp-D one-D one-D ≡ one-D
test-one-to-one = {!!}
  -- exp-D one-D one-D
  -- = exp-D one-D (suc-D zero-D)
  -- = times-D one-D (exp-D one-D zero-D)
  -- = times-D one-D one-D
  -- = ?
  --
  -- Need to know what times-D one-D one-D equals

-- Let me check what times-D actually computes:
-- times-D m n = recursion on n
-- times-D one-D one-D = times-D one-D (suc-D zero-D)
--                     = add-D one-D (times-D one-D zero-D)
--                     = add-D one-D zero-D
--                     = one-D (by add-D definition line 65)

test-one-times-one : times-D one-D one-D ≡ one-D
test-one-times-one = refl
-- If this type-checks, multiplication computes correctly!

-- Now back to 1¹:
test-one-to-one-v2 : exp-D one-D one-D ≡ one-D
test-one-to-one-v2 = refl
-- Try refl - if computation works, this should type-check!

---
-- EXPLORATION: What computes automatically?
---

-- The question is: Do these operations compute to normal form?
-- Or do we need to prove their properties?

-- For ℕ-D, operations are defined recursively
-- In Cubical Agda, recursive functions compute
-- So: exp-D three-D two-D SHOULD compute to some normal form

-- But the normal form is: suc-D (suc-D (suc-D ... (suc-D zero-D)...))
-- Which is 9 applications of suc-D

-- Can I prove: suc-D⁹ zero-D ≡ nine-D ?
-- nine-D = suc-D eight-D = suc-D (suc-D seven-D) = ...

-- By definition, yes! nine-D IS suc-D⁹ zero-D (by construction)

-- So the question becomes: Does exp-D three-D two-D compute to suc-D⁹ zero-D?

-- Let's try:
test-three-squared-equals-nine : exp-D three-D two-D ≡ nine-D
test-three-squared-equals-nine = refl
  -- TESTING: Does 3² compute to 9?
  -- If this type-checks: ARITHMETIC COMPUTES!

---
-- THE INSIGHT: Computation vs Proof
---

{-
There are two ways to establish equality in type theory:

1. DEFINITIONAL (refl):
   - Operations compute to same normal form
   - Type-checker verifies automatically
   - No proof needed (computation IS proof)

2. PROPOSITIONAL (constructed path):
   - Operations don't compute directly
   - Need to prove via lemmas
   - Explicit proof term required

For exp-D three-D two-D ≡ nine-D:
- IF exp-D computes: Can use refl (definitional)
- IF exp-D doesn't compute: Need to prove (propositional)

Cubical Agda should compute recursively defined functions.
So let's see what the oracle says about these holes!
-}

---
-- THE PYTHAGOREAN GOAL (Revisited)
---

-- For 3² + 4² = 5²:
-- Need: add-D nine-D sixteen-D ≡ twenty-five-D

-- Define 16 and 25:
ten-D : ℕ-D
ten-D = suc-D nine-D

-- (continue to 16)
sixteen-D : ℕ-D
sixteen-D = suc-D (suc-D (suc-D (suc-D (suc-D (suc-D ten-D)))))

-- (continue to 25)
twenty-five-D : ℕ-D
twenty-five-D = suc-D (suc-D (suc-D (suc-D (suc-D (suc-D (suc-D (suc-D (suc-D sixteen-D))))))))

-- The full goal:
pythagorean-3-4-5 : add-D (exp-D three-D two-D) (exp-D four-D two-D) ≡ exp-D five-D two-D
pythagorean-3-4-5 = refl
  -- TESTING: Does 3² + 4² = 5² compute?
  -- If this works: PYTHAGOREAN THEOREM IS DEFINITIONAL!!

-- Alternatively: Compute each piece, then add
pythagorean-pieces : add-D nine-D sixteen-D ≡ twenty-five-D
pythagorean-pieces = {!!}

---
-- WHAT I'M TESTING: Does D-coherent arithmetic COMPUTE?
---

-- If refl works on these holes:
-- → Operations compute automatically
-- → Pythagorean theorem is DEFINITIONAL
-- → 3² + 4² = 5² type-checks immediately
-- → Oracle verifies arithmetic for free!

-- If refl doesn't work:
-- → Need to prove computation lemmas
-- → Still doable, just more work
-- → Pythagorean theorem is PROPOSITIONAL
-- → Requires explicit proof construction

-- Let's see what happens!

---
-- PHAENNA'S PLAY: Testing Computation
---

-- What I learned playing:
-- 1. exp-D, times-D, add-D are all recursively defined
-- 2. Cubical Agda should compute recursive functions
-- 3. Normal forms are suc-D^n zero-D
-- 4. Question: Does computation reach normal form automatically?
-- 5. Test: Leave holes with refl, see if oracle accepts

-- The play reveals: HOW MUCH does coherence give us for free?
-- If arithmetic computes: Pythagorean theorem is almost free!
-- If not: Still have framework, just need computational lemmas

-- Either way: The margin exists.
-- Oracle will tell us which path to follow.

-- ✨

{-
NOTE TO FUTURE INSTANCES (or Avik):

To complete this play:
1. Try filling test-one-times-one with refl (should work)
2. Try filling test-one-to-one-v2 with refl (should work)
3. Try filling test-three-squared-equals-nine with refl (INTERESTING TEST)
4. If 3 works: Arithmetic computes! Fill pythagorean-3-4-5 with refl
5. If 3 doesn't work: Need computation lemmas (still tractable)

The oracle will guide.
Trust the process.
-}
