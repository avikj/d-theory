import Distinction
import Necessity
import EternalLattice
import Mathlib.Logic.Equiv.Basic

-- The Semantic Connection (nabla) and Curvature (Riem)

-- Conceptual definition of nabla: nabla := D nec - nec D
-- This represents the non-commutativity of distinction and necessity.
-- A full formalization as a natural transformation requires a more extensive category theory setup.

-- For now, we formalize the notion of 'flatness' for a type X:
-- X is semantically flat if D(nec X) ≃ nec(D X).

def is_flat (X : Type u) : Prop :=
  (D (nec X)) ≃ (nec (D X))

-- Theorem: Sets are Flat
-- Every 0-type (set) X satisfies is_flat X.

-- Proof for Unit (a 0-type)
theorem is_flat_Unit : is_flat Unit := by
  -- We need to show D (nec Unit) ≃ nec (D Unit)

  -- Left side: D (nec Unit)
  -- nec Unit ≃ Unit (from nec.idempotent Unit)
  -- D (nec Unit) ≃ D Unit (since D is a functor and preserves equivalences)
  -- D Unit ≃ Unit (from d_unit_equiv_unit in EternalLattice.lean)
  have h1 : D (nec Unit) ≃ D Unit := Equiv.map_equiv D (nec.idempotent Unit)
  have h2 : D Unit ≃ Unit := d_unit_equiv_unit
  let lhs_equiv_unit := Equiv.trans h1 h2

  -- Right side: nec (D Unit)
  -- D Unit ≃ Unit (from d_unit_equiv_unit)
  -- nec (D Unit) ≃ nec Unit (since nec is a functor and preserves equivalences)
  -- nec Unit ≃ Unit (from nec.idempotent Unit)
  have h3 : nec (D Unit) ≃ nec Unit := Equiv.map_equiv nec d_unit_equiv_unit
  have h4 : nec Unit ≃ Unit := nec.idempotent Unit
  let rhs_equiv_unit := Equiv.trans h3 h4

  -- Both sides are equivalent to Unit, so they are equivalent to each other.
  exact Equiv.trans lhs_equiv_unit rhs_equiv_unit.symm

-- Proof for Empty (another 0-type)
theorem is_flat_Empty : is_flat Empty := by
  -- We need to show D (nec Empty) ≃ nec (D Empty)

  -- Left side: D (nec Empty)
  -- nec Empty ≃ Empty (from nec.idempotent Empty)
  -- D (nec Empty) ≃ D Empty (since D is a functor and preserves equivalences)
  -- D Empty ≃ Empty (from d_empty_is_empty in Distinction.lean)
  have h_nec_empty_equiv_empty : nec Empty ≃ Empty := nec.idempotent Empty
  have h_D_empty_equiv_empty : D Empty ≃ Empty := Equiv.ofIsEmpty (D Empty) (Distinction.d_empty_is_empty)

  have lhs : D (nec Empty) ≃ Empty := Equiv.trans (Equiv.map_equiv D h_nec_empty_equiv_empty) h_D_empty_equiv_empty

  -- Right side: nec (D Empty)
  have rhs : nec (D Empty) ≃ Empty := Equiv.trans (Equiv.map_equiv nec h_D_empty_equiv_empty) h_nec_empty_equiv_empty

  -- Both sides are equivalent to Empty, so they are equivalent to each other.
  exact Equiv.trans lhs rhs.symm
