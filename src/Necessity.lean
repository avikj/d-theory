import Mathlib.Logic.Equiv.Basic

-- The Necessity Operator (0-truncation)

-- Definition of the Necessity Operator as 0-truncation
-- This collapses all elements of a type X into a single element, effectively making it a 0-type.
def nec (X : Type u) : Type u :=
  Quotient (fun _ _ : X => True)

-- The unit of the necessity operator
def nec.eta (X : Type u) : X → nec X :=
  Quotient.mk (fun _ _ : X => True)

-- The action of the necessity operator on morphisms (functoriality)
def nec.map {X Y : Type u} (f : X → Y) : nec X → nec Y :=
  Quotient.map f (fun _ _ _ _ => id)

-- Proof that nec is a functor (preserves identity and composition)
-- Identity preservation
theorem nec.map_id (X : Type u) : nec.map (id : X → X) = id := by
  ext x
  simp [nec.map]

-- Composition preservation
theorem nec.map_comp {X Y Z : Type u} (g : Y → Z) (f : X → Y) : nec.map (g ∘ f) = nec.map g ∘ nec.map f := by
  ext x
  simp [nec.map]

-- Proof that nec is idempotent (nec (nec X) ≃ nec X)
theorem nec.idempotent (X : Type u) : nec (nec X) ≃ nec X := by
  by_cases hX_nonempty : Nonempty X
  . -- Case 1: X is non-empty
    -- Show that nec X is inhabited
    have hnX_inhabited : Inhabited (nec X) := by
      cases' hX_nonempty with x
      exact Inhabited.mk (nec.eta X x)

    -- Show that nec X has at most one element
    have hnX_subsingleton : Subsingleton (nec X) := by
      intro a b
      have := Quotient.ind₂ (fun x y => (Quotient.mk (fun _ _ : X => True) x = Quotient.mk (fun _ _ : X => True) y)) a b
      simp

    -- Conclude that nec X is Unique and thus equivalent to Unit
    have hnX_unique : Unique (nec X) := Unique.mk' hnX_inhabited hnX_subsingleton
    let equiv_nec_X_unit : nec X ≃ Unit := Equiv.ofUnique (nec X)

    -- Now, for nec (nec X)
    -- Show that nec (nec X) is inhabited
    have hnnX_inhabited : Inhabited (nec (nec X)) := by
      let a : nec X := hnX_inhabited.default
      exact Inhabited.mk (nec.eta (nec X) a)

    -- Show that nec (nec X) has at most one element
    have hnnX_subsingleton : Subsingleton (nec (nec X)) := by
      intro a b
      have := Quotient.ind₂ (fun x y => (Quotient.mk (fun _ _ : nec X => True) x = Quotient.mk (fun _ _ : nec X => True) y)) a b
      simp
    
    -- Conclude that nec (nec X) is Unique and thus equivalent to Unit
    have hnnX_unique : Unique (nec (nec X)) := Unique.mk' hnnX_inhabited hnnX_subsingleton
    let equiv_nec_nec_X_unit : nec (nec X) ≃ Unit := Equiv.ofUnique (nec (nec X))

    -- By transitivity, nec (nec X) ≃ nec X
    exact Equiv.trans equiv_nec_nec_X_unit equiv_nec_X_unit.symm

  . -- Case 2: X is empty
    -- If X is empty, then nec X is empty
    have hnX_empty : IsEmpty (nec X) := by
      intro val
      apply Quotient.exists_rep val
      intro x
      exact hX_nonempty (Nonempty.intro x)
    
    -- If nec X is empty, then nec (nec X) is also empty
    have hnnX_empty : IsEmpty (nec (nec X)) := by
      intro val
      apply Quotient.exists_rep val
      intro x
      exact hnX_empty (Nonempty.intro x)

    -- Two empty types are equivalent
    exact Equiv.ofIsEmpty (nec (nec X)) (nec X)

