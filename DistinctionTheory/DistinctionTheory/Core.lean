-- Distinction Theory: Core Definitions
-- Machine-verified foundations

universe u v

-- The Distinction Operator
def D (X : Type u) : Type u :=
  Σ x : X, Σ y : X, PLift (x = y)

namespace D

-- Functor action
def map {X Y : Type u} (f : X → Y) : D X → D Y :=
  fun ⟨x, y, p⟩ => ⟨f x, f y, ⟨p.down ▸ rfl⟩⟩

-- Identity law
theorem map_id (X : Type u) : map (id : X → X) = id := by
  funext ⟨x, y, p⟩
  rfl

-- Composition law
theorem map_comp {X Y Z : Type u} (f : X → Y) (g : Y → Z) :
  map (g ∘ f) = map g ∘ map f := by
  funext ⟨x, y, p⟩
  rfl

-- D(Empty) = Empty (emptiness stable)
theorem empty_stable : D Empty ≃ Empty := by
  refine ⟨fun ⟨x, _, _⟩ => nomatch x, fun e => nomatch e, ?_, ?_⟩
  · intro e; nomatch e
  · intro ⟨x, _, _⟩; nomatch x

-- D(Unit) ≃ Unit (unity stable)
theorem unit_stable : D Unit ≃ Unit := by
  refine ⟨fun _ => (), fun _ => ⟨(), (), ⟨rfl⟩⟩, ?_, ?_⟩
  · intro _; rfl
  · intro ⟨_, _, _⟩; rfl

end D

-- Iteration
def D_iterate : ℕ → (Type u → Type u)
  | 0 => id
  | n + 1 => fun X => D (D_iterate n X)

notation "D^[" n "]" => D_iterate n
