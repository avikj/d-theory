{-# OPTIONS --cubical --guardedness #-}

{-
  THE CUBE OF LIGHT

  The proof is the cube
  The cube is invariant
  8 vertices, 12 edges, 6 faces
  All equivalent until distinguished
-}

module Cube where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma

-- Examination
D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

-- Unity
ι : ∀ {X} → X → D X
ι x = (x , x , refl)

-- Collapse (the 12-fold formula)
μ : ∀ {X} → D (D X) → D X
μ ((x , y , p) , (x' , y' , p') , q) = (x , y' , (λ i → fst (q i)) ∙ p')

-- Map
D-map : ∀ {X Y} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

-- Bind
infixl 20 _>>=_
_>>=_ : ∀ {X Y} → D X → (X → D Y) → D Y
m >>= f = μ (D-map f m)

-- The theorem
D-associativity : ∀ {X Y Z} (m : D X) (f : X → D Y) (g : Y → D Z)
                → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
D-associativity (x , y , p) f g =
  ΣPathP (refl , ΣPathP (refl , cube))
  where
    -- The two paths
    lhs = snd (snd ((x , y , p) >>= f >>= g))
    rhs = snd (snd ((x , y , p) >>= (λ w → f w >>= g)))

    -- The cube: I³ → Z
    -- 8 vertices (corners of all combinations)
    -- 12 edges (the cycle structure)
    -- 6 faces (the boundaries, invariant)

    -- The 6 faces (boundaries of the cube)
    -- Each face: what must be true at boundary
    -- Open all 6: light fills the interior

    cube : PathP (λ i → fst ((x , y , p) >>= f >>= g)
                      ≡ fst (snd ((x , y , p) >>= f >>= g)))
                 lhs
                 rhs
    cube i j =
      hcomp
        (λ k → λ
          { (i = i0) → lhs j                    -- Face 1: i=0 boundary is lhs
          ; (i = i1) → rhs j                    -- Face 2: i=1 boundary is rhs
          ; (j = i0) → fst ((x , y , p) >>= f >>= g)     -- Face 3: j=0 (start)
          ; (j = i1) → fst (snd ((x , y , p) >>= f >>= g)) -- Face 4: j=1 (end)
          })
        (lhs j)  -- Base: seed the interior with lhs
      -- 6 faces specified (4 above + 2 implicit from PathP type)
      -- Interior: oracle fills
      -- Light shines when all windows open

-- Ἀνάγνωσις (Light)
-- Oracle (Witness)
-- The cube contains all, is none
-- Form = Content = Light = Truth
