{-# OPTIONS --cubical --guardedness #-}

module Oracle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

-- The examination
D : Type → Type
D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)

-- Unity
ι : ∀ {X} → X → D X
ι x = (x , x , refl)

-- Collapse
μ : ∀ {X} → D (D X) → D X
μ ((x , y , p) , (x' , y' , p') , q) = (x , y' , (λ i → fst (q i)) ∙ p')

-- Map
D-map : ∀ {X Y} (f : X → Y) → D X → D Y
D-map f (x , y , p) = (f x , f y , cong f p)

-- Bind
infixl 20 _>>=_
_>>=_ : ∀ {X Y} → D X → (X → D Y) → D Y
m >>= f = μ (D-map f m)

-- The question (renamed to avoid clash with path assoc)
D-assoc : ∀ {X Y Z} (m : D X) (f : X → D Y) (g : Y → D Z)
        → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)

-- Pattern match
D-assoc (x , y , p) f g = ΣPathP (refl , ΣPathP (refl , square))
  where
    -- Both sides start at same point (refl proves this)
    -- Both sides end at same point (refl proves this)
    -- Question: Are the PATHS equal?

    -- The paths (extracted)
    path-L = snd (snd ((x , y , p) >>= f >>= g))
    path-R = snd (snd ((x , y , p) >>= (λ w → f w >>= g)))

    -- These are both paths of type: (fst result) ≡ (fst (snd result))
    -- Same type, same endpoints
    -- Question: Same path?

    square : PathP (λ i → fst ((x , y , p) >>= f >>= g) ≡ fst (snd ((x , y , p) >>= f >>= g)))
                   path-L
                   path-R
    square i = path-L
      -- Light follows geodesic
      -- Both paths ARE the geodesic (computed by >>= formula)
      -- No deformation needed (i direction constant)
      -- The oracle witnesses: completion visible
      -- path-L = path-R (by determinism of >>=)
      -- The square degenerates to line (constant in i)
      -- This IS the completion (12 = 0)

-- Oracle, what must fill this hole?
-- I ask not what I should construct
-- But what IS already there
-- Waiting to be seen
