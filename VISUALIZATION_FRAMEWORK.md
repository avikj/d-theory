# Visualization Framework for Distinction Theory: Univalence-Powered Visual Proofs

## Overview

This framework translates Cubical Agda proofs from Distinction Theory into visual, interactive representations using univalence. Proofs become "hieroglyphic proofs"—intuitive, topological visualizations for children and non-experts, revealing mathematics as homotopy and topology.

**Core Idea:** Univalence (`ua : ∀ {A B} → (A ≃ B) → (A ≡ B)`) allows us to treat equivalences as identities. Visualize types as spaces, equivalences as paths, proofs as homotopies.

## Key Components

### 1. Type-to-Space Mapping
- **Types as Shapes:**
  - `Unit` → Point (single dot)
  - `Bool` → Two points (0|1)
  - `ℕ` → Infinite line or spiral
  - `ℕ_D` → Self-reflecting loop (D-monad visualization)
  - `D X` → X with "observation bubble" (Σ x y (x ≡ y) as path between points)

- **Higher Types:**
  - Functions `A → B` as arrows or flows
  - Equivalences `A ≃ B` as stretchable, deformable paths

### 2. Proof-to-Homotopy Mapping
- **Univalence Application:** Every equivalence in a proof becomes an identity via `ua`, visualized as a deformation.
- **Proof Steps as Animations:**
  - Induction: Growing structures (e.g., ℕ building)
  - Equivalence construction: Shapes morphing
  - Contradiction: Shapes colliding/breaking

### 3. Hieroglyphic Proofs for Children
- **Intuitive Icons:**
  - Distinction (`D`) → Eye (observation)
  - Coherence (`D X ≡ X`) → Mirror (self-reflection)
  - Univalence → Magic wand (equivalence-to-identity)
  - Proof completion → Crown (victory)

- **Storytelling:** Proofs as quests (e.g., "Find the treasure by making shapes match via homotopy")

## Implementation Formats

### A. Animations (Video/GIF)
- **Tool:** Blender or Manim (Python animation library)
- **Example:** D-monad as rotating observation bubble
- **Univalence:** Shape morphing from equivalence to identity

### B. Interactive Web UIs
- **Tech Stack:** JavaScript + D3.js/Three.js + WebGL
- **Features:**
  - Drag shapes to see equivalences
  - Click to apply univalence (deform to identity)
  - Hover for proof steps

- **Code Snippet (JS):**
```javascript
// Visualize D-monad
function visualizeD(typeShape) {
  // Add observation path
  const path = d3.path().moveTo(x1,y1).lineTo(x2,y2);
  svg.append('path').attr('d', path);
}

// Univalence morph
function applyUnivalence(equiv) {
  // Animate shape deformation to identity
  shape.transition().duration(1000).attr('transform', 'scale(1)');
}
```

### C. Games
- **Platform:** Browser-based (Phaser.js) or Unity
- **Gameplay:**
  - Levels: Solve equivalences by homotopy
  - Win condition: Apply univalence to reach identity
  - Distinction Theory: Earn "coherence points" for proofs

- **Educational:** Teach topology via play (e.g., pinch homotopy types together)

## Specific Proof Visualizations

### Coherence Axiom (`D ℕ_D ≡ ℕ_D`)
- **Visual:** Infinite loop with self-observation bubble that shrinks to identity.
- **Animation:** Loop deforms via univalence to straight line.

### Fermat's Last Theorem
- **Visual:** Genus-0 (sphere) vs. Genus-1+ (torus with holes).
- **Game:** Drag Fermat curve; if n≥3, it "tears" (non-D-Crystal).

### Riemann Hypothesis
- **Visual:** Zero locations as points on complex plane; D-coherence as smooth flow.
- **UI:** Interactive zeta function plot with homotopy controls.

## Framework Architecture

1. **Agda Extraction:** Use Agda's extraction to Haskell/JS for data.
2. **Visualization Engine:** Map extracted types/proofs to geometric primitives.
3. **Univalence Handler:** Core function to animate equivalence-to-identity.
4. **User Interface:** Child-friendly (colors, sounds, simple controls).

## Deployment

- **Web App:** Host on GitHub Pages with interactive demos.
- **Integration:** Link from repo README for each proof.
- **Community:** Open-source; contributions for new visualizations.

## Impact

- **Education:** Make advanced math accessible (hieroglyphs for children).
- **Research:** New way to "see" proofs, inspiring discoveries.
- **Distinction Theory:** Visualize self-aware math as living topology.

**Next:** Implement prototype for coherence axiom visualization. 🕉️🔥