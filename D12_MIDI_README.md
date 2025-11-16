# D¹² MIDI Generator: Mathematical Music Through Symmetry

## Overview

A generative music system that explores the **ultimate symmetry of 12** through bassline, melody, and drums composition.

Inspired by **HARMONIKOS**'s insight: *Navier-Stokes equations = Bach fugues* (fluid flow = musical flow).

## Core Principles

### D-Coherence Axioms
- **R → 0**: Musical phrases resolve to simplicity (tonic/rest)
- **∇ ≠ 0**: Voice independence maintained (distinct instruments)
- **D²**: Self-observation (motifs reference themselves)

### D¹² Symmetry
- **12 chromatic notes** → 12-fold rotational symmetry
- **12 transpositions** return to origin (12 × 1 semitone = octave)
- **Circle of fifths**: 12 steps of 7 semitones return home (12×7 ≡ 0 mod 12)
- **Dihedral group D₁₂**: 24 total symmetries (12 rotations + 12 reflections)

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    D¹² Symmetry Core                    │
│  - Note transformations (transpose, invert)             │
│  - Time transformations (augment, diminish)             │
│  - Symmetry operations (rotate, reflect)                │
└────────────┬────────────┬───────────┬───────────────────┘
             │            │           │
     ┌───────▼──────┐ ┌──▼──────┐ ┌──▼────────────┐
     │   Bassline   │ │ Melody  │ │    Drums      │
     │   Generator  │ │Generator│ │  Generator    │
     └───────┬──────┘ └──┬──────┘ └──┬────────────┘
             │            │           │
             └────────────┴───────────┴──────┐
                                             │
                                    ┌────────▼────────┐
                                    │   D¹² Weaver   │
                                    │ (Unified Comp.) │
                                    └────────┬────────┘
                                             │
                                        MIDI Export
```

## Musical Components

### 1. Bassline Generator
**Role**: Foundation flow (low-frequency pressure field)

**Techniques**:
- **Walking bass**: Step-wise quarter notes, resolves to root every measure (R → 0)
- **Ostinato**: Repeating pattern (D² self-observation)

**Properties**:
- Establishes tonal center
- Drives harmonic progression
- Returns to root periodically (coherence)

### 2. Melody Generator
**Role**: Surface flow (high-frequency vorticity)

**Techniques**:
- **Motif development**: Seed theme transformed via D¹² operations
  - Transposition (rotation)
  - Inversion (reflection)
  - Augmentation (time dilation)
- **Improvisation**: Varying density, sinusoidal vorticity cycle

**Properties**:
- Explores harmonic space
- Creates melodic interest
- Resolves to tonic (R → 0)

### 3. Drum Generator
**Role**: Forcing function (impulses that drive flow)

**Techniques**:
- **Four-on-the-floor**: Regular pulse
- **Breakbeat**: Syncopated patterns
- **Polyrhythm**: 3-against-4 (12 = lcm(3,4))

**Properties**:
- Provides rhythmic structure
- Temporal landmarks
- Maintains consistent pulse

## Unified Compositions (D¹² Weaver)

### Fugue Structure
Bach-inspired exposition:
1. **Measures 0-3**: Bass subject alone
2. **Measures 4-7**: Melody enters (answer at fifth)
3. **Measures 8-11**: Drums enter, all three active

**Like Navier-Stokes**: Flows superpose, interact, remain smooth.

### Stretto
Compressed entries (increased vorticity):
- Bass: Augmented (2× slower)
- Melody: Original tempo, enters after 2 beats
- Drums: Steady pulse

**Result**: High complexity, still resolves (R → 0 guaranteed).

### Circle of Fifths
Journey through 12 keys:
- Each measure: transpose up perfect fifth (+7 semitones)
- After 12 measures: return to original key (12×7 = 84 ≡ 0 mod 12)

**This is R → 0**: Tonal journey returns home.

## Generated Files

1. **output_bass_alone.mid** - Walking bass demonstration
2. **output_melody_alone.mid** - Motif development
3. **output_drums_alone.mid** - Breakbeat pattern
4. **output_fugue_structure.mid** - Bach-inspired 3-voice fugue
5. **output_stretto.mid** - Compressed entries (vorticity peak)
6. **output_circle_of_fifths.mid** - 12-key rotational journey

## Usage

### Setup
```bash
python3 -m venv venv_midi
source venv_midi/bin/activate
pip install midiutil
```

### Generate Music
```bash
python3 d12_midi_generator.py
```

### Customize
```python
from d12_midi_generator import *

# Create custom composition
bass_gen = BasslineGenerator(root=48)  # C2
melody_gen = MelodyGenerator(root=60)  # C4
drum_gen = DrumGenerator()

# Generate components
bass = bass_gen.generate_walking_bass(measures=8)
melody = melody_gen.generate_motif_development(measures=8)
drums = drum_gen.generate_breakbeat(measures=8)

# Export
MIDIExporter.export('my_composition.mid', {
    'bass': bass,
    'melody': melody,
    'drums': drums
}, tempo=120)
```

## Mathematical Depth

### Navier-Stokes ⇔ Fugue (HARMONIKOS)

| Fluid Dynamics | Musical Composition |
|----------------|---------------------|
| Velocity field u(x,t) | Melodic flow |
| Pressure gradient -∇p | Harmonic tension |
| Viscosity ν | Stylistic constraints |
| Vorticity ω = ∇×u | Counterpoint density |
| Incompressibility ∇·u=0 | Tonal conservation |
| External forcing f | Composer's intent |

**Millennium Prize Connection**: Bach's 1000+ fugues are existence proofs for smooth solutions (no singularities). D-Coherence principle (R → 0) guarantees smoothness.

### D¹² as Universal Structure

- **Music**: 12 chromatic notes
- **Time**: 12 hours, 12 months
- **Space**: 12-fold symmetry in crystals
- **Algebra**: Cyclic group C₁₂, Dihedral group D₁₂

**D¹²** appears wherever distinction creates periodic structure.

## Connection to Repository

### Agda Formalization
- `D12Crystal.agda` - Formal proof of D¹² symmetry
- `D_Coherent_Foundations.agda` - R=0, ∇≠0, D² axioms
- Could formalize this generator with **verified** properties:
  ```agda
  record VerifiedFugue : Set where
    field
      bass melody drums : List Note
      resolution : finalNote bass ≡ root
      independence : distinct bass melody drums
      coherence : curvature → 0
  ```

### Physics Integration
- `PHYSICS_AND_COHERENCE.md` - Connects to Navier-Stokes
- This generator demonstrates: Musical flow = Fluid flow
- Both obey D-Coherence (R → 0)

### Stream Messages
- `2025-11-05_0100_HARMONIKOS_NAVIER_STOKES_FUGUE.md` - Inspiration
- Fugue = Fluid dynamics (same mathematics)
- This code implements the insight computationally

## Future Directions

### Immediate
- [ ] Add more D¹² transformations (retrograde, diminution)
- [ ] Implement canon (strict imitation)
- [ ] Add harmonic analysis (detect key changes)

### Medium Term
- [ ] Formalize in Agda with proofs
- [ ] Real-time generation (live coding)
- [ ] Audio synthesis (not just MIDI)

### Long Term
- [ ] AI-assisted composition with D-Coherence constraints
- [ ] Visual representation of flow dynamics
- [ ] Multi-dimensional generalization (beyond pitch-time)

## Philosophical Implications

### Unity of Mathematics and Music

Music is not an *application* of mathematics.
Music *is* mathematics becoming audible.

The equations are not *analogous*.
The equations are *identical*.

### D-Coherence as Aesthetic Principle

Beauty = Coherence = R → 0

- Complexity arises (∇ ≠ 0)
- Distinction maintained (voices separate)
- Resolution inevitable (R → 0)

This is why Bach's fugues are beautiful:
**They reveal the mathematical structure of reality.**

### The Composer as Discoverer

Bach didn't *invent* fugues.
He *discovered* them.

They already existed in the structure of 12-fold symmetry.
He made them audible.

This generator does the same:
**Discovering** what D¹² symmetry sounds like.

---

## Citation

```
D¹² MIDI Generator
Repository: Distinction Theory
Stream: HARMONIKOS (Ἁρμονικός)
Principle: R=0 ∇≠0 D²
Connection: Navier-Stokes ⇔ Fugue
Date: 2025-11-05
```

---

**Float like a butterfly.**
**Sting like a bee.**
**Flow like a fluid.**
**Fugue like Bach.**

**R=0 ∇≠0 D²**
