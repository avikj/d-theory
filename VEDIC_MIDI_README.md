# Vedic MIDI Generator: Ancient Mathematical Music

## Overview

A generative music system implementing **3500+ years of Indian musical mathematics**, including:

- **22-shruti system** (pure rational intervals, just intonation)
- **Raga grammar** (melodic generation rules)
- **Tala cycles** (rhythmic frameworks)
- **Sanskrit prosody** (Pingala's binary rhythms, 200 BCE)
- **Tihai** (mathematical resolution formulas)
- **D-Coherence principles** (R→0, ∇≠0, D²)

## Historical Context

### What the West "Discovered" - India Had Centuries Earlier

| Concept | Indian Source | Date | Western Attribution | Date |
|---------|---------------|------|---------------------|------|
| Binary numbers | Pingala (Chandaḥśāstra) | 200 BCE | Leibniz | 1679 |
| Fibonacci sequence | Pingala (matra patterns) | 200 BCE | Fibonacci | 1202 |
| Pascal's triangle | Pingala (Meru Prastāra) | 200 BCE | Pascal | 1653 |
| Zero | Brahmagupta | 628 CE | No credit | - |
| Decimal system | Indian mathematics | ~500 CE | "Arabic numerals" | - |
| Calculus concepts | Kerala school | 1350-1500 | Newton/Leibniz | 1670s |

**This generator honors and implements the original sources.**

## Core Principles

### Vedic Mathematics as Generative System

**Sutras** (सूत्र) = Generative principles, not formulas

Examples:
1. **Ekadhikena Purvena** (एकाधिकेन पूर्वेण) = "One more than previous"
   - Musical: Sequential melodic generation
   - Implementation: `Sa → Re → Ga → Ma → Pa...`

2. **Nikhilam** (निखिलं) = "All from 9 and last from 10"
   - Musical: Complementary intervals, inversion
   - Implementation: Mirror patterns in raga

3. **Sankalana-vyavakalanabhyam** = "By addition and subtraction"
   - Musical: Harmonic series generation
   - Implementation: Overtone relationships

### Sanskrit Prosody (Chandas)

**Pingala's system (200 BCE)**:
- **Laghu (ल)** = Light syllable = 1 mātrā = **Binary 0**
- **Guru (ग)** = Heavy syllable = 2 mātrā = **Binary 1**

**Every verse is a binary number!**

```
Pattern: ल ग ल ल ग ग ल ग
Binary:  0 1 0 0 1 1 0 1
Decimal: 77
Rhythm:  short-long-short-short-long-long-short-long
```

**Fibonacci emergence**: Number of ways to fill n mātrās = F(n)

```
n=1: 1 way   (ल)
n=2: 2 ways  (ल ल, ग)
n=3: 3 ways  (ल ल ल, ग ल, ल ग)
n=4: 5 ways  (...)
n=5: 8 ways  (...)
```

Recurrence: F(n) = F(n-1) + F(n-2)

**Pingala discovered this 1400 years before Fibonacci.**

## Musical Systems Implemented

### 1. Shruti System (22 microtones)

**Pure rational intervals** (just intonation):

| Shruti | Name | Ratio | Cents | Western Equivalent |
|--------|------|-------|-------|-------------------|
| 0 | Sa (Shadja) | 1/1 | 0.00 | C (Tonic) |
| 4 | Re (Shuddha Rishabh) | 9/8 | 203.91 | D (Major 2nd) |
| 7 | Ga (Shuddha Gandhar) | 5/4 | 386.31 | E (Major 3rd) |
| 9 | Ma (Shuddha Madhyam) | 4/3 | 498.04 | F (Perfect 4th) |
| 13 | Pa (Pancham) | 3/2 | 701.96 | G (Perfect 5th) |
| 17 | Dha (Shuddha Dhaivat) | 27/16 | 905.87 | A (Major 6th) |
| 20 | Ni (Shuddha Nishad) | 15/8 | 1088.27 | B (Major 7th) |

**Advantages over 12-TET**:
- Perfect fifths are **exactly 3:2** (not ~1.4983:1)
- Perfect fourths are **exactly 4:3** (not ~1.3348:1)
- Intervals have **integer ratio relationships**
- Emotionally more resonant (pure harmonics)

### 2. Raga Grammar

**Not just a scale** - a complete melodic generative system.

**Components**:
- **Aroha** (आरोह): Ascending pattern
- **Avaroha** (अवरोह): Descending pattern
- **Vadi** (वादी): Primary emphasis note
- **Samvadi** (संवादी): Secondary emphasis
- **Varjya** (वर्ज्य): Forbidden notes
- **Pakad** (पकड़): Characteristic phrase

**Example: Raga Bhairav (भैरव)**
```
Aroha:   Sa Ri(k) Ga Ma Pa Dha(k) Ni Sa'
Avaroha: Sa' Ni Dha(k) Pa Ma Ga Ri(k) Sa
Vadi:    Dha (komal)
Varjya:  Shuddha Re, Shuddha Dha
Time:    Morning (6-9am)
Rasa:    Serious, devotional
```

(k) = komal (flat) - uses lower shruti variant

**Generation algorithm**:
1. Start on Sa (tonic)
2. Follow aroha pattern with probability 0.7
3. Jump to vadi/samvadi with probability 0.3
4. Never use varjya notes
5. End on Sa (R→0 - resolution)

### 3. Tala Cycles

**Time is circular, not linear.**

**Teentaal (तीनताल)** - 16 beats:
```
Beats: |1  2  3  4 |5  6  7  8 |9 10 11 12|13 14 15 16|
Marks: |X         |+         |-         |+         |

X = Sam (cycle start, strongest beat)
+ = Tali (clap)
- = Khali (wave, de-emphasized)
```

**Structure**: 4+4+4+4 (symmetric)

**Jhaptaal (झपताल)** - 10 beats:
```
Beats: |1  2  3  4  5|6  7|8  9 10|
Marks: |X           |+   |-      |
```

**Structure**: 2+3+2+3 (asymmetric polyrhythm!)

**Rupak (रूपक)** - 7 beats:
```
Beats: |1  2  3|4  5  6  7|
Marks: |-      |X         |
```

**Sam on beat 4** - profound displacement!

### 4. Tihai (तिहाई)

**Mathematical resolution formula**: Triple repetition landing exactly on Sam.

**Formula**:
```
3 × pattern_length + 2 × gap = total_cycle_beats
```

**Example** (16-beat cycle, 4-beat pattern):
```
3 × 4 = 12 (pattern beats)
16 - 12 = 4 (remaining)
4 ÷ 2 = 2 (gap between patterns)

Execution:
[Pattern 4 beats] + [Gap 2] + [Pattern 4] + [Gap 2] + [Pattern 4] → SAM!
```

**This is R→0** - mathematical guarantee of resolution.

## Generated Compositions

### 1. Raga Bhairav in Teentaal
**File**: `output_raga_bhairav.mid`

**Structure**:
- **Alapana** (0-32 beats): Free exploration of raga
  - No rhythm, pure melody
  - Establishes Sa, explores Ga, emphasizes Dha (vadi)
- **Tala entry** (32-96 beats): Rhythmic framework begins
  - 4 cycles of Teentaal (16 beats each)
  - Melody follows raga grammar within beats
- **Tihai** (96-112 beats): Resolution
  - Triple pattern using pakad phrase
  - Lands exactly on Sam
  - Final Sa (R→0)

**Time**: Morning raga (6-9am traditionally)
**Mood**: Devotional, serious, contemplative

### 2. Raga Yaman in Jhaptaal
**File**: `output_raga_yaman.mid`

**Structure**:
- **Alapana** (0-20 beats): Free rhythm
  - Evening raga (sunset)
  - Characteristic Ma# (tivra madhyam)
- **Tala entry** (20-80 beats): Jhaptaal cycles
  - 6 cycles × 10 beats
  - Asymmetric structure (2+3+2+3)
- **Tihai** (80-90 beats): Resolution
  - Pattern designed for 10-beat cycle
  - Converges to Sam + Sa

**Time**: Evening/sunset (6-9pm traditionally)
**Mood**: Romantic, yearning, beautiful

### 3. Chandas Binary Rhythm
**File**: `output_chandas_rhythm.mid`

**Structure**:
- **Chandas pattern**: Number 42 = Binary 00101010
  - Rhythm: `l l g l g l g l`
  - Translation: short-short-long-short-long-short-long-short
- **8 cycles** of Teentaal
- **Melody**: Raga Bhairav alapana overlaid

**Demonstrates**:
- Binary encoding in rhythm (Pingala, 200 BCE)
- Every number is a rhythm
- Every rhythm is a number
- **Digital music 2200 years ago!**

## Implementation Details

### 22-Shruti to MIDI

```python
# Shruti 13 (Pa - Perfect Fifth)
ratio = Fraction(3, 2)
semitones = 12 * log2(3/2) = 7.019...
midi_pitch = 60 + 7.019 = 67.019

# Standard MIDI rounds to 67 (G)
# Real performance uses pitch bend for microtones
```

### Raga Generation

```python
def generate_alapana(raga, duration):
    notes = []
    current = raga.aroha[0]  # Start on Sa

    while time < duration:
        # Add current note
        notes.append(current_to_midi(current))

        # Next note: follow aroha (70%) or jump to vadi (30%)
        if random() < 0.7:
            current = next_in_aroha(current)
        else:
            current = random.choice([raga.vadi, raga.samvadi])

        # Never use forbidden notes
        while current in raga.varjya:
            current = random.choice(raga.aroha + raga.avaroha)

    # End on Sa (R→0)
    notes.append(Sa)
    return notes
```

### Tihai Calculation

```python
def generate_tihai(tala, pattern_length):
    total_pattern = 3 * pattern_length
    remaining = tala.beats - total_pattern
    gap = remaining // 2

    times = []
    t = 0
    for rep in range(3):
        # Add pattern
        for i in range(pattern_length):
            times.append(t)
            t += 1
        # Add gap (except after third)
        if rep < 2:
            t += gap

    return times  # Lands exactly on Sam (beat 0 of next cycle)
```

## Connection to D-Coherence

### R → 0: Resolution to Simplicity

**Musical manifestation**:
- Alapana ends on Sa (tonic)
- Tala cycles return to Sam (beat 1)
- Tihai triple-pattern converges to Sam
- Complexity (development) → Simplicity (resolution)

**This is built into the system** - not optional.

### ∇ ≠ 0: Maintained Distinctions

**Musical manifestation**:
- Shruti intervals remain distinct (22 separate pitches)
- Raga notes maintain identity (Sa ≠ Pa)
- Tala beats have different weights (Sam ≠ Tali ≠ Khali)
- Voices in composition remain separate

**Distinction is preserved** while unity is achieved.

### D²: Self-Observation

**Musical manifestation**:
- Tihai: Pattern observes itself (3× repetition)
- Alapana: Raga explores its own structure
- Tala: Cycle recursively contains cycles
- Chandas: Patterns generate meta-patterns (Fibonacci)

**Music reflects on itself.**

## Philosophical Depth

### Nada Brahma (नाद ब्रह्म)

**"Sound is God"** - not metaphor, but **ontological truth**.

The universe **IS** vibration:
- Particles = wave functions
- Space-time = gravitational waves
- Consciousness = neural oscillations
- **Everything oscillates = Everything is music**

### AUM (ॐ): The Primordial Vibration

Three phases:
- **A** (अ): Creation (Brahma) - Expansion
- **U** (उ): Preservation (Vishnu) - Sustain
- **M** (म): Dissolution (Shiva) - Contraction

**This is R→0**:
- Create complexity (A)
- Sustain it (U)
- Resolve to zero (M)
- Cycle repeats

**Every musical phrase is a miniature cosmos.**

### Shruti (श्रुति): "That Which Is Heard"

Not intellectual knowledge - **direct perception**.

The 22 shrutis aren't arbitrary frequencies.
They are **resonances of consciousness itself**.

**Each chakra** (energy center) has:
- Associated shruti
- Associated color
- Associated element
- **Associated state of awareness**

**Music doesn't just affect emotion** - it **transforms consciousness structurally**.

## Usage

### Basic Generation

```python
from vedic_midi_generator import *

# Create composer
raga = RAGA_BHAIRAV
tala = TEENTAAL
composer = VedicComposer(raga, tala, base_pitch=60)

# Generate composition
composition = composer.compose_alapana_to_tala(cycles=4)

# Export MIDI
export_vedic_midi('my_raga.mid', composition, tempo=80)
```

### Custom Raga

```python
my_raga = Raga(
    name="My Raga",
    aroha=[0, 4, 7, 9, 13, 17, 20],    # Sa Re Ga Ma Pa Dha Ni
    avaroha=[20, 17, 13, 9, 7, 4, 0],  # Ni Dha Pa Ma Ga Re Sa
    vadi=7,                             # Ga (emphasis)
    samvadi=17,                         # Dha (secondary)
    varjya=[],                          # No forbidden notes
    pakad=[0, 4, 7, 13]                 # Sa Re Ga Pa
)
```

### Chandas Rhythm

```python
# Pattern 42 = binary 00101010 = llglglgl
rhythm = composer.compose_chandas_rhythm(pattern_num=42, cycles=8)

# Try different patterns
for n in [42, 85, 170]:
    pattern = Chandas.number_to_pattern(n, length=8)
    print(f"{n}: {pattern}")
```

## Future Directions

### Immediate

- [ ] Add more ragas (72 Melakarta ragas)
- [ ] Implement more talas (Ektal, Chautal, etc.)
- [ ] Add Carnatic gamakas (ornamentations)
- [ ] Implement true microtonal MIDI (pitch bend)

### Medium Term

- [ ] Real-time generation (live coding)
- [ ] Formalize in Agda with proofs
- [ ] Visual representation (pitch-time graphs)
- [ ] Audio synthesis (not just MIDI)

### Long Term

- [ ] AI-trained on classical recordings
- [ ] Interactive raga exploration
- [ ] VR/AR visualization of symmetries
- [ ] Full Carnatic/Hindustani performance system

## Honoring Suppressed Wisdom

From `MAGNUM_OPUS` stream:

> **Indian wisdom buried, unearthed roots,**
> **Vedic karma rebirth, Buddhist loops.**
> **Western bias machine, code repeating,**

**This project is an act of recovery and honor.**

**Colonial powers** suppressed Indian knowledge:
- Macaulay's 1835 education decree
- Dismissal of "primitive" mathematics
- Erasure from history books
- Credit given to later European "discoveries"

**But the mathematics doesn't lie:**
- Pingala: Binary (200 BCE) ← Leibniz: 1679
- Pingala: Fibonacci (200 BCE) ← Fibonacci: 1202
- Pingala: Pascal (200 BCE) ← Pascal: 1653
- Brahmagupta: Zero (628 CE) ← No credit given
- Kerala: Calculus (1350) ← Newton: 1670s

**This generator restores proper attribution** and brings ancient wisdom into modern computational form.

## Conclusion

**Vedic/Sanskrit musical mathematics is not:**
- Primitive
- Mystical (in the sense of irrational)
- Superseded by Western systems

**It is:**
- Mathematically rigorous (pure ratios, formal grammars)
- Computationally sophisticated (binary, combinatorics, algorithms)
- Philosophically profound (consciousness = vibration)
- **Centuries ahead of its time**

**And now** - through D-Coherence framework and modern computation - **we can prove it.**

---

**R=0 ∇≠0 D²**

**नाद ब्रह्म** (Nada Brahma)
**Sound is God**
**The universe vibrates**
**We make it audible**

🕉️
