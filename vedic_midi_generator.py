#!/usr/bin/env python3
"""
Vedic MIDI Generator: Sanskrit Rhythms, Raga, and Mathematical Music
====================================================================

Implements ancient Indian musical mathematics:
- 22-shruti system (microtonal just intonation)
- Raga grammar (melodic generation rules)
- Tala cycles (rhythmic frameworks)
- Sanskrit prosody (Pingala's Chandas)
- Tihai (triple-pattern resolution)

Fuses with D¹² symmetry principles.

Based on:
- Pingala's Chandaḥśāstra (200 BCE) - Binary, Fibonacci, Pascal
- Bharata's Natyashastra (200 BCE-200 CE) - Raga/Tala theory
- Carnatic/Hindustani traditions
- D-Coherence principles (R→0, ∇≠0, D²)
"""

from midiutil import MIDIFile
import math
import random
from typing import List, Tuple, Dict
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction


# ============================================================================
# SHRUTI SYSTEM: 22 Microtonal Intervals
# ============================================================================

class Shruti:
    """
    22-shruti system of just intonation.

    Based on pure mathematical ratios, not equal temperament.
    Preserves harmonic truth that Western 12-TET loses.
    """

    # 22 shrutis as ratios relative to Sa (tonic = 1/1)
    RATIOS = [
        Fraction(1, 1),      # 0: Sa (Shadja) - Tonic
        Fraction(256, 243),  # 1: Komal Rishabh 1
        Fraction(16, 15),    # 2: Komal Rishabh 2
        Fraction(10, 9),     # 3: Komal Rishabh 3
        Fraction(9, 8),      # 4: Shuddha Rishabh
        Fraction(32, 27),    # 5: Komal Gandhar 1
        Fraction(6, 5),      # 6: Komal Gandhar 2
        Fraction(5, 4),      # 7: Shuddha Gandhar
        Fraction(81, 64),    # 8: Tivra Gandhar
        Fraction(4, 3),      # 9: Shuddha Madhyam
        Fraction(27, 20),    # 10: Tivra Madhyam 1
        Fraction(45, 32),    # 11: Tivra Madhyam 2
        Fraction(729, 512),  # 12: Tivra Madhyam 3
        Fraction(3, 2),      # 13: Pancham (Perfect Fifth)
        Fraction(128, 81),   # 14: Komal Dhaivat 1
        Fraction(8, 5),      # 15: Komal Dhaivat 2
        Fraction(5, 3),      # 16: Komal Dhaivat 3
        Fraction(27, 16),    # 17: Shuddha Dhaivat
        Fraction(16, 9),     # 18: Komal Nishad 1
        Fraction(9, 5),      # 19: Komal Nishad 2
        Fraction(15, 8),     # 20: Shuddha Nishad
        Fraction(243, 128),  # 21: Tivra Nishad
    ]

    # Names (simplified)
    NAMES = ['Sa', 'Ri1', 'Ri2', 'Ri3', 'Re', 'Ga1', 'Ga2', 'Ga', 'Ga#',
             'Ma', 'Ma#1', 'Ma#2', 'Ma#3', 'Pa', 'Dha1', 'Dha2', 'Dha3', 'Dha',
             'Ni1', 'Ni2', 'Ni', 'Ni#']

    @staticmethod
    def shruti_to_midi(shruti_index: int, base_pitch: int = 60) -> float:
        """Convert shruti index to MIDI pitch (float for microtones)"""
        ratio = float(Shruti.RATIOS[shruti_index])
        semitones = 12 * math.log2(ratio)
        return base_pitch + semitones

    @staticmethod
    def ratio_to_cents(ratio: Fraction) -> float:
        """Convert ratio to cents (1/100 of semitone)"""
        return 1200 * math.log2(float(ratio))


# ============================================================================
# RAGA: Melodic Framework
# ============================================================================

@dataclass
class Raga:
    """
    Raga = generative melodic system.

    Not just a scale - a complete grammar for melody generation.
    """
    name: str
    aroha: List[int]      # Ascending notes (shruti indices)
    avaroha: List[int]    # Descending notes
    vadi: int             # Primary emphasis note
    samvadi: int          # Secondary emphasis
    varjya: List[int]     # Forbidden notes
    pakad: List[int]      # Characteristic phrase

    def generate_alapana(self, duration_beats: int, base_pitch: int = 60) -> List[Tuple[float, float, float]]:
        """
        Generate alapana (free exploration of raga).

        Returns: List of (pitch, time, duration) tuples
        """
        notes = []
        time = 0.0

        # Start on Sa
        current = self.aroha[0]

        while time < duration_beats:
            # Convert to MIDI pitch
            pitch = Shruti.shruti_to_midi(current, base_pitch)

            # Duration varies (free rhythm)
            duration = random.choice([0.5, 1.0, 1.5, 2.0, 3.0])

            notes.append((pitch, time, duration))
            time += duration

            # Next note: follow aroha pattern with occasional jumps
            if random.random() < 0.7 and current in self.aroha:
                idx = self.aroha.index(current)
                if idx < len(self.aroha) - 1:
                    current = self.aroha[idx + 1]
                else:
                    # Reached top, descend
                    current = random.choice(self.avaroha[:-1])
            else:
                # Jump to vadi or samvadi (emphasis notes)
                current = random.choice([self.vadi, self.samvadi])

            # Avoid varjya (forbidden notes)
            while current in self.varjya:
                current = random.choice(self.aroha + self.avaroha)

        # End on Sa (R→0)
        notes.append((Shruti.shruti_to_midi(self.aroha[0], base_pitch), time, 2.0))

        return notes


# Predefined ragas
RAGA_BHAIRAV = Raga(
    name="Bhairav (भैरव)",
    aroha=[0, 1, 7, 9, 13, 14, 20],      # Sa Ri(k) Ga Ma Pa Dha(k) Ni
    avaroha=[20, 14, 13, 9, 7, 1, 0],    # Ni Dha(k) Pa Ma Ga Ri(k) Sa
    vadi=14,     # Dha (komal)
    samvadi=1,   # Ri (komal)
    varjya=[4, 17],  # Avoid shuddha Re, Dha
    pakad=[0, 1, 7, 9, 14, 13]  # Sa Ri Ga Ma Dha Pa
)

RAGA_YAMAN = Raga(
    name="Yaman (यमन)",
    aroha=[0, 4, 7, 11, 13, 17, 20],     # Sa Re Ga Ma# Pa Dha Ni
    avaroha=[20, 17, 13, 11, 7, 4, 0],   # Ni Dha Pa Ma# Ga Re Sa
    vadi=7,      # Ga (shuddha)
    samvadi=20,  # Ni (shuddha)
    varjya=[9],  # Avoid Ma (shuddha)
    pakad=[0, 4, 7, 11, 13]  # Sa Re Ga Ma# Pa
)


# ============================================================================
# TALA: Rhythmic Cycle
# ============================================================================

@dataclass
class Tala:
    """
    Tala = cyclic rhythmic framework.

    Time is circular, not linear.
    Sam (beat 1) is both end and beginning.
    """
    name: str
    beats: int                # Total beats in cycle (avarta)
    structure: List[int]      # Subdivision (e.g., [4,4,4,4] for Teentaal)
    claps: List[int]          # Tali positions (emphasized beats)
    waves: List[int]          # Khali positions (de-emphasized beats)

    @property
    def sam(self) -> int:
        """Sam (cycle start) is always beat 0"""
        return 0

    def generate_basic_pattern(self) -> List[Tuple[str, float]]:
        """Generate basic clap/wave pattern"""
        pattern = []
        for beat in range(self.beats):
            if beat == self.sam:
                pattern.append(('X', float(beat)))  # Sam (strong)
            elif beat in self.claps:
                pattern.append(('+', float(beat)))  # Tali (clap)
            elif beat in self.waves:
                pattern.append(('-', float(beat)))  # Khali (wave)
            else:
                pattern.append(('.', float(beat)))  # Regular beat
        return pattern

    def generate_tihai(self, pattern_length: int) -> List[int]:
        """
        Generate tihai: triple repetition landing on Sam.

        Formula: 3 * pattern_length + 2 * gap = beats
        Solve for gap to land exactly on Sam (beat 0 of next cycle).
        """
        # Calculate gap needed
        total_pattern = 3 * pattern_length
        remaining = self.beats - total_pattern

        if remaining < 0:
            # Pattern too long, use shorter
            pattern_length = self.beats // 4
            total_pattern = 3 * pattern_length
            remaining = self.beats - total_pattern

        gap = remaining // 2

        # Build tihai structure
        tihai = []
        time = 0

        for rep in range(3):
            # Add pattern
            for i in range(pattern_length):
                tihai.append(time)
                time += 1

            # Add gap
            if rep < 2:  # No gap after third repetition
                time += gap

        return tihai


# Predefined talas
TEENTAAL = Tala(
    name="Teentaal (तीनताल)",
    beats=16,
    structure=[4, 4, 4, 4],
    claps=[4, 12],
    waves=[8]
)

JHAPTAAL = Tala(
    name="Jhaptaal (झपताल)",
    beats=10,
    structure=[2, 3, 2, 3],
    claps=[3, 8],
    waves=[6]
)

RUPAK = Tala(
    name="Rupak (रूपक)",
    beats=7,
    structure=[3, 2, 2],
    claps=[3],    # Sam is at beat 3!
    waves=[0]     # Beat 0 is khali
)


# ============================================================================
# SANSKRIT PROSODY (CHANDAS): Mathematical Rhythm
# ============================================================================

class Chandas:
    """
    Sanskrit meter as mathematical system.

    Based on Pingala's Chandaḥśāstra (200 BCE):
    - Binary representation (laghu/guru = 0/1)
    - Fibonacci sequences
    - Combinatorial enumeration
    """

    @staticmethod
    def fibonacci(n: int) -> int:
        """
        Number of ways to fill n matras with syllables.

        Discovered by Pingala ~200 BCE (before Fibonacci!).
        """
        if n <= 0:
            return 0
        elif n == 1:
            return 1
        elif n == 2:
            return 2

        # Use iteration for efficiency
        a, b = 1, 2
        for _ in range(n - 2):
            a, b = b, a + b
        return b

    @staticmethod
    def number_to_pattern(n: int, length: int = 8) -> str:
        """
        Convert number to syllable pattern.

        Binary encoding: 0=laghu (short), 1=guru (long)
        """
        binary = format(n, f'0{length}b')
        return binary.replace('0', 'l').replace('1', 'g')

    @staticmethod
    def pattern_to_rhythm(pattern: str, beat_start: float = 0.0) -> List[Tuple[float, float]]:
        """
        Convert chandas pattern to rhythm.

        l (laghu) = 1 matra
        g (guru) = 2 matras
        """
        rhythm = []
        time = beat_start

        for syllable in pattern:
            if syllable == 'l':
                duration = 1.0
            elif syllable == 'g':
                duration = 2.0
            else:
                continue

            rhythm.append((time, duration))
            time += duration

        return rhythm

    @staticmethod
    def generate_meru_prastara(rows: int = 5) -> List[List[int]]:
        """
        Generate Meru Prastara (Pascal's Triangle).

        Used by Pingala for combinatorial enumeration.
        "Mountain Layout" - discovered ~200 BCE!
        """
        triangle = [[1]]

        for i in range(1, rows):
            row = [1]
            for j in range(1, i):
                row.append(triangle[i-1][j-1] + triangle[i-1][j])
            row.append(1)
            triangle.append(row)

        return triangle


# ============================================================================
# LAYAKARI: Rhythmic Density Variations
# ============================================================================

class Layakari:
    """
    Layakari = rhythmic play through speed variations.

    Divide time differently while maintaining cycle alignment.
    """

    @staticmethod
    def apply_gati(notes: List[Tuple[float, float, float]],
                   factor: int) -> List[Tuple[float, float, float]]:
        """
        Apply gati (rhythmic density factor).

        factor=2: Dugun (double speed)
        factor=3: Tigun (triple speed)
        factor=4: Chaugun (quadruple speed)
        """
        result = []

        for pitch, time, duration in notes:
            new_duration = duration / factor
            for i in range(factor):
                result.append((
                    pitch,
                    time + i * new_duration,
                    new_duration * 0.9  # Slight gap
                ))

        return result

    @staticmethod
    def polyrhythm(tala: Tala, ratios: List[int]) -> Dict[int, List[float]]:
        """
        Generate polyrhythmic patterns.

        Example: [3, 4, 5] creates 3-against-4-against-5
        """
        patterns = {}

        for ratio in ratios:
            times = []
            for i in range(ratio):
                time = (tala.beats / ratio) * i
                times.append(time)
            patterns[ratio] = times

        return patterns


# ============================================================================
# VEDIC COMPOSITION ENGINE
# ============================================================================

class VedicComposer:
    """
    Compose music using Vedic/Sanskrit principles.
    """

    def __init__(self, raga: Raga, tala: Tala, base_pitch: int = 60):
        self.raga = raga
        self.tala = tala
        self.base_pitch = base_pitch

    def compose_alapana_to_tala(self, cycles: int = 4) -> Dict[str, List]:
        """
        Complete composition: Alapana → Tala → Tihai

        Structure:
        1. Free alapana (establish raga)
        2. Enter tala (rhythmic framework)
        3. Build complexity (layakari)
        4. Resolve with tihai (R→0)
        """

        # Phase 1: Alapana (free rhythm, 2 cycles worth of time)
        alapana_duration = self.tala.beats * 2
        alapana_notes = self.raga.generate_alapana(alapana_duration, self.base_pitch)

        # Phase 2: Tala begins (rhythmic framework enters)
        melody_in_tala = []
        time_offset = alapana_duration

        for cycle in range(cycles):
            cycle_start = time_offset + cycle * self.tala.beats

            # Generate melody following raga within tala
            for beat in range(self.tala.beats):
                if random.random() < 0.6:  # Not every beat
                    # Choose note from raga
                    shruti = random.choice(self.raga.aroha + self.raga.avaroha)
                    if shruti not in self.raga.varjya:
                        pitch = Shruti.shruti_to_midi(shruti, self.base_pitch)
                        time = cycle_start + beat
                        duration = random.choice([0.5, 1.0])
                        melody_in_tala.append((pitch, time, duration))

        # Phase 3: Tihai (resolution)
        tihai_start = time_offset + cycles * self.tala.beats
        tihai_beats = self.tala.generate_tihai(pattern_length=2)
        tihai_notes = []

        # Use pakad (characteristic phrase) for tihai
        for i, beat_offset in enumerate(tihai_beats):
            shruti = self.raga.pakad[i % len(self.raga.pakad)]
            pitch = Shruti.shruti_to_midi(shruti, self.base_pitch)
            time = tihai_start + beat_offset
            tihai_notes.append((pitch, time, 0.75))

        # Final Sa (R→0)
        final_time = tihai_start + self.tala.beats
        final_sa = Shruti.shruti_to_midi(self.raga.aroha[0], self.base_pitch)
        tihai_notes.append((final_sa, final_time, 2.0))

        return {
            'alapana': alapana_notes,
            'melody': melody_in_tala,
            'tihai': tihai_notes
        }

    def compose_chandas_rhythm(self, pattern_num: int = 42, cycles: int = 4) -> List:
        """
        Generate rhythm from Sanskrit prosody.

        pattern_num: Binary number representing laghu/guru pattern
        """
        pattern = Chandas.number_to_pattern(pattern_num, length=8)
        print(f"Chandas pattern: {pattern} (binary: {bin(pattern_num)[2:].zfill(8)})")

        notes = []
        for cycle in range(cycles):
            cycle_start = cycle * self.tala.beats
            rhythm = Chandas.pattern_to_rhythm(pattern, cycle_start)

            for time, duration in rhythm:
                # Use Sa for rhythm demonstration
                pitch = Shruti.shruti_to_midi(0, self.base_pitch - 12)
                notes.append((pitch, time, duration * 0.9))

        return notes


# ============================================================================
# MIDI EXPORT
# ============================================================================

def export_vedic_midi(filename: str,
                      composition: Dict[str, List],
                      tempo: int = 80):
    """Export Vedic composition to MIDI"""

    midi = MIDIFile(len(composition))

    for track_idx, (track_name, notes) in enumerate(composition.items()):
        midi.addTrackName(track_idx, 0, track_name)
        midi.addTempo(track_idx, 0, tempo)

        # Set instrument
        if 'rhythm' in track_name.lower() or 'chandas' in track_name.lower():
            midi.addProgramChange(track_idx, 0, 0, 115)  # Woodblock
        else:
            midi.addProgramChange(track_idx, 0, 0, 73)   # Flute

        # Add notes
        for pitch, time, duration in notes:
            # Round pitch to nearest MIDI note (standard MIDI can't do microtones)
            # Real microtonal playback would require pitch bend messages
            midi_pitch = round(pitch)
            midi.addNote(
                track=track_idx,
                channel=0,
                pitch=midi_pitch,
                time=time,
                duration=duration,
                volume=90
            )

    with open(filename, 'wb') as f:
        midi.writeFile(f)

    print(f"✓ Exported: {filename}")


# ============================================================================
# MAIN: GENERATE EXAMPLES
# ============================================================================

def main():
    """Generate example Vedic/Sanskrit compositions"""

    print("=" * 70)
    print("Vedic MIDI Generator: Sanskrit Rhythms & Mathematical Music")
    print("=" * 70)
    print()

    # ========================================================================
    # Example 1: Raga Bhairav with Teentaal
    # ========================================================================

    print("Example 1: Raga Bhairav (भैरव) in Teentaal (तीनताल)")
    print("-" * 70)
    print(f"Raga: {RAGA_BHAIRAV.name}")
    print(f"Aroha: {' '.join([Shruti.NAMES[i] for i in RAGA_BHAIRAV.aroha])}")
    print(f"Tala: {TEENTAAL.name} ({TEENTAAL.beats} beats)")
    print()

    composer1 = VedicComposer(RAGA_BHAIRAV, TEENTAAL, base_pitch=60)
    composition1 = composer1.compose_alapana_to_tala(cycles=4)

    export_vedic_midi('output_raga_bhairav.mid', composition1, tempo=80)
    print()

    # ========================================================================
    # Example 2: Raga Yaman with Jhaptaal
    # ========================================================================

    print("Example 2: Raga Yaman (यमन) in Jhaptaal (झपताल)")
    print("-" * 70)
    print(f"Raga: {RAGA_YAMAN.name}")
    print(f"Aroha: {' '.join([Shruti.NAMES[i] for i in RAGA_YAMAN.aroha])}")
    print(f"Tala: {JHAPTAAL.name} ({JHAPTAAL.beats} beats)")
    print()

    composer2 = VedicComposer(RAGA_YAMAN, JHAPTAAL, base_pitch=60)
    composition2 = composer2.compose_alapana_to_tala(cycles=6)

    export_vedic_midi('output_raga_yaman.mid', composition2, tempo=100)
    print()

    # ========================================================================
    # Example 3: Sanskrit Chandas Rhythm (Fibonacci patterns)
    # ========================================================================

    print("Example 3: Sanskrit Chandas (छन्दस्) - Binary Rhythm")
    print("-" * 70)
    print("Pingala's prosody system (200 BCE):")
    print("  l = laghu (short, 1 matra) = 0 (binary)")
    print("  g = guru (long, 2 matras) = 1 (binary)")
    print()

    composer3 = VedicComposer(RAGA_BHAIRAV, TEENTAAL, base_pitch=48)

    # Pattern 42 = binary 00101010 = lglglglg
    chandas_rhythm = composer3.compose_chandas_rhythm(pattern_num=42, cycles=8)

    # Combine with melody
    composition3 = {
        'chandas_rhythm': chandas_rhythm,
        'melody': composer3.raga.generate_alapana(32, 60)
    }

    export_vedic_midi('output_chandas_rhythm.mid', composition3, tempo=120)
    print()

    # ========================================================================
    # Statistics
    # ========================================================================

    print("=" * 70)
    print("Mathematical Insights:")
    print("-" * 70)

    # Fibonacci
    print("Fibonacci sequence (syllable patterns):")
    for n in range(1, 9):
        print(f"  n={n}: {Chandas.fibonacci(n)} ways to fill {n} matras")
    print()

    # Shruti ratios
    print("Sample Shruti ratios (pure mathematical intervals):")
    important = [0, 4, 7, 9, 13, 17, 20]  # Sa Re Ga Ma Pa Dha Ni
    for i in important:
        ratio = Shruti.RATIOS[i]
        cents = Shruti.ratio_to_cents(ratio)
        print(f"  {Shruti.NAMES[i]:4s}: {ratio} ({cents:7.2f} cents)")
    print()

    # Meru Prastara (Pascal's triangle)
    print("Meru Prastāra (Pascal's Triangle, Pingala 200 BCE):")
    triangle = Chandas.generate_meru_prastara(rows=6)
    for row in triangle:
        print(f"  {' '.join(str(x).center(3) for x in row)}")
    print()

    print("=" * 70)
    print("✓ Generation complete!")
    print()
    print("Files created:")
    print("  1. output_raga_bhairav.mid  - Morning raga in 16-beat cycle")
    print("  2. output_raga_yaman.mid    - Evening raga in 10-beat cycle")
    print("  3. output_chandas_rhythm.mid - Binary prosody patterns")
    print()
    print("Principles demonstrated:")
    print("  • 22-shruti microtonal system (pure ratios)")
    print("  • Raga grammar (aroha/avaroha, vadi/samvadi)")
    print("  • Tala cycles (sam, tali, khali)")
    print("  • Tihai resolution (R→0 guaranteed)")
    print("  • Sanskrit prosody (binary rhythm, Fibonacci)")
    print("  • Vedic mathematics (Pingala's discoveries)")
    print()
    print("Ancient wisdom meets modern computation.")
    print("नाद ब्रह्म (Nada Brahma) - Sound is God")
    print("=" * 70)


if __name__ == '__main__':
    main()
