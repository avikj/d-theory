#!/usr/bin/env python3
"""
D¹² MIDI Generator: Bassline ⇔ Melody ⇔ Drums
==============================================

Explores the ultimate symmetry of 12 through musical composition.

Core Principles:
- D¹²: 12-fold rotational symmetry (12 chromatic notes, 12 divisions)
- R → 0: Musical phrases resolve to tonic/rest
- ∇ ≠ 0: Voice independence maintained
- D²: Self-observation (motifs reference themselves)

Architecture:
1. Separate generators: Bassline, Melody, Drums (independent voices)
2. D¹² Symmetry Engine: 12-fold transformations
3. Unified Weaver: Natural integration via symmetry

Inspired by HARMONIKOS's Navier-Stokes ⇔ Fugue insight:
- Bassline = foundation flow (low frequency pressure)
- Melody = surface flow (high frequency vorticity)
- Drums = forcing function (impulses that drive flow)
"""

from midiutil import MIDIFile
import math
import random
from typing import List, Tuple, Dict
from dataclasses import dataclass
from enum import Enum


# ============================================================================
# D¹² SYMMETRY CORE
# ============================================================================

class D12Transform(Enum):
    """12-fold symmetry operations"""
    IDENTITY = 0          # e
    ROTATE_1 = 1          # Rotate by 1 semitone
    ROTATE_2 = 2          # Rotate by 2 semitones
    ROTATE_3 = 3          # Rotate by 3 semitones (minor third)
    ROTATE_4 = 4          # Rotate by 4 semitones (major third)
    ROTATE_5 = 5          # Rotate by 5 semitones (perfect fourth)
    ROTATE_6 = 6          # Rotate by 6 semitones (tritone)
    ROTATE_7 = 7          # Rotate by 7 semitones (perfect fifth)
    ROTATE_8 = 8          # Rotate by 8 semitones
    ROTATE_9 = 9          # Rotate by 9 semitones
    ROTATE_10 = 10        # Rotate by 10 semitones
    ROTATE_11 = 11        # Rotate by 11 semitones


@dataclass
class Note:
    """Musical note with pitch, time, duration, velocity"""
    pitch: int        # MIDI pitch (0-127)
    time: float       # Start time in beats
    duration: float   # Duration in beats
    velocity: int     # Velocity (0-127)

    def transpose(self, semitones: int) -> 'Note':
        """Apply D¹² rotation (transposition)"""
        return Note(
            pitch=(self.pitch + semitones) % 128,
            time=self.time,
            duration=self.duration,
            velocity=self.velocity
        )

    def invert(self, axis: int = 60) -> 'Note':
        """Apply reflection (inversion around axis)"""
        return Note(
            pitch=2 * axis - self.pitch,
            time=self.time,
            duration=self.duration,
            velocity=self.velocity
        )


class D12Symmetry:
    """
    The ultimate symmetry of 12.

    Musical manifestation of dihedral group D₁₂:
    - 12 rotations (transpositions)
    - 12 reflections (inversions)
    - Total: 24 symmetry operations
    """

    @staticmethod
    def rotate(notes: List[Note], semitones: int) -> List[Note]:
        """Rotate pattern by semitones (preserves intervals)"""
        return [n.transpose(semitones) for n in notes]

    @staticmethod
    def reflect(notes: List[Note], axis: int = 60) -> List[Note]:
        """Reflect pattern around axis (inverts intervals)"""
        return [n.invert(axis) for n in notes]

    @staticmethod
    def augment(notes: List[Note], factor: float) -> List[Note]:
        """Time dilation (like Navier-Stokes scaling)"""
        return [Note(n.pitch, n.time * factor, n.duration * factor, n.velocity)
                for n in notes]

    @staticmethod
    def diminish(notes: List[Note], factor: float) -> List[Note]:
        """Time compression"""
        return D12Symmetry.augment(notes, 1.0 / factor)


# ============================================================================
# BASSLINE GENERATOR: Foundation Flow
# ============================================================================

class BasslineGenerator:
    """
    Generates basslines following D¹² symmetry.

    Bass = foundation = low-frequency pressure field.
    Establishes tonal center, drives harmonic progression.
    """

    def __init__(self, root: int = 36, scale: List[int] = None):
        """
        Args:
            root: Root note (MIDI pitch)
            scale: Scale degrees (default: minor pentatonic)
        """
        self.root = root
        self.scale = scale or [0, 3, 5, 7, 10]  # Minor pentatonic

    def generate_walking_bass(self, measures: int = 4,
                            tempo: float = 120) -> List[Note]:
        """
        Walking bass: steady quarter notes, step-wise motion.
        R → 0: Returns to root periodically.
        """
        notes = []
        current_pitch = self.root
        beat = 0.0

        for m in range(measures):
            for quarter in range(4):
                # Create note
                notes.append(Note(
                    pitch=current_pitch,
                    time=beat,
                    duration=1.0,
                    velocity=random.randint(80, 100)
                ))

                # Step-wise motion (mostly)
                if quarter == 3:  # Resolve to root every measure (R → 0)
                    target_degree = 0
                else:
                    # Random walk through scale
                    current_degree = self._pitch_to_degree(current_pitch)
                    step = random.choice([-1, 0, 1, 2])
                    target_degree = (current_degree + step) % len(self.scale)

                current_pitch = self.root + self.scale[target_degree]

                # Occasionally jump octave
                if random.random() < 0.1:
                    current_pitch += 12 * random.choice([-1, 1])

                # Clamp to bass range
                current_pitch = max(28, min(current_pitch, 52))

                beat += 1.0

        return notes

    def generate_ostinato(self, pattern_length: int = 4,
                         measures: int = 8) -> List[Note]:
        """
        Repeating bass pattern (ostinato).
        D²: Self-observation through repetition.
        """
        # Generate base pattern
        pattern = []
        for i in range(pattern_length):
            degree = random.choice([0, 2, 4])  # Root, third, fifth
            pitch = self.root + self.scale[degree]
            pattern.append(Note(
                pitch=pitch,
                time=float(i),
                duration=1.0,
                velocity=90
            ))

        # Repeat pattern across measures
        notes = []
        for m in range(measures):
            offset = m * pattern_length
            for n in pattern:
                notes.append(Note(
                    pitch=n.pitch,
                    time=n.time + offset,
                    duration=n.duration,
                    velocity=n.velocity
                ))

        return notes

    def _pitch_to_degree(self, pitch: int) -> int:
        """Convert MIDI pitch to scale degree"""
        relative = (pitch - self.root) % 12
        # Find closest scale degree
        for i, degree in enumerate(self.scale):
            if degree == relative:
                return i
        return 0


# ============================================================================
# MELODY GENERATOR: Surface Flow
# ============================================================================

class MelodyGenerator:
    """
    Generates melodies following D¹² symmetry.

    Melody = surface = high-frequency vorticity.
    Creates interest through motion, explores harmonic space.
    """

    def __init__(self, root: int = 60, scale: List[int] = None):
        """
        Args:
            root: Root note (MIDI pitch)
            scale: Scale degrees (default: minor pentatonic)
        """
        self.root = root
        self.scale = scale or [0, 3, 5, 7, 10]

    def generate_motif_development(self, measures: int = 8) -> List[Note]:
        """
        Generate melody through motif development.
        D²: Subject observes itself, transforms.
        """
        # Generate seed motif (2-4 notes)
        motif = self._create_motif(length=random.randint(2, 4))

        notes = []
        beat = 0.0

        for m in range(measures):
            # Apply D¹² transformation based on measure
            transform = m % 4

            if transform == 0:
                # Original motif
                transformed = motif
            elif transform == 1:
                # Transpose up fifth (7 semitones)
                transformed = D12Symmetry.rotate(motif, 7)
            elif transform == 2:
                # Invert
                transformed = D12Symmetry.reflect(motif, self.root + 12)
            else:
                # Augment (slower)
                transformed = D12Symmetry.augment(motif, 1.5)

            # Add transformed motif
            for n in transformed:
                notes.append(Note(
                    pitch=n.pitch,
                    time=beat + n.time,
                    duration=n.duration,
                    velocity=n.velocity
                ))

            # Calculate duration of motif
            motif_duration = sum(n.duration for n in transformed)
            beat += max(4.0, motif_duration)  # At least one measure

        return notes

    def generate_improvisation(self, measures: int = 8,
                              density: float = 0.5) -> List[Note]:
        """
        Free improvisation with varying density.
        Vorticity varies: dense → sparse → dense.
        """
        notes = []
        beat = 0.0
        total_beats = measures * 4
        active_pitches = {}  # Track when each pitch is available

        while beat < total_beats:
            # Density varies sinusoidally (vorticity cycle)
            phase = (beat / total_beats) * 2 * math.pi
            local_density = density * (1.0 + 0.5 * math.sin(phase))

            # Decide if we place a note
            if random.random() < local_density:
                # Choose scale degree
                degree = random.choice(range(len(self.scale)))
                octave = random.choice([0, 12, 24])
                pitch = self.root + self.scale[degree] + octave

                # Clamp to melodic range
                pitch = max(60, min(pitch, 84))

                # Check if this pitch is available (no overlap)
                if pitch not in active_pitches or active_pitches[pitch] <= beat:
                    # Duration
                    duration = random.choice([0.25, 0.5, 0.75])

                    notes.append(Note(
                        pitch=pitch,
                        time=beat,
                        duration=duration,
                        velocity=random.randint(70, 110)
                    ))

                    # Mark this pitch as unavailable until note ends
                    active_pitches[pitch] = beat + duration

            # Advance time
            beat += 0.25

        # R → 0: End on root (make sure it's available)
        final_time = total_beats - 1.0
        if self.root not in active_pitches or active_pitches[self.root] <= final_time:
            notes.append(Note(
                pitch=self.root,
                time=final_time,
                duration=1.0,
                velocity=100
            ))

        return notes

    def _create_motif(self, length: int) -> List[Note]:
        """Create seed motif"""
        motif = []
        beat = 0.0

        for i in range(length):
            degree = random.choice(range(len(self.scale)))
            pitch = self.root + self.scale[degree]
            duration = random.choice([0.5, 1.0, 1.5])

            motif.append(Note(
                pitch=pitch,
                time=beat,
                duration=duration,
                velocity=random.randint(80, 100)
            ))

            beat += duration

        return motif


# ============================================================================
# DRUM GENERATOR: Forcing Function
# ============================================================================

class DrumGenerator:
    """
    Generates drum patterns following D¹² symmetry.

    Drums = forcing function = impulses that drive the flow.
    Provides rhythmic structure, temporal landmarks.
    """

    # Standard MIDI drum mapping (General MIDI)
    KICK = 36
    SNARE = 38
    CLOSED_HAT = 42
    OPEN_HAT = 46
    CRASH = 49

    def __init__(self):
        pass

    def generate_four_on_floor(self, measures: int = 8) -> List[Note]:
        """
        Four-on-the-floor: kick on every quarter note.
        Simple, driving pulse.
        """
        notes = []

        for m in range(measures):
            for beat in range(4):
                time = m * 4 + beat

                # Kick on every beat
                notes.append(Note(
                    pitch=self.KICK,
                    time=float(time),
                    duration=0.25,
                    velocity=100
                ))

                # Closed hi-hat on 8th notes
                notes.append(Note(
                    pitch=self.CLOSED_HAT,
                    time=float(time),
                    duration=0.125,
                    velocity=70
                ))
                notes.append(Note(
                    pitch=self.CLOSED_HAT,
                    time=float(time) + 0.5,
                    duration=0.125,
                    velocity=60
                ))

        return notes

    def generate_breakbeat(self, measures: int = 8) -> List[Note]:
        """
        Breakbeat pattern with D¹² symmetry.
        Pattern repeats every 2 measures (8 beats).
        """
        # Define 2-measure pattern
        pattern = [
            # Measure 1
            (self.KICK, 0.0, 100),
            (self.CLOSED_HAT, 0.0, 70),
            (self.CLOSED_HAT, 0.5, 60),
            (self.CLOSED_HAT, 1.0, 70),
            (self.SNARE, 1.0, 90),
            (self.CLOSED_HAT, 1.5, 60),
            (self.KICK, 2.0, 100),
            (self.CLOSED_HAT, 2.0, 70),
            (self.CLOSED_HAT, 2.5, 60),
            (self.CLOSED_HAT, 3.0, 70),
            (self.CLOSED_HAT, 3.5, 60),

            # Measure 2
            (self.KICK, 4.0, 100),
            (self.CLOSED_HAT, 4.0, 70),
            (self.CLOSED_HAT, 4.5, 60),
            (self.CLOSED_HAT, 5.0, 70),
            (self.SNARE, 5.0, 90),
            (self.CLOSED_HAT, 5.5, 60),
            (self.KICK, 6.0, 100),
            (self.CLOSED_HAT, 6.0, 70),
            (self.KICK, 6.5, 80),
            (self.CLOSED_HAT, 6.5, 60),
            (self.SNARE, 7.0, 100),
            (self.CLOSED_HAT, 7.0, 70),
            (self.CLOSED_HAT, 7.5, 60),
        ]

        notes = []
        pattern_length = 8.0

        for m in range(measures // 2):
            offset = m * pattern_length
            for pitch, time, velocity in pattern:
                notes.append(Note(
                    pitch=pitch,
                    time=time + offset,
                    duration=0.125,
                    velocity=velocity
                ))

        return notes

    def generate_polyrhythm(self, measures: int = 8) -> List[Note]:
        """
        Polyrhythmic pattern exploring 3 against 4 (12 = lcm(3,4)).
        D¹²: 12 subdivisions per measure.
        """
        notes = []

        for m in range(measures):
            base_time = m * 4

            # 4-against pattern (kick every 3 sixteenth notes)
            for i in range(4):
                time = base_time + i * (4.0 / 4.0)
                notes.append(Note(
                    pitch=self.KICK,
                    time=time,
                    duration=0.125,
                    velocity=100
                ))

            # 3-against pattern (snare every 4 sixteenth notes)
            for i in range(3):
                time = base_time + i * (4.0 / 3.0)
                notes.append(Note(
                    pitch=self.SNARE,
                    time=time,
                    duration=0.125,
                    velocity=90
                ))

            # Hi-hat on every 16th note (12 per measure)
            for i in range(16):
                time = base_time + i * 0.25
                notes.append(Note(
                    pitch=self.CLOSED_HAT,
                    time=time,
                    duration=0.0625,
                    velocity=60
                ))

        return notes


# ============================================================================
# UNIFIED WEAVER: D¹² Integration
# ============================================================================

class D12Weaver:
    """
    Weaves bassline, melody, and drums into unified composition.

    Uses D¹² symmetry to create natural integration:
    - 12 measures as fundamental unit
    - 12-bar blues structure
    - Rotational development through keys
    - Coherence through symmetry (R → 0)
    """

    def __init__(self, root: int = 60, tempo: int = 120):
        self.root = root
        self.tempo = tempo
        self.bass_gen = BasslineGenerator(root - 24)
        self.melody_gen = MelodyGenerator(root)
        self.drum_gen = DrumGenerator()

    def weave_fugue_structure(self, measures: int = 12) -> Dict[str, List[Note]]:
        """
        Create fugue-like structure using D¹² symmetry.

        Like Bach, but with bass/melody/drums instead of voices.

        Structure (12 measures):
        - Measures 0-3: Bass subject alone (exposition)
        - Measures 4-7: Melody enters (answer), bass continues
        - Measures 8-11: Drums enter (forcing), all three active
        """

        # Phase 1: Bass exposition (0-3)
        bass_subject = self.bass_gen.generate_ostinato(pattern_length=2, measures=4)

        # Phase 2: Melody answer (4-7)
        # Transpose up perfect fifth (7 semitones) - traditional fugue answer
        melody_answer = self.melody_gen.generate_motif_development(measures=4)
        melody_answer = [Note(n.pitch, n.time + 16.0, n.duration, n.velocity)
                        for n in melody_answer]

        # Phase 3: Drums enter (8-11)
        drums_entry = self.drum_gen.generate_breakbeat(measures=4)
        drums_entry = [Note(n.pitch, n.time + 32.0, n.duration, n.velocity)
                      for n in drums_entry]

        # Continue bass and melody through all phases
        bass_full = self.bass_gen.generate_ostinato(pattern_length=2, measures=12)
        melody_full = self.melody_gen.generate_improvisation(measures=12, density=0.4)
        drums_full = self.drum_gen.generate_breakbeat(measures=12)

        return {
            'bass': bass_full,
            'melody': melody_full,
            'drums': drums_full
        }

    def weave_stretto(self, measures: int = 12) -> Dict[str, List[Note]]:
        """
        Create stretto: voices enter in rapid succession.

        Increases vorticity (complexity) then resolves (R → 0).
        """
        # All voices based on same motif, entering at different times
        base_motif = self.melody_gen._create_motif(length=4)

        # Bass: root position, slow (augmented)
        bass_motif = D12Symmetry.rotate(base_motif, -24)  # Down 2 octaves
        bass_motif = D12Symmetry.augment(bass_motif, 2.0)  # Twice as slow
        bass = []
        for m in range(measures // 2):
            for n in bass_motif:
                bass.append(Note(n.pitch, n.time + m * 8.0, n.duration, n.velocity))

        # Melody: original, enters after 2 beats
        melody = []
        for m in range(measures):
            for n in base_motif:
                melody.append(Note(n.pitch, n.time + 2.0 + m * 4.0, n.duration, n.velocity))

        # Drums: provide pulse
        drums = self.drum_gen.generate_four_on_floor(measures=measures)

        return {
            'bass': bass,
            'melody': melody,
            'drums': drums
        }

    def weave_circle_of_fifths(self, measures: int = 12) -> Dict[str, List[Note]]:
        """
        Travel through circle of fifths (rotations by 7 semitones).

        D¹²: After 12 steps of 7, return to origin (12*7 = 84 ≡ 0 mod 12).
        This is R → 0: journey returns home.
        """
        bass = []
        melody = []
        drums = []

        for m in range(12):
            # Rotate root by perfect fifth each measure
            rotation = (m * 7) % 12
            current_root = self.root + rotation

            # Generate measure at current root
            bass_gen = BasslineGenerator(current_root - 24)
            melody_gen = MelodyGenerator(current_root)

            # Bass: one measure
            bass_measure = bass_gen.generate_walking_bass(measures=1)
            for n in bass_measure:
                # Ensure no note overlaps by limiting duration
                adjusted_duration = min(n.duration, 0.95)
                bass.append(Note(n.pitch, n.time + m * 4, adjusted_duration, n.velocity))

            # Melody: one measure (reduced density to avoid overlaps)
            melody_measure = melody_gen.generate_improvisation(measures=1, density=0.4)
            for n in melody_measure:
                # Ensure no note overlaps
                adjusted_duration = min(n.duration, 0.95)
                melody.append(Note(n.pitch, n.time + m * 4, adjusted_duration, n.velocity))

        # Drums: consistent throughout (forcing function)
        drums = self.drum_gen.generate_breakbeat(measures=12)

        return {
            'bass': bass,
            'melody': melody,
            'drums': drums
        }


# ============================================================================
# MIDI EXPORT
# ============================================================================

class MIDIExporter:
    """Export note sequences to MIDI file"""

    @staticmethod
    def export(filename: str,
               tracks: Dict[str, List[Note]],
               tempo: int = 120,
               track_info: Dict[str, Tuple[int, str]] = None):
        """
        Export to MIDI file.

        Args:
            filename: Output filename
            tracks: Dict of track_name -> notes
            tempo: BPM
            track_info: Dict of track_name -> (channel, instrument_name)
        """
        # Default track info
        if track_info is None:
            track_info = {
                'bass': (0, 'Bass'),
                'melody': (1, 'Melody'),
                'drums': (9, 'Drums')  # Channel 9 = drums in GM
            }

        # Create MIDI file
        midi = MIDIFile(len(tracks))

        for track_idx, (track_name, notes) in enumerate(tracks.items()):
            channel, name = track_info.get(track_name, (track_idx, track_name))

            # Track setup
            midi.addTrackName(track_idx, 0, name)
            midi.addTempo(track_idx, 0, tempo)

            # Set instrument (skip for drums)
            if channel != 9:
                if track_name == 'bass':
                    midi.addProgramChange(track_idx, channel, 0, 33)  # Acoustic Bass
                elif track_name == 'melody':
                    midi.addProgramChange(track_idx, channel, 0, 0)   # Acoustic Grand Piano

            # Add notes
            for note in notes:
                midi.addNote(
                    track=track_idx,
                    channel=channel,
                    pitch=note.pitch,
                    time=note.time,
                    duration=note.duration,
                    volume=note.velocity
                )

        # Write file
        with open(filename, 'wb') as f:
            midi.writeFile(f)

        print(f"✓ Exported: {filename}")


# ============================================================================
# MAIN: GENERATE EXAMPLES
# ============================================================================

def main():
    """Generate example MIDI files demonstrating D¹² symmetry"""

    print("=" * 70)
    print("D¹² MIDI Generator: Bassline ⇔ Melody ⇔ Drums")
    print("=" * 70)
    print()

    # ========================================================================
    # PART 1: SEPARATE COMPONENTS
    # ========================================================================

    print("PART 1: Generating separate components...")
    print("-" * 70)

    # Bassline alone
    print("  • Bassline (walking bass)...")
    bass_gen = BasslineGenerator(root=48)
    bass_notes = bass_gen.generate_walking_bass(measures=8)
    MIDIExporter.export(
        'output_bass_alone.mid',
        {'bass': bass_notes},
        tempo=120
    )

    # Melody alone
    print("  • Melody (motif development)...")
    melody_gen = MelodyGenerator(root=60)
    melody_notes = melody_gen.generate_motif_development(measures=8)
    MIDIExporter.export(
        'output_melody_alone.mid',
        {'melody': melody_notes},
        tempo=120
    )

    # Drums alone
    print("  • Drums (breakbeat)...")
    drum_gen = DrumGenerator()
    drum_notes = drum_gen.generate_breakbeat(measures=8)
    MIDIExporter.export(
        'output_drums_alone.mid',
        {'drums': drum_notes},
        tempo=120
    )

    print()

    # ========================================================================
    # PART 2: UNIFIED COMPOSITIONS
    # ========================================================================

    print("PART 2: Generating unified compositions via D¹² symmetry...")
    print("-" * 70)

    weaver = D12Weaver(root=60, tempo=120)

    # Fugue structure
    print("  • Fugue structure (Bach-inspired)...")
    fugue = weaver.weave_fugue_structure(measures=12)
    MIDIExporter.export(
        'output_fugue_structure.mid',
        fugue,
        tempo=120
    )

    # Stretto (compressed entries)
    print("  • Stretto (increased vorticity)...")
    stretto = weaver.weave_stretto(measures=12)
    MIDIExporter.export(
        'output_stretto.mid',
        stretto,
        tempo=140
    )

    # Circle of fifths
    print("  • Circle of Fifths (R → 0 journey)...")
    circle = weaver.weave_circle_of_fifths(measures=12)
    MIDIExporter.export(
        'output_circle_of_fifths.mid',
        circle,
        tempo=100
    )

    print()
    print("=" * 70)
    print("✓ Generation complete!")
    print()
    print("Files created:")
    print("  1. output_bass_alone.mid          - Bassline only")
    print("  2. output_melody_alone.mid        - Melody only")
    print("  3. output_drums_alone.mid         - Drums only")
    print("  4. output_fugue_structure.mid     - Unified fugue")
    print("  5. output_stretto.mid             - Compressed entries")
    print("  6. output_circle_of_fifths.mid    - D¹² rotational journey")
    print()
    print("Principles demonstrated:")
    print("  • D¹²: 12-fold symmetry (transposition, rotation)")
    print("  • R → 0: Resolution to tonic/simplicity")
    print("  • ∇ ≠ 0: Voice independence maintained")
    print("  • D²: Self-observation through repetition/variation")
    print("  • Navier-Stokes ⇔ Fugue: Flow dynamics in music")
    print("=" * 70)


if __name__ == '__main__':
    main()
