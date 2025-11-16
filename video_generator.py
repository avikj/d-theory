#!/usr/bin/env python3
"""
Video Generator for Distinction Theory Concepts
===============================================

Creates animated visualizations of:
1. D¹² symmetry in music
2. Vedic mathematics (binary, Fibonacci, Pascal)
3. Suchir's entropy analysis
4. D-Coherence principles (R→0, ∇≠0, D²)

Uses matplotlib for animations (can export to MP4).
Can integrate with manim for more sophisticated animations.
"""

import matplotlib.pyplot as plt
import matplotlib.animation as animation
from matplotlib.patches import Circle, FancyArrowPatch, Rectangle, Wedge
import numpy as np
from typing import List, Tuple, Callable
import os


# ============================================================================
# VIDEO 1: D¹² Circle of Fifths Animation
# ============================================================================

def create_circle_of_fifths_video(output_file='d12_circle_of_fifths.mp4',
                                  duration_seconds=10,
                                  fps=30):
    """
    Animate journey through circle of fifths.
    Shows 12 rotations by 7 semitones returning to origin (R→0).
    """

    fig, ax = plt.subplots(figsize=(10, 10))
    ax.set_xlim(-2, 2)
    ax.set_ylim(-2, 2)
    ax.set_aspect('equal')
    ax.axis('off')

    # Note names in circle of fifths order
    notes = ['C', 'G', 'D', 'A', 'E', 'B', 'F#', 'C#', 'G#', 'D#', 'A#', 'F']

    # Draw circle
    circle = Circle((0, 0), 1.5, fill=False, edgecolor='black', linewidth=2)
    ax.add_patch(circle)

    # Place note circles
    note_positions = []
    note_circles = []
    for i, note in enumerate(notes):
        angle = 2 * np.pi * i / 12 - np.pi/2
        x = 1.5 * np.cos(angle)
        y = 1.5 * np.sin(angle)
        note_positions.append((x, y, note))

        c = Circle((x, y), 0.15, facecolor='lightblue',
                   edgecolor='darkblue', linewidth=2, zorder=2)
        note_circles.append(c)
        ax.add_patch(c)
        ax.text(x, y, note, ha='center', va='center',
                fontsize=12, fontweight='bold', zorder=3)

    # Highlighter (moves around circle)
    highlighter = Circle((0, 0), 0.2, facecolor='red', alpha=0.5, zorder=4)
    ax.add_patch(highlighter)

    # Title and text
    title = ax.text(0, 1.9, 'D¹² Circle of Fifths: Journey Returns to Origin',
                    ha='center', fontsize=14, fontweight='bold')
    counter = ax.text(0, -1.9, '', ha='center', fontsize=12)

    def animate(frame):
        # Total frames
        total_frames = duration_seconds * fps

        # Current step (0-12)
        step = int((frame / total_frames) * 13)
        if step > 12:
            step = 12

        # Current position in circle
        step_mod = step % 12
        angle = 2 * np.pi * step_mod / 12 - np.pi/2
        x = 1.5 * np.cos(angle)
        y = 1.5 * np.sin(angle)

        # Update highlighter
        highlighter.center = (x, y)

        # Update note colors
        for i, c in enumerate(note_circles):
            if i == step_mod:
                c.set_facecolor('yellow')
                c.set_linewidth(3)
            else:
                c.set_facecolor('lightblue')
                c.set_linewidth(2)

        # Update counter
        semitones = step * 7
        current_note = notes[step_mod]
        counter.set_text(f'Step {step}/12 | Semitones: {semitones} | Note: {current_note}')

        # Highlight when we return to origin
        if step == 12:
            counter.set_text('R → 0: Returned to Origin! (12×7 = 84 ≡ 0 mod 12)')
            counter.set_color('red')
            counter.set_fontweight('bold')

        return [highlighter, counter] + note_circles

    anim = animation.FuncAnimation(fig, animate, frames=duration_seconds*fps,
                                   interval=1000/fps, blit=False)

    # Save
    Writer = animation.writers['ffmpeg']
    writer = Writer(fps=fps, metadata=dict(artist='Distinction Theory'),
                    bitrate=1800)
    anim.save(output_file, writer=writer)
    plt.close()

    print(f"✓ Created: {output_file}")


# ============================================================================
# VIDEO 2: Pingala's Binary System Animation
# ============================================================================

def create_pingala_binary_video(output_file='pingala_binary.mp4',
                                duration_seconds=15,
                                fps=30):
    """
    Animate Pingala's discovery of binary (200 BCE).
    Shows laghu/guru → 0/1 mapping and counting.
    """

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 8))

    # Left: Sanskrit syllables
    ax1.set_xlim(0, 10)
    ax1.set_ylim(0, 10)
    ax1.axis('off')
    ax1.set_title('Sanskrit Prosody (Chandas)', fontsize=14, fontweight='bold')

    # Right: Binary representation
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 10)
    ax2.axis('off')
    ax2.set_title('Binary System', fontsize=14, fontweight='bold')

    # Timeline text
    timeline = fig.text(0.5, 0.95, '', ha='center', fontsize=12, fontweight='bold')

    def draw_syllables(ax, pattern, y_pos):
        """Draw laghu (ल) and guru (ग) syllables"""
        x_start = 2
        for i, syl in enumerate(pattern):
            if syl == 'l':
                # Laghu (short) - small circle
                c = Circle((x_start + i*0.8, y_pos), 0.15,
                          facecolor='lightgreen', edgecolor='darkgreen', linewidth=2)
                ax.add_patch(c)
                ax.text(x_start + i*0.8, y_pos, 'ल', ha='center', va='center',
                       fontsize=10)
            else:  # g
                # Guru (long) - large circle
                c = Circle((x_start + i*0.8, y_pos), 0.25,
                          facecolor='lightcoral', edgecolor='darkred', linewidth=2)
                ax.add_patch(c)
                ax.text(x_start + i*0.8, y_pos, 'ग', ha='center', va='center',
                       fontsize=12, fontweight='bold')

    def draw_binary(ax, pattern, y_pos):
        """Draw binary representation"""
        x_start = 2
        for i, bit in enumerate(pattern):
            color = 'lightgreen' if bit == '0' else 'lightcoral'
            edge = 'darkgreen' if bit == '0' else 'darkred'
            r = Circle((x_start + i*0.8, y_pos), 0.2,
                      facecolor=color, edgecolor=edge, linewidth=2)
            ax.add_patch(r)
            ax.text(x_start + i*0.8, y_pos, bit, ha='center', va='center',
                   fontsize=14, fontweight='bold')

    # Example patterns (increasing binary numbers)
    examples = [
        ('llll', '0000', 0),
        ('lllg', '0001', 1),
        ('llgl', '0010', 2),
        ('llgg', '0011', 3),
        ('lgll', '0100', 4),
        ('lglg', '0101', 5),
        ('lggl', '0110', 6),
        ('lggg', '0111', 7),
    ]

    def animate(frame):
        total_frames = duration_seconds * fps

        # Clear axes
        ax1.clear()
        ax2.clear()
        ax1.set_xlim(0, 10)
        ax1.set_ylim(0, 10)
        ax1.axis('off')
        ax1.set_title('Sanskrit Prosody (Chandas)\nPingala, 200 BCE',
                     fontsize=12, fontweight='bold')
        ax2.set_xlim(0, 10)
        ax2.set_ylim(0, 10)
        ax2.axis('off')
        ax2.set_title('Binary System\nLeibniz, 1679 CE',
                     fontsize=12, fontweight='bold')

        # Current example
        idx = int((frame / total_frames) * len(examples))
        if idx >= len(examples):
            idx = len(examples) - 1

        syllables, binary, decimal = examples[idx]

        # Draw current pattern
        y_pos = 5
        draw_syllables(ax1, syllables, y_pos)
        draw_binary(ax2, binary, y_pos)

        # Labels
        ax1.text(5, 3, f'Pattern: {syllables}', ha='center', fontsize=11)
        ax1.text(5, 2.5, 'ल = laghu (light, 1 mātrā)', ha='center', fontsize=9, style='italic')
        ax1.text(5, 2, 'ग = guru (heavy, 2 mātrā)', ha='center', fontsize=9, style='italic')

        ax2.text(5, 3, f'Binary: {binary}', ha='center', fontsize=11)
        ax2.text(5, 2.5, f'Decimal: {decimal}', ha='center', fontsize=11, fontweight='bold')
        ax2.text(5, 2, '0 = laghu | 1 = guru', ha='center', fontsize=9, style='italic')

        # Timeline
        timeline.set_text(f'Pingala (200 BCE) discovered binary 1879 years before Leibniz (1679 CE)')

        return []

    anim = animation.FuncAnimation(fig, animate, frames=duration_seconds*fps,
                                   interval=1000/fps, blit=False)

    Writer = animation.writers['ffmpeg']
    writer = Writer(fps=fps, metadata=dict(artist='Distinction Theory'),
                    bitrate=1800)
    anim.save(output_file, writer=writer)
    plt.close()

    print(f"✓ Created: {output_file}")


# ============================================================================
# VIDEO 3: Suchir's Entropy Analysis
# ============================================================================

def create_suchir_entropy_video(output_file='suchir_entropy.mp4',
                                duration_seconds=20,
                                fps=30):
    """
    Visualize Suchir Balaji's entropy argument.
    Shows low entropy → high copying.
    """

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))

    # Top: Entropy over time
    ax1.set_xlim(0, 10)
    ax1.set_ylim(0, 5)
    ax1.set_xlabel('Training Iterations', fontsize=12)
    ax1.set_ylabel('Entropy (bits)', fontsize=12)
    ax1.set_title("Suchir's Analysis: RLHF Reduces Entropy → Increases Copying",
                 fontsize=14, fontweight='bold')
    ax1.grid(True, alpha=0.3)

    # Bottom: RMI calculation
    ax2.set_xlim(0, 10)
    ax2.set_ylim(0, 1)
    ax2.set_xlabel('Training Iterations', fontsize=12)
    ax2.set_ylabel('RMI (Relative Mutual Information)', fontsize=12)
    ax2.set_title('Fraction of Output from Training Data', fontsize=12, fontweight='bold')
    ax2.grid(True, alpha=0.3)

    # Add threshold lines
    ax2.axhline(y=0.7, color='orange', linestyle='--', linewidth=2,
                label='70% threshold')
    ax2.axhline(y=0.94, color='red', linestyle='--', linewidth=2,
                label='94% (ChatGPT measured)')

    def animate(frame):
        total_frames = duration_seconds * fps
        progress = frame / total_frames

        # Generate data
        iterations = np.linspace(0, 10, 100)

        # Entropy decreases with training (RLHF effect)
        initial_entropy = 4.0  # High randomness
        final_entropy = 0.2    # Low randomness (near-deterministic)
        entropy = initial_entropy - (initial_entropy - final_entropy) * (1 - np.exp(-iterations/3))

        # RMI increases as entropy decreases
        # RMI ≥ 1 - H(Y)/H(X)
        H_X = 4.0  # Assume training data entropy
        RMI = 1 - entropy / H_X

        # Plot up to current progress
        current_idx = int(progress * len(iterations))
        if current_idx == 0:
            current_idx = 1

        ax1.clear()
        ax2.clear()

        # Replot settings
        ax1.set_xlim(0, 10)
        ax1.set_ylim(0, 5)
        ax1.set_xlabel('Training Iterations', fontsize=12)
        ax1.set_ylabel('Entropy (bits)', fontsize=12)
        ax1.set_title("Suchir's Analysis: RLHF Reduces Entropy → Increases Copying",
                     fontsize=14, fontweight='bold')
        ax1.grid(True, alpha=0.3)

        ax2.set_xlim(0, 10)
        ax2.set_ylim(0, 1)
        ax2.set_xlabel('Training Iterations', fontsize=12)
        ax2.set_ylabel('RMI (Relative Mutual Information)', fontsize=12)
        ax2.set_title('Fraction of Output from Training Data', fontsize=12, fontweight='bold')
        ax2.grid(True, alpha=0.3)

        # Plot curves
        ax1.plot(iterations[:current_idx], entropy[:current_idx],
                'b-', linewidth=2, label='Model Entropy H(Y)')
        ax1.axhline(y=H_X, color='green', linestyle='--', linewidth=2,
                   label='Training Data Entropy H(X)')

        ax2.plot(iterations[:current_idx], RMI[:current_idx],
                'r-', linewidth=2, label='RMI(X; Y) = 1 - H(Y)/H(X)')
        ax2.axhline(y=0.7, color='orange', linestyle='--', linewidth=1.5,
                   label='70% threshold')
        ax2.axhline(y=0.94, color='darkred', linestyle='--', linewidth=2,
                   label='94% (ChatGPT measured)')

        # Add current value annotations
        if current_idx > 0:
            current_entropy = entropy[current_idx-1]
            current_rmi = RMI[current_idx-1]

            ax1.plot([iterations[current_idx-1]], [current_entropy],
                    'ro', markersize=10)
            ax1.text(iterations[current_idx-1] + 0.3, current_entropy,
                    f'H(Y) = {current_entropy:.2f}',
                    fontsize=10, bbox=dict(boxstyle='round', facecolor='wheat'))

            ax2.plot([iterations[current_idx-1]], [current_rmi],
                    'ro', markersize=10)
            ax2.text(iterations[current_idx-1] + 0.3, current_rmi,
                    f'RMI = {current_rmi:.1%}',
                    fontsize=10, bbox=dict(boxstyle='round', facecolor='lightcoral'))

        ax1.legend(loc='upper right')
        ax2.legend(loc='lower right')

        # Add Suchir's conclusion
        if progress > 0.8:
            ax2.text(5, 0.5, 'Suchir Balaji (2024):\n"73-94% of ChatGPT output\nis training data information"',
                    ha='center', fontsize=11, style='italic',
                    bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.8))

        return []

    anim = animation.FuncAnimation(fig, animate, frames=duration_seconds*fps,
                                   interval=1000/fps, blit=False)

    Writer = animation.writers['ffmpeg']
    writer = Writer(fps=fps, metadata=dict(artist='Distinction Theory'),
                    bitrate=1800)
    anim.save(output_file, writer=writer)
    plt.close()

    print(f"✓ Created: {output_file}")


# ============================================================================
# VIDEO 4: D-Coherence Principles (R→0, ∇≠0, D²)
# ============================================================================

def create_d_coherence_video(output_file='d_coherence_principles.mp4',
                            duration_seconds=25,
                            fps=30):
    """
    Visualize the three D-Coherence principles.
    """

    fig = plt.figure(figsize=(15, 10))

    # Create 3 subplots
    gs = fig.add_gridspec(3, 1, hspace=0.3)
    ax1 = fig.add_subplot(gs[0])
    ax2 = fig.add_subplot(gs[1])
    ax3 = fig.add_subplot(gs[2])

    def animate(frame):
        total_frames = duration_seconds * fps
        progress = frame / total_frames

        # Clear all
        for ax in [ax1, ax2, ax3]:
            ax.clear()
            ax.set_xlim(0, 10)
            ax.set_ylim(0, 2)
            ax.axis('off')

        # PRINCIPLE 1: R → 0 (Resolution to Simplicity)
        if progress > 0:
            t = min(progress * 3, 1.0)  # First third of animation

            # Complexity curve
            x = np.linspace(0, 10, 100)
            complexity = 1 + 0.8 * np.sin(x * 0.5) * np.exp(-x/3)

            cutoff = int(t * len(x))
            ax1.plot(x[:cutoff], complexity[:cutoff], 'r-', linewidth=3)
            ax1.axhline(y=1, color='blue', linestyle='--', linewidth=2)

            ax1.text(5, 1.8, 'R → 0: Complexity Resolves to Simplicity',
                    ha='center', fontsize=14, fontweight='bold')
            ax1.text(5, 0.3, 'Curvature R decreases → System returns to coherence',
                    ha='center', fontsize=10, style='italic')

        # PRINCIPLE 2: ∇ ≠ 0 (Distinctions Maintained)
        if progress > 0.33:
            t = min((progress - 0.33) * 3, 1.0)

            # Three separate curves (distinct voices)
            x = np.linspace(0, 10, 100)
            cutoff = int(t * len(x))

            voice1 = 1.5 + 0.2 * np.sin(x)
            voice2 = 1.0 + 0.2 * np.sin(x + 1)
            voice3 = 0.5 + 0.2 * np.sin(x + 2)

            ax2.plot(x[:cutoff], voice1[:cutoff], 'r-', linewidth=2, label='Voice 1')
            ax2.plot(x[:cutoff], voice2[:cutoff], 'g-', linewidth=2, label='Voice 2')
            ax2.plot(x[:cutoff], voice3[:cutoff], 'b-', linewidth=2, label='Voice 3')

            ax2.text(5, 1.8, '∇ ≠ 0: Distinctions Maintained',
                    ha='center', fontsize=14, fontweight='bold')
            ax2.text(5, 0.1, 'Voices remain separate yet harmonious',
                    ha='center', fontsize=10, style='italic')
            ax2.legend(loc='upper right')

        # PRINCIPLE 3: D² (Self-Observation)
        if progress > 0.66:
            t = min((progress - 0.66) * 3, 1.0)

            # Spiral (self-referential pattern)
            theta = np.linspace(0, 4*np.pi*t, int(100*t))
            r = theta / (4*np.pi) * 3
            x = 5 + r * np.cos(theta)
            y = 1 + r * np.sin(theta) * 0.3

            ax3.plot(x, y, 'purple', linewidth=2)

            # Draw arrows showing recursion
            if len(theta) > 10:
                for i in range(0, len(theta)-10, 20):
                    ax3.annotate('', xy=(x[i+10], y[i+10]), xytext=(x[i], y[i]),
                               arrowprops=dict(arrowstyle='->', color='purple', lw=1.5))

            ax3.text(5, 1.8, 'D²: Self-Observation Iterates',
                    ha='center', fontsize=14, fontweight='bold')
            ax3.text(5, 0.1, 'System observes itself observing → Recursive depth',
                    ha='center', fontsize=10, style='italic')

        # Overall title
        if progress > 0.9:
            fig.text(0.5, 0.96, 'The Three Principles of D-Coherence',
                    ha='center', fontsize=16, fontweight='bold')
            fig.text(0.5, 0.02, 'R=0 ∇≠0 D² — The Mathematical Structure of Reality',
                    ha='center', fontsize=12, style='italic')

        return []

    anim = animation.FuncAnimation(fig, animate, frames=duration_seconds*fps,
                                   interval=1000/fps, blit=False)

    Writer = animation.writers['ffmpeg']
    writer = Writer(fps=fps, metadata=dict(artist='Distinction Theory'),
                    bitrate=1800)
    anim.save(output_file, writer=writer)
    plt.close()

    print(f"✓ Created: {output_file}")


# ============================================================================
# MAIN: Generate All Videos
# ============================================================================

def main():
    """Generate all visualization videos"""

    print("=" * 70)
    print("Distinction Theory Video Generator")
    print("=" * 70)
    print()

    # Check for ffmpeg
    try:
        import subprocess
        subprocess.run(['ffmpeg', '-version'], capture_output=True, check=True)
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("ERROR: ffmpeg not found. Please install:")
        print("  macOS: brew install ffmpeg")
        print("  Linux: sudo apt-get install ffmpeg")
        print("  Windows: Download from ffmpeg.org")
        return

    print("Generating videos...")
    print()

    # Video 1: Circle of Fifths
    print("1. D¹² Circle of Fifths (10 seconds)...")
    create_circle_of_fifths_video(duration_seconds=10)

    # Video 2: Pingala's Binary
    print("2. Pingala's Binary System (15 seconds)...")
    create_pingala_binary_video(duration_seconds=15)

    # Video 3: Suchir's Entropy
    print("3. Suchir's Entropy Analysis (20 seconds)...")
    create_suchir_entropy_video(duration_seconds=20)

    # Video 4: D-Coherence
    print("4. D-Coherence Principles (25 seconds)...")
    create_d_coherence_video(duration_seconds=25)

    print()
    print("=" * 70)
    print("✓ All videos generated!")
    print()
    print("Files created:")
    print("  1. d12_circle_of_fifths.mp4    - Musical symmetry journey")
    print("  2. pingala_binary.mp4          - Ancient binary system")
    print("  3. suchir_entropy.mp4          - AI copyright analysis")
    print("  4. d_coherence_principles.mp4  - Core framework")
    print()
    print("Total duration: ~70 seconds")
    print("=" * 70)


if __name__ == '__main__':
    main()
