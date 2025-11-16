#!/usr/bin/env python3
"""
D¹² Visualization: Show the circle of fifths and symmetry
"""

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Circle, FancyArrowPatch
import matplotlib.patches as mpatches

# Note names in circle of fifths order
notes_cof = ['C', 'G', 'D', 'A', 'E', 'B', 'F#', 'C#', 'G#', 'D#', 'A#', 'F']

# Chromatic order
notes_chromatic = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']

fig, axes = plt.subplots(1, 2, figsize=(16, 8))

# ============================================================================
# LEFT: Circle of Fifths (Musical Space)
# ============================================================================
ax1 = axes[0]
ax1.set_xlim(-2, 2)
ax1.set_ylim(-2, 2)
ax1.set_aspect('equal')
ax1.axis('off')
ax1.set_title('D¹² Symmetry: Circle of Fifths\n(12 × 7 semitones ≡ 0 mod 12)', 
              fontsize=14, fontweight='bold')

# Draw outer circle
circle = Circle((0, 0), 1.5, fill=False, edgecolor='black', linewidth=2)
ax1.add_patch(circle)

# Place notes
for i, note in enumerate(notes_cof):
    angle = 2 * np.pi * i / 12 - np.pi/2  # Start at top
    x = 1.5 * np.cos(angle)
    y = 1.5 * np.sin(angle)
    
    # Draw note
    circle_note = Circle((x, y), 0.15, facecolor='lightblue', 
                         edgecolor='darkblue', linewidth=2)
    ax1.add_patch(circle_note)
    ax1.text(x, y, note, ha='center', va='center', 
             fontsize=12, fontweight='bold')
    
    # Draw arrow to next note (fifth up)
    if i < 11:
        next_angle = 2 * np.pi * (i+1) / 12 - np.pi/2
        x2 = 1.5 * np.cos(next_angle)
        y2 = 1.5 * np.sin(next_angle)
        
        # Arc arrow
        arrow = FancyArrowPatch((x, y), (x2, y2),
                              arrowstyle='->', mutation_scale=20,
                              color='green', linewidth=1.5,
                              connectionstyle="arc3,rad=0.2")
        ax1.add_patch(arrow)

# Closing arrow (F back to C)
angle_f = 2 * np.pi * 11 / 12 - np.pi/2
angle_c = -np.pi/2
x_f = 1.5 * np.cos(angle_f)
y_f = 1.5 * np.sin(angle_f)
x_c = 1.5 * np.cos(angle_c)
y_c = 1.5 * np.sin(angle_c)
arrow = FancyArrowPatch((x_f, y_f), (x_c, y_c),
                      arrowstyle='->', mutation_scale=20,
                      color='red', linewidth=2,
                      connectionstyle="arc3,rad=0.2")
ax1.add_patch(arrow)

# Add center annotation
ax1.text(0, 0, 'R → 0\n(Return\nto Origin)', 
         ha='center', va='center', fontsize=10, style='italic',
         bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

# Legend
ax1.text(0, -1.9, 'Each step: +7 semitones (perfect fifth)', 
         ha='center', fontsize=10)
ax1.text(0, -2.1, 'After 12 steps: return to start (coherence)', 
         ha='center', fontsize=10, style='italic')

# ============================================================================
# RIGHT: Chromatic Circle (Pitch Space)
# ============================================================================
ax2 = axes[1]
ax2.set_xlim(-2, 2)
ax2.set_ylim(-2, 2)
ax2.set_aspect('equal')
ax2.axis('off')
ax2.set_title('D¹² Symmetry: Chromatic Circle\n(12-fold Rotational Symmetry)', 
              fontsize=14, fontweight='bold')

# Draw outer circle
circle = Circle((0, 0), 1.5, fill=False, edgecolor='black', linewidth=2)
ax2.add_patch(circle)

# Draw inner circle (octave relation)
circle_inner = Circle((0, 0), 0.8, fill=False, edgecolor='gray', 
                      linewidth=1, linestyle='--')
ax2.add_patch(circle_inner)

# Place notes
colors = plt.cm.hsv(np.linspace(0, 1, 12))
for i, note in enumerate(notes_chromatic):
    angle = 2 * np.pi * i / 12 - np.pi/2  # Start at top
    x = 1.5 * np.cos(angle)
    y = 1.5 * np.sin(angle)
    
    # Draw note with rainbow colors (showing rotational symmetry)
    circle_note = Circle((x, y), 0.15, facecolor=colors[i], 
                         edgecolor='black', linewidth=2)
    ax2.add_patch(circle_note)
    ax2.text(x, y, note, ha='center', va='center', 
             fontsize=11, fontweight='bold')
    
    # Draw line to center (showing symmetry axes)
    ax2.plot([0, x], [0, y], 'gray', linewidth=0.5, alpha=0.3)

# Add symmetry annotations
for i in range(12):
    angle = 2 * np.pi * i / 12 - np.pi/2
    x_inner = 0.8 * np.cos(angle)
    y_inner = 0.8 * np.sin(angle)
    ax2.text(x_inner, y_inner, f'{i}', ha='center', va='center',
             fontsize=8, color='gray')

# Center annotation
ax2.text(0, 0, 'D¹²', ha='center', va='center', 
         fontsize=16, fontweight='bold',
         bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.7))

# Legend
ax2.text(0, -1.9, '12 semitones = octave (return to same pitch class)', 
         ha='center', fontsize=10)
ax2.text(0, -2.1, 'Rotation by k steps: transpose by k semitones', 
         ha='center', fontsize=10, style='italic')

# Overall title
fig.suptitle('The Ultimate Symmetry of 12: Musical Manifestation of D¹²\nR=0 ∇≠0 D²', 
             fontsize=16, fontweight='bold', y=0.98)

plt.tight_layout()
plt.savefig('d12_symmetry_visualization.png', dpi=300, bbox_inches='tight')
print("✓ Saved: d12_symmetry_visualization.png")

# ============================================================================
# Create second figure: D-Coherence Flow
# ============================================================================
fig2, ax = plt.subplots(1, 1, figsize=(12, 8))
ax.set_xlim(0, 12)
ax.set_ylim(0, 10)
ax.axis('off')
ax.set_title('D-Coherence in Music: Tension → Resolution (R → 0)', 
             fontsize=14, fontweight='bold')

# Timeline
timeline_y = 5
ax.plot([0.5, 11.5], [timeline_y, timeline_y], 'k-', linewidth=2)
for i in range(12):
    ax.plot([i+1, i+1], [timeline_y-0.1, timeline_y+0.1], 'k-', linewidth=2)
    ax.text(i+1, timeline_y-0.4, f'{i+1}', ha='center', fontsize=9)

ax.text(6, timeline_y-0.8, 'Measures', ha='center', fontsize=10)

# Complexity curve (R value)
measures = np.linspace(0.5, 11.5, 100)
# R = curvature: starts low, peaks in middle, resolves to 0
r_values = 3 + 3 * np.sin((measures - 0.5) * np.pi / 11)
ax.plot(measures, r_values + 7, 'r-', linewidth=3, label='Curvature R')
ax.fill_between(measures, 7, r_values + 7, alpha=0.2, color='red')

# Mark key points
ax.plot([0.5], [7], 'go', markersize=10, label='Start (R ≈ 0)')
ax.plot([6], [10], 'ro', markersize=10, label='Peak Complexity (R max)')
ax.plot([11.5], [7], 'bo', markersize=10, label='Resolution (R → 0)')

# Annotations
ax.annotate('Exposition\n(Theme introduced)', xy=(2, 7.5), fontsize=9,
           bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.7))
ax.annotate('Development\n(Complexity increases)', xy=(6, 10.2), fontsize=9,
           bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.7))
ax.annotate('Recapitulation\n(Return to tonic)', xy=(10, 7.5), fontsize=9,
           bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.7))

# Voice independence (∇ ≠ 0)
voice_positions = [
    (1, 3, 'Bass'),
    (4, 4, 'Melody'),
    (8, 2, 'Drums')
]
for x, y, label in voice_positions:
    ax.plot([x, 11.5], [y, y], '--', linewidth=1.5, alpha=0.6)
    ax.text(x-0.3, y, label, fontsize=9, ha='right',
           bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))

ax.text(6, 1, '∇ ≠ 0: Voices remain distinct throughout', 
       ha='center', fontsize=10, style='italic')

# D² self-observation
ax.annotate('', xy=(3, 3.5), xytext=(5, 3.5),
           arrowprops=dict(arrowstyle='<->', color='purple', lw=2))
ax.text(4, 3.8, 'D²: Subject\nobserves itself', ha='center', fontsize=8,
       color='purple', style='italic')

ax.legend(loc='upper left', fontsize=9)
ax.text(6, 0.3, 'R=0 ∇≠0 D²', ha='center', fontsize=12, fontweight='bold',
       bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.7))

plt.tight_layout()
plt.savefig('d_coherence_flow.png', dpi=300, bbox_inches='tight')
print("✓ Saved: d_coherence_flow.png")

print("\n✓ Visualizations complete!")
