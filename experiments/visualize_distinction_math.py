#!/usr/bin/env python3
"""
Distinction Theory Math Visualizations: Revealing Mathematics Visually

Creates visualizations that make the abstract concepts of Distinction Theory concrete:

1. The D-monad structure: How observation creates self-reference
2. Thinking numbers: D-iterations collapsing back to unity
3. ℕ_D Higher Inductive Type: Coherence built into the foundation
4. D-crystals: Self-consistent mathematical structures
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyBboxPatch, FancyArrowPatch, Rectangle, ConnectionPatch
from matplotlib.patches import Wedge, Polygon, Arc
import matplotlib.patches as mpatches
from matplotlib.text import TextPath
from matplotlib.transforms import Affine2D
import matplotlib.path as mpath


def visualize_d_monad():
    """Visualize the fundamental D-monad structure"""

    fig, ax = plt.subplots(figsize=(12, 8))

    # Type X (base set)
    x_circle = Circle((2, 2), 1.5, facecolor='lightblue', edgecolor='black',
                     linewidth=2, alpha=0.8, label='Type X')
    ax.add_patch(x_circle)
    ax.text(2, 2, 'X\nelements\nx, y, ...', ha='center', va='center',
           fontsize=12, fontweight='bold')

    # Elements in X
    elements = [(1.5, 2.5), (2.5, 2.5), (2, 1.2)]
    element_labels = ['x', 'y', 'z']
    for (x, y), label in zip(elements, element_labels):
        ax.plot(x, y, 'o', markersize=12, color='blue', markeredgecolor='black', zorder=5)
        ax.text(x, y, label, ha='center', va='center', fontsize=14, fontweight='bold')

    # D X structure
    dx_box = FancyBboxPatch((5, 1), 4, 4, boxstyle="round,pad=0.1",
                           facecolor='lightcoral', edgecolor='black',
                           linewidth=2, alpha=0.8)
    ax.add_patch(dx_box)
    ax.text(7, 4.5, 'D X = Σ[x∈X] Σ[y∈X] (x ≡ y)', ha='center', va='center',
           fontsize=11, fontweight='bold')
    ax.text(7, 0.5, 'Elements: (x,y,p) where p proves x≡y', ha='center', va='center',
           fontsize=10)

    # Example element in D X
    ax.plot(6, 2.5, 'o', markersize=12, color='red', markeredgecolor='black', zorder=5)
    ax.text(6, 2.5, '(x,y,refl)', ha='center', va='center', fontsize=12, fontweight='bold')

    # Identity path visualization
    path = Arc((6, 2.5), 0.8, 0.8, theta1=0, theta2=180, linewidth=3, color='purple',
              label='Identity Path p: x≡y')
    ax.add_patch(path)
    ax.arrow(5.8, 2.5, 0.3, 0, head_width=0.05, head_length=0.05, fc='purple', ec='purple')

    # Arrow from X to D X
    arrow = FancyArrowPatch((3.5, 2), (5, 2), arrowstyle='->', linewidth=3,
                           color='darkgreen', mutation_scale=20)
    ax.add_patch(arrow)
    ax.text(4.25, 2.3, 'D', fontsize=16, fontweight='bold', color='darkgreen')

    # Title and explanation
    ax.set_title('The Distinction Monad D: Act of Self-Observation', fontsize=16, fontweight='bold')
    ax.text(0.02, 0.98, 'D X represents observing X: pairs of elements with proof they are identical',
           transform=ax.transAxes, fontsize=10, verticalalignment='top',
           bbox=dict(boxstyle="round,pad=0.3", facecolor="yellow", alpha=0.5))

    ax.set_xlim(0, 10)
    ax.set_ylim(0, 5)
    ax.set_aspect('equal')
    ax.axis('off')

    plt.tight_layout()
    plt.savefig('d_monad_visualization.png', dpi=300, bbox_inches='tight')
    print("✓ Created: d_monad_visualization.png")
    plt.close()


def visualize_thinking_numbers():
    """Visualize thinking numbers as D-iterations collapsing to unity"""

    fig, ax = plt.subplots(figsize=(14, 8))

    # Base Unit type
    unit_circle = Circle((2, 1), 0.8, facecolor='gold', edgecolor='black',
                        linewidth=3, alpha=0.9)
    ax.add_patch(unit_circle)
    ax.text(2, 1, '𝟙\n(Unit)', ha='center', va='center', fontsize=14, fontweight='bold')

    # D iterations tower
    levels = 12
    x_positions = np.linspace(2, 12, levels + 1)

    for i in range(levels + 1):
        # All D^n 𝟙 collapse back to Unit
        circle = Circle((x_positions[i], 1), 0.6 - i*0.03, facecolor='gold',
                       edgecolor='black', linewidth=2, alpha=0.8 - i*0.05)
        ax.add_patch(circle)

        # Label each level
        if i == 0:
            label = '𝟙'
        else:
            label = f'D^{i}(𝟙)'
        ax.text(x_positions[i], 1, label, ha='center', va='center',
               fontsize=12 - i*0.3, fontweight='bold')

        # Coherence proof: all equal to Unit
        if i > 0:
            ax.text(x_positions[i], 0.4, '≡ 𝟙', ha='center', va='center',
                   fontsize=10, color='darkgreen', fontweight='bold')

    # Thinking number structure
    for i in range(1, levels + 1):
        # Each thinking number carries its coherence proof
        proof_box = FancyBboxPatch((x_positions[i], 2.5), 1.2, 0.8,
                                  boxstyle="round,pad=0.1", facecolor='lightgreen',
                                  edgecolor='darkgreen', linewidth=2)
        ax.add_patch(proof_box)
        ax.text(x_positions[i], 2.5, f'Thinking\nNumber {i}', ha='center', va='center',
               fontsize=9, fontweight='bold')

        # Arrow showing the proof
        arrow = FancyArrowPatch((x_positions[i], 1.6), (x_positions[i], 2.3),
                               arrowstyle='->', linewidth=2, color='darkgreen')
        ax.add_patch(arrow)

    # Special 12
    twelve_circle = Circle((x_positions[12], 1), 0.8, facecolor='purple',
                          edgecolor='black', linewidth=4, alpha=0.7)
    ax.add_patch(twelve_circle)
    ax.text(x_positions[12], 1, 'D¹²(𝟙) ≡ 𝟙', ha='center', va='center',
           fontsize=12, fontweight='bold', color='white')

    # Title
    ax.set_title('Thinking Numbers: Self-Observation Iterations All Return to Unity',
                fontsize=16, fontweight='bold')
    ax.text(0.02, 0.95, 'Each "number" n is D^n(𝟙) with built-in proof ≡ 𝟙.\n' +
           'Self-observation of self-observation = self-observation.',
           transform=ax.transAxes, fontsize=10, verticalalignment='top',
           bbox=dict(boxstyle="round,pad=0.3", facecolor="lightyellow", alpha=0.8))

    ax.set_xlim(0, 14)
    ax.set_ylim(-0.5, 4)
    ax.axis('off')

    plt.tight_layout()
    plt.savefig('thinking_numbers_visualization.png', dpi=300, bbox_inches='tight')
    print("✓ Created: thinking_numbers_visualization.png")
    plt.close()


def visualize_nat_d_hit():
    """Visualize ℕ_D as Higher Inductive Type with coherence"""

    fig, ax = plt.subplots(figsize=(12, 10))

    # Zero constructor
    zero_box = Rectangle((1, 8), 2, 1, facecolor='lightblue', edgecolor='black',
                        linewidth=2, alpha=0.8)
    ax.add_patch(zero_box)
    ax.text(2, 8.5, 'zero-D : ℕ_D', ha='center', va='center',
           fontsize=12, fontweight='bold')

    # Successor constructor
    suc_box = Rectangle((5, 8), 2, 1, facecolor='lightgreen', edgecolor='black',
                       linewidth=2, alpha=0.8)
    ax.add_patch(suc_box)
    ax.text(6, 8.5, 'suc-D : ℕ_D → ℕ_D', ha='center', va='center',
           fontsize=12, fontweight='bold')

    # Coherence axiom (path constructor)
    coherence_box = FancyBboxPatch((3, 5), 6, 2, boxstyle="round,pad=0.2",
                                  facecolor='lightcoral', edgecolor='red',
                                  linewidth=3, alpha=0.8)
    ax.add_patch(coherence_box)
    ax.text(6, 6, 'coherence-axiom : (n:ℕ_D) → D(suc-D n) ≡ suc-D-map(η n)',
           ha='center', va='center', fontsize=11, fontweight='bold')

    # Show what this means
    ax.text(6, 4.5, 'Path constructor: Observing successor ≡ Successor of observation',
           ha='center', va='center', fontsize=10, color='red')

    # Example elements
    elements = [(2, 2), (4, 2), (6, 2), (8, 2)]
    labels = ['0', '1', '2', '3']
    colors = ['blue', 'green', 'orange', 'purple']

    for i, ((x, y), label, color) in enumerate(zip(elements, labels, colors)):
        circle = Circle((x, y), 0.4, facecolor=color, edgecolor='black',
                       linewidth=2, alpha=0.9)
        ax.add_patch(circle)
        ax.text(x, y, label, ha='center', va='center', fontsize=14, fontweight='bold')

        # Show coherence path for successors
        if i > 0:
            # Path from D(suc(n-1)) to suc(D(n-1))
            path = Arc((x, y-0.8), 1.2, 0.8, theta1=0, theta2=180, linewidth=2,
                      color='red', linestyle='--')
            ax.add_patch(path)
            ax.text(x, y-1.2, 'Coherence\nPath', ha='center', va='center',
                   fontsize=8, color='red')

    # Arrows showing construction
    arrow1 = FancyArrowPatch((2, 7), (2, 2.4), arrowstyle='->', linewidth=2, color='blue')
    ax.add_patch(arrow1)

    arrow2 = FancyArrowPatch((6, 7), (6, 2.4), arrowstyle='->', linewidth=2, color='green')
    ax.add_patch(arrow2)

    # Path arrow
    path_arrow = FancyArrowPatch((6, 4.8), (6, 2.4), arrowstyle='<->', linewidth=3,
                                color='red', linestyle='--')
    ax.add_patch(path_arrow)
    ax.text(6.5, 3.5, 'Path\nConstructor', ha='left', va='center',
           fontsize=10, color='red', fontweight='bold')

    # Title
    ax.set_title('ℕ_D: Higher Inductive Type with Built-in Coherence', fontsize=16, fontweight='bold')
    ax.text(0.02, 0.98, 'ℕ_D is not ℕ with coherence proven later.\n' +
           'It\'s a new type where coherence is axiomatized as a path constructor.\n' +
           'Every operation inherits D-coherence automatically.',
           transform=ax.transAxes, fontsize=10, verticalalignment='top',
           bbox=dict(boxstyle="round,pad=0.3", facecolor="lightyellow", alpha=0.8))

    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis('off')

    plt.tight_layout()
    plt.savefig('nat_d_hit_visualization.png', dpi=300, bbox_inches='tight')
    print("✓ Created: nat_d_hit_visualization.png")
    plt.close()


def visualize_d_crystals():
    """Visualize D-crystals as self-consistent structures"""

    fig, ax = plt.subplots(figsize=(14, 8))

    # Different types and their D-behavior
    types_data = [
        ('ℕ (Standard)', 'D ℕ ≢ ℕ', 'red', 'Not self-consistent'),
        ('S¹ (Circle)', 'D S¹ ≢ S¹', 'orange', 'Order-dependent coherence'),
        ('𝟙 (Unit)', 'D 𝟙 ≡ 𝟙', 'green', 'D-Crystal!'),
        ('ℕ_D (D-Native)', 'D ℕ_D ≡ ℕ_D', 'blue', 'D-Crystal!'),
        ('D-Crystals', 'D X ≃ X', 'purple', 'Self-consistent by definition'),
    ]

    y_positions = np.linspace(6, 1, len(types_data))

    for i, (name, property, color, desc) in enumerate(types_data):
        y = y_positions[i]

        # Type box
        box = FancyBboxPatch((2, y-0.4), 3, 0.8, boxstyle="round,pad=0.1",
                           facecolor=color, edgecolor='black', linewidth=2, alpha=0.8)
        ax.add_patch(box)
        ax.text(3.5, y, name, ha='center', va='center', fontsize=12, fontweight='bold')

        # Property
        ax.text(6, y, property, ha='center', va='center', fontsize=11, fontweight='bold')

        # Description
        ax.text(9, y, desc, ha='center', va='center', fontsize=10)

        # For D-crystals, show self-consistency
        if 'D-Crystal' in name or 'D-Crystal!' in desc:
            # Loop arrow showing D X ≃ X
            loop = Arc((3.5, y+0.6), 2, 1, theta1=0, theta2=180, linewidth=3, color=color)
            ax.add_patch(loop)
            arrow = FancyArrowPatch((2.5, y+0.6), (4.5, y+0.6), arrowstyle='->',
                                   linewidth=3, color=color)
            ax.add_patch(arrow)
            ax.text(3.5, y+1, 'D', fontsize=14, fontweight='bold', color=color, ha='center')

    # Self-consistency explanation
    ax.text(0.02, 0.95, 'D-Crystals are types stable under self-observation.\n' +
           'D X ≃ X means observing the type doesn\'t change its structure.\n' +
           'These are the "self-consistent" mathematical objects.',
           transform=ax.transAxes, fontsize=10, verticalalignment='top',
           bbox=dict(boxstyle="round,pad=0.3", facecolor="lightyellow", alpha=0.8))

    # Title
    ax.set_title('D-Crystals: Self-Consistent Mathematical Structures', fontsize=16, fontweight='bold')

    ax.set_xlim(0, 12)
    ax.set_ylim(0, 8)
    ax.axis('off')

    plt.tight_layout()
    plt.savefig('d_crystals_visualization.png', dpi=300, bbox_inches='tight')
    print("✓ Created: d_crystals_visualization.png")
    plt.close()


def main():
    """Generate all visualizations"""
    print("Creating Distinction Theory Math Visualizations...")

    visualize_d_monad()
    visualize_thinking_numbers()
    visualize_nat_d_hit()
    visualize_d_crystals()

    print("\n✓ All visualizations created!")
    print("Files: d_monad_visualization.png, thinking_numbers_visualization.png,")
    print("       nat_d_hit_visualization.png, d_crystals_visualization.png")


if __name__ == "__main__":
    main()