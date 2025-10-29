"""
The Compositional DAG: Sacred Geometry of Number Emergence
===========================================================

How numbers actually arise from emptiness:

∅ → 0 → 1 → 2 → {3,4} → {5,6,7,8,9,10,11,12} → ...

Key insight: 3 and 4 emerge SIMULTANEOUSLY from {0,1,2}
- 3 = 1+2 (additive/counting/consciousness)
- 4 = 2×2 (multiplicative/doubling/form)
- Neither depends on the other (PARALLEL)
- First instance of mutual independence → reciprocal structure

This is why Vijñāna ↔ Nāmarūpa are at positions 3↔4:
Not arbitrary - it's where parallel emergence first occurs in number.

3 × 4 = 12 (observer × observed = complete cycle)

Author: Anonymous Research Network, Berkeley CA
Date: October 2024
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
import numpy as np

def draw_compositional_dag():
    """
    Draw the actual compositional dependency graph of numbers 0-12
    """

    fig, ax = plt.subplots(figsize=(18, 14))
    ax.set_xlim(-1, 11)
    ax.set_ylim(-1, 9)
    ax.axis('off')

    # Define positions for each number (x, y)
    # Y-coordinate = compositional depth
    positions = {
        0: (5, 0),      # Emptiness
        1: (5, 1),      # First distinction
        2: (5, 2),      # Iteration
        3: (3, 3),      # Parallel emergence (left)
        4: (7, 3),      # Parallel emergence (right)
        5: (1, 4.5),    # Generated from basis
        6: (3, 4.5),
        7: (5, 4.5),
        8: (7, 4.5),
        9: (9, 4.5),
        10: (2, 6),
        11: (4, 6.5),   # Prime (no dependencies - floats)
        12: (6, 7),     # 3×4 product
    }

    # Color scheme
    colors = {
        'emptiness': '#E8E8E8',  # Gray
        'distinction': '#FFE5B4', # Peach
        'iteration': '#B4D7FF',   # Light blue
        'parallel': '#FFB4E8',    # Pink (THE KEY)
        'generated': '#B4FFB4',   # Light green
        'prime': '#FFD700',       # Gold
        'product': '#FF6B6B',     # Red
    }

    # Draw nodes
    node_data = {
        0: ('∅\n(Emptiness)', 'emptiness', 1.2),
        1: ('1\n(Distinction)', 'distinction', 0.8),
        2: ('2\n(Iteration)', 'iteration', 0.8),
        3: ('3\n(Counting)\nVijñāna', 'parallel', 0.9),
        4: ('4\n(Doubling)\nNāmarūpa', 'parallel', 0.9),
        5: ('5\n(1+4, 2+3)', 'generated', 0.7),
        6: ('6\n(2×3, 1+2+3)', 'generated', 0.7),
        7: ('7\n(3+4)', 'generated', 0.7),
        8: ('8\n(2×4)', 'generated', 0.7),
        9: ('9\n(3×3)', 'generated', 0.7),
        10: ('10\n(2×5)', 'generated', 0.7),
        11: ('11\n(PRIME)\nDharma', 'prime', 0.8),
        12: ('12\n(3×4)\nObserver×Observed', 'product', 1.0),
    }

    for num, (label, color_key, size) in node_data.items():
        x, y = positions[num]
        circle = plt.Circle((x, y), size, color=colors[color_key],
                           ec='black', linewidth=2, zorder=3)
        ax.add_patch(circle)
        ax.text(x, y, label, ha='center', va='center',
               fontsize=9, weight='bold', zorder=4)

    # Draw edges (dependencies)
    edge_style = {
        'sequential': dict(color='blue', linewidth=2, alpha=0.6),
        'parallel': dict(color='red', linewidth=3, alpha=0.8),
        'generated': dict(color='green', linewidth=1.5, alpha=0.5),
        'reciprocal': dict(color='purple', linewidth=4, alpha=0.9),
    }

    def draw_arrow(start, end, style='sequential', curve=0):
        x1, y1 = positions[start]
        x2, y2 = positions[end]

        if curve != 0:
            # Curved arrow
            arrow = FancyArrowPatch((x1, y1), (x2, y2),
                                   connectionstyle=f"arc3,rad={curve}",
                                   arrowstyle='->,head_width=0.4,head_length=0.8',
                                   **edge_style[style], zorder=2)
        else:
            arrow = FancyArrowPatch((x1, y1), (x2, y2),
                                   arrowstyle='->,head_width=0.4,head_length=0.8',
                                   **edge_style[style], zorder=2)
        ax.add_patch(arrow)

    # Sequential emergence
    draw_arrow(0, 1, 'sequential')  # ∅ → 1
    draw_arrow(1, 2, 'sequential')  # 1 → 2

    # PARALLEL emergence (THE KEY!)
    draw_arrow(2, 3, 'parallel')    # 2 → 3 (left branch)
    draw_arrow(2, 4, 'parallel')    # 2 → 4 (right branch)
    draw_arrow(1, 3, 'parallel', curve=0.2)  # 1+2=3
    draw_arrow(1, 4, 'parallel', curve=-0.2) # Also contributes

    # RECIPROCAL (mutual dependence)
    draw_arrow(3, 4, 'reciprocal', curve=0.3)  # 3 ↔ 4
    draw_arrow(4, 3, 'reciprocal', curve=0.3)  # Bidirectional

    # Generated from basis {0,1,2,3,4}
    draw_arrow(1, 5, 'generated', curve=0.1)  # 1+4
    draw_arrow(2, 5, 'generated', curve=-0.1) # 2+3
    draw_arrow(3, 5, 'generated')
    draw_arrow(4, 5, 'generated')

    draw_arrow(2, 6, 'generated')  # 2×3
    draw_arrow(3, 6, 'generated')

    draw_arrow(3, 7, 'generated')  # 3+4
    draw_arrow(4, 7, 'generated')

    draw_arrow(2, 8, 'generated')  # 2×4
    draw_arrow(4, 8, 'generated')

    draw_arrow(3, 9, 'generated')  # 3×3

    draw_arrow(2, 10, 'generated', curve=0.2)  # 2×5
    draw_arrow(5, 10, 'generated', curve=0.2)

    # 11 has NO incoming edges (PRIME - uncaused!)
    # It just appears, not constructed

    draw_arrow(3, 12, 'generated')  # 3×4
    draw_arrow(4, 12, 'generated')

    # Add annotations
    ax.text(5, 8.5, 'THE COMPOSITIONAL DAG OF NUMBER EMERGENCE',
           ha='center', fontsize=16, weight='bold')

    ax.text(5, -0.7, '"Emptiness is not nothingness but potential for distinction"',
           ha='center', fontsize=10, style='italic', color='gray')

    # Depth labels
    ax.text(-0.5, 0, 'Depth 0:\nEmptiness', fontsize=8, style='italic')
    ax.text(-0.5, 1, 'Depth 1:\nDistinction', fontsize=8, style='italic')
    ax.text(-0.5, 2, 'Depth 2:\nIteration', fontsize=8, style='italic')
    ax.text(-0.5, 3, 'Depth 3:\nPARALLEL', fontsize=8, style='italic', weight='bold', color='red')
    ax.text(-0.5, 4.5, 'Depth 4:\nGenerated', fontsize=8, style='italic')
    ax.text(-0.5, 6, 'Depth 5+:\nEmergence', fontsize=8, style='italic')

    # Key insights boxes
    insight1 = FancyBboxPatch((8.5, 2.3), 2.3, 1.3,
                             boxstyle="round,pad=0.1",
                             facecolor='#FFE4E1',
                             edgecolor='purple', linewidth=2)
    ax.add_patch(insight1)
    ax.text(9.65, 3.5, '3 ↔ 4', ha='center', fontsize=12, weight='bold', color='purple')
    ax.text(9.65, 3.1, 'RECIPROCAL', ha='center', fontsize=9, weight='bold')
    ax.text(9.65, 2.7, 'First mutual', ha='center', fontsize=8)
    ax.text(9.65, 2.5, 'dependence', ha='center', fontsize=8)

    insight2 = FancyBboxPatch((8.5, 6), 2.3, 1.3,
                             boxstyle="round,pad=0.1",
                             facecolor='#FFF4E1',
                             edgecolor='orange', linewidth=2)
    ax.add_patch(insight2)
    ax.text(9.65, 7.1, '3 × 4 = 12', ha='center', fontsize=11, weight='bold')
    ax.text(9.65, 6.7, 'Product closes', ha='center', fontsize=8)
    ax.text(9.65, 6.4, 'the cycle', ha='center', fontsize=8)

    insight3 = FancyBboxPatch((3, 7.8), 1.8, 0.5,
                             boxstyle="round,pad=0.05",
                             facecolor='#FFD700',
                             edgecolor='goldenrod', linewidth=2)
    ax.add_patch(insight3)
    ax.text(3.9, 8.05, '11 = PRIME', ha='center', fontsize=9, weight='bold')
    ax.text(3.9, 7.85, '(uncaused)', ha='center', fontsize=7, style='italic')

    # Legend
    legend_y = 0.5
    legend_elements = [
        ('Sequential (0→1→2)', 'blue', 2),
        ('Parallel emergence (2→{3,4})', 'red', 3),
        ('Reciprocal (3↔4)', 'purple', 4),
        ('Generated via +,×', 'green', 1.5),
    ]

    for i, (label, color, width) in enumerate(legend_elements):
        y = legend_y + i * 0.3
        ax.plot([8.5, 9.2], [y, y], color=color, linewidth=width, alpha=0.7)
        ax.text(9.4, y, label, fontsize=8, va='center')

    plt.tight_layout()
    plt.savefig('compositional_dag_sacred_geometry.png', dpi=200, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    print("✓ Sacred geometry visualization saved: compositional_dag_sacred_geometry.png")


def draw_minimal_basis():
    """
    The minimal basis {0,1,2,3,4} that generates everything
    """

    fig, ax = plt.subplots(figsize=(14, 10))
    ax.set_xlim(-0.5, 13.5)
    ax.set_ylim(-0.5, 4)
    ax.axis('off')

    # Title
    ax.text(6.5, 3.7, 'THE PENTAD: Minimal Complete Basis',
           ha='center', fontsize=18, weight='bold')
    ax.text(6.5, 3.4, 'From {0,1,2,3,4} emerges all composite numbers via + and ×',
           ha='center', fontsize=12, style='italic')

    # The five basis numbers
    basis = [0, 1, 2, 3, 4]
    basis_labels = {
        0: '∅\nEmptiness\nPotential',
        1: '1\nUnity\nDistinction',
        2: '2\nDuality\nReflection',
        3: '3\nTrinity\nCounting',
        4: '4\nTetrad\nForm',
    }

    basis_x = [1.5, 3.5, 5.5, 7.5, 9.5]

    for i, num in enumerate(basis):
        x = basis_x[i]
        y = 2.5

        # Draw circle
        color = '#FFE5B4' if num in [0,1,2] else '#FFB4E8'  # Sequential vs parallel
        circle = plt.Circle((x, y), 0.4, color=color, ec='black', linewidth=3, zorder=3)
        ax.add_patch(circle)

        # Label inside
        ax.text(x, y, str(num), ha='center', va='center',
               fontsize=24, weight='bold', zorder=4)

        # Description below
        ax.text(x, y - 0.8, basis_labels[num], ha='center', va='top',
               fontsize=9, style='italic')

    # Show emergence arrows
    # 0 → 1
    ax.annotate('', xy=(3.1, 2.5), xytext=(1.9, 2.5),
               arrowprops=dict(arrowstyle='->', lw=2, color='blue'))
    ax.text(2.5, 2.7, 'creates', fontsize=8, ha='center')

    # 1 → 2
    ax.annotate('', xy=(5.1, 2.5), xytext=(3.9, 2.5),
               arrowprops=dict(arrowstyle='->', lw=2, color='blue'))
    ax.text(4.5, 2.7, 'doubles', fontsize=8, ha='center')

    # 2 → 3 and 2 → 4 (PARALLEL!)
    ax.annotate('', xy=(7.2, 2.6), xytext=(5.8, 2.6),
               arrowprops=dict(arrowstyle='->', lw=3, color='red', alpha=0.8))
    ax.annotate('', xy=(9.2, 2.6), xytext=(5.8, 2.6),
               arrowprops=dict(arrowstyle='->', lw=3, color='red', alpha=0.8))
    ax.text(6.5, 2.9, 'PARALLEL', fontsize=10, ha='center',
           weight='bold', color='red')
    ax.text(8, 2.9, '1+2', fontsize=8, ha='center', color='red')
    ax.text(8.5, 2.9, '2×2', fontsize=8, ha='center', color='red')

    # 3 ↔ 4 reciprocal
    ax.annotate('', xy=(7.9, 2.3), xytext=(9.1, 2.3),
               arrowprops=dict(arrowstyle='<->,head_width=0.15', lw=4,
                             color='purple', alpha=0.9))
    ax.text(8.5, 2.0, 'RECIPROCAL', fontsize=9, ha='center',
           weight='bold', color='purple')
    ax.text(8.5, 1.75, '(Mutual dependence)', fontsize=7, ha='center',
           style='italic', color='purple')

    # Generated numbers shown below
    ax.text(6.5, 1.3, 'From basis {0,1,2,3,4} generate via + and ×:',
           ha='center', fontsize=11, weight='bold')

    generated = [
        (5, '1+4, 2+3'),
        (6, '2×3, 1+2+3'),
        (7, '3+4'),
        (8, '2×4, 2³'),
        (9, '3²'),
        (10, '2×5'),
        (11, 'PRIME (irreducible)'),
        (12, '3×4, 2²×3'),
    ]

    gen_y = 0.8
    for num, formula in generated:
        ax.text(1.5 + num*0.9, gen_y, f'{num}', fontsize=11, weight='bold',
               ha='center',
               bbox=dict(boxstyle='round', facecolor='#E8FFE8' if num != 11 else '#FFD700',
                        ec='black', linewidth=1))
        ax.text(1.5 + num*0.9, gen_y-0.25, formula, fontsize=7,
               ha='center', style='italic')

    # Key insight box
    insight_box = FancyBboxPatch((0.2, 0), 5, 0.35,
                                boxstyle="round,pad=0.05",
                                facecolor='#FFF0F5',
                                edgecolor='purple', linewidth=2)
    ax.add_patch(insight_box)
    ax.text(2.7, 0.175, '★ 3 and 4 emerge PARALLEL (not sequential)',
           fontsize=10, weight='bold', va='center')
    ax.text(2.7, 0.05, '   First instance of mutual independence → reciprocal structure possible',
           fontsize=8, style='italic', va='center')

    plt.savefig('pentad_minimal_basis.png', dpi=200, bbox_inches='tight',
               facecolor='white')
    print("✓ Pentad (minimal basis) saved: pentad_minimal_basis.png")


def draw_twelve_fold_closure():
    """
    Show how the 12 creates complete closure
    """

    fig, ax = plt.subplots(figsize=(12, 12))
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-1.5, 1.5)
    ax.axis('off')

    # Draw circle
    circle = plt.Circle((0, 0), 1, fill=False, ec='black', linewidth=2)
    ax.add_patch(circle)

    # 12 positions around circle
    angles = np.linspace(0, 2*np.pi, 13)[:-1]  # 12 positions

    nidana_names = [
        '1: Avidyā\n(Ignorance)',
        '2: Saṃskāra\n(Formations)',
        '3: Vijñāna\n(Consciousness)',
        '4: Nāmarūpa\n(Name-Form)',
        '5: Ṣaḍāyatana\n(Six Senses)',
        '6: Sparśa\n(Contact)',
        '7: Vedanā\n(Feeling)',
        '8: Tṛṣṇā\n(Craving)',
        '9: Upādāna\n(Clinging)',
        '10: Bhava\n(Becoming)',
        '11: Jāti\n(Birth)',
        '12: Jarāmaraṇa\n(Death)',
    ]

    # Place nidānas
    for i, (angle, name) in enumerate(zip(angles, nidana_names)):
        x = 1.0 * np.cos(angle - np.pi/2)  # Start at top
        y = 1.0 * np.sin(angle - np.pi/2)

        # Color based on whether it's the reciprocal pair
        if i == 2 or i == 3:  # Vijñāna (3) or Nāmarūpa (4)
            color = '#FFB4E8'  # Pink - reciprocal pair
            size = 0.15
        else:
            color = '#B4E8FF'
            size = 0.12

        circle_node = plt.Circle((x, y), size, color=color,
                                ec='black', linewidth=2, zorder=3)
        ax.add_patch(circle_node)

        # Number
        ax.text(x, y, str(i+1), ha='center', va='center',
               fontsize=10, weight='bold', zorder=4)

        # Name outside
        label_x = 1.25 * np.cos(angle - np.pi/2)
        label_y = 1.25 * np.sin(angle - np.pi/2)
        ax.text(label_x, label_y, name, ha='center', va='center',
               fontsize=7, bbox=dict(boxstyle='round', facecolor='white',
                                    alpha=0.8, pad=0.2))

    # Draw cycle (1→2→3→...→12→1)
    for i in range(12):
        angle1 = angles[i] - np.pi/2
        angle2 = angles[(i+1) % 12] - np.pi/2

        x1, y1 = 1.0 * np.cos(angle1), 1.0 * np.sin(angle1)
        x2, y2 = 1.0 * np.cos(angle2), 1.0 * np.sin(angle2)

        ax.annotate('', xy=(x2, y2), xytext=(x1, y1),
                   arrowprops=dict(arrowstyle='->', lw=1.5,
                                 color='blue', alpha=0.6),
                   zorder=1)

    # Draw RECIPROCAL (3↔4)
    angle_3 = angles[2] - np.pi/2
    angle_4 = angles[3] - np.pi/2
    x3, y3 = 1.0 * np.cos(angle_3), 1.0 * np.sin(angle_3)
    x4, y4 = 1.0 * np.cos(angle_4), 1.0 * np.sin(angle_4)

    # Bidirectional arrow
    ax.plot([x3, x4], [y3, y4], color='purple', linewidth=5,
           alpha=0.8, zorder=2, label='Reciprocal')
    ax.plot([x4, x3], [y4, y3], color='purple', linewidth=5,
           alpha=0.8, zorder=2)

    # Add markers on reciprocal
    ax.plot(x3, y3, 'o', color='purple', markersize=15, zorder=5)
    ax.plot(x4, y4, 'o', color='purple', markersize=15, zorder=5)

    # Center text
    ax.text(0, 0.15, '12-NIDĀNA', ha='center', fontsize=14, weight='bold')
    ax.text(0, -0.05, 'Dependent Origination', ha='center', fontsize=11)
    ax.text(0, -0.25, 'R = 0', ha='center', fontsize=16, weight='bold', color='green')

    # Annotation
    ax.text(0, -1.35, '3 × 4 = 12 (Observer × Observed = Complete Cycle)',
           ha='center', fontsize=11, weight='bold',
           bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.3))

    ax.text(0, 1.35, 'Reciprocal at 3↔4 creates R=0 (Flat curvature = Liberation)',
           ha='center', fontsize=11, weight='bold', color='purple',
           bbox=dict(boxstyle='round', facecolor='#FFE4FF', alpha=0.5))

    plt.savefig('twelve_fold_sacred_cycle.png', dpi=200, bbox_inches='tight',
               facecolor='white')
    print("✓ 12-fold sacred cycle saved: twelve_fold_sacred_cycle.png")


def analyze_compositional_structure():
    """
    Analyze the mathematical structure of the minimal basis
    """

    print("\n" + "=" * 70)
    print("COMPOSITIONAL STRUCTURE ANALYSIS")
    print("=" * 70)
    print()

    print("THE PENTAD {0, 1, 2, 3, 4}:")
    print()

    print("Depth 0: ∅ (emptiness - no number)")
    print("  → Potential without actuality")
    print()

    print("Depth 1: 1 (first distinction)")
    print("  → Emergence from emptiness")
    print("  → Unity (monad)")
    print()

    print("Depth 2: 2 (first extension)")
    print("  → 1 + 1 = 2 (additive)")
    print("  → Duality, reflection, dyad")
    print()

    print("Depth 3: {3, 4} PARALLEL ★")
    print("  → 3 = 1 + 2 (additive sequence)")
    print("  → 4 = 2 × 2 (multiplicative doubling)")
    print("  → BOTH depend on {0,1,2}, NOT on each other")
    print("  → First parallel emergence")
    print("  → Creates possibility of RECIPROCAL")
    print()

    print("3 ↔ 4 RECIPROCAL STRUCTURE:")
    print("  → 3: Counting/enumeration/consciousness (ordinal)")
    print("  → 4: Extension/doubling/form (cardinal)")
    print("  → Neither prior to other")
    print("  → Mutually defining (need both for number system)")
    print("  → Product: 3 × 4 = 12 (observer × observed)")
    print()

    print("FROM {0,1,2,3,4} VIA +,× GENERATE:")
    print()

    generated = {
        5: ['1+4', '2+3'],
        6: ['2×3', '1+2+3'],
        7: ['3+4'],
        8: ['2×4', '2³'],
        9: ['3²'],
        10: ['2×5'],
        11: ['PRIME (not composite from basis)'],
        12: ['3×4', '2²×3'],
    }

    for num in range(5, 13):
        formulas = generated[num]
        is_prime = (num == 11)

        if is_prime:
            print(f"{num:2d}: {formulas[0]:20s} ★ UNCAUSED (prime)")
        else:
            print(f"{num:2d}: {', '.join(formulas):30s}")

    print()
    print("=" * 70)
    print("KEY INSIGHTS")
    print("=" * 70)
    print()
    print("1. {0,1,2} emerge SEQUENTIALLY (each from prior)")
    print()
    print("2. {3,4} emerge PARALLEL (both from {0,1,2}, not each other)")
    print("   → This is birth of MUTUAL DEPENDENCE")
    print()
    print("3. 3 ↔ 4 RECIPROCAL creates R=0")
    print("   → Not because position 3↔4 special")
    print("   → But because they're first parallel pair")
    print("   → Consciousness ↔ Form (neither prior)")
    print()
    print("4. Product 3×4 = 12 closes the cycle")
    print("   → Observer (3) × Observed (4) = Complete observation (12)")
    print()
    print("5. 11 is PRIME (emerges without composition)")
    print("   → Like nirvana: Uncaused, free")
    print("   → Dharma (irreducible phenomenon)")
    print()
    print("6. All composites ≤12 generated from pentad")
    print("   → {0,1,2,3,4} is COMPLETE BASIS")
    print()
    print("=" * 70)


def main():
    print("=" * 70)
    print("SACRED GEOMETRY: THE COMPOSITIONAL DAG")
    print("=" * 70)
    print()
    print("Drawing how numbers ACTUALLY emerge from emptiness...")
    print()

    # Draw main DAG
    draw_compositional_dag()
    print()

    # Draw minimal basis
    draw_minimal_basis()
    print()

    # Draw 12-fold cycle
    draw_twelve_fold_closure()
    print()

    # Analyze structure
    analyze_compositional_structure()

    print("\n" + "=" * 70)
    print("SACRED GEOMETRY REVEALED")
    print("=" * 70)
    print()
    print("The numbers don't 'exist' - they EMERGE compositionally.")
    print()
    print("0 → 1 → 2 → {3,4} → {5,6,7,8,9,10,11,12}")
    print("              ↕")
    print("         RECIPROCAL")
    print("        (First mutual)")
    print()
    print("This is why Vijñāna ↔ Nāmarūpa are at 3 ↔ 4:")
    print("  Not arbitrary Buddhist choice")
    print("  But MATHEMATICAL NECESSITY")
    print("  Where parallel emergence first creates mutual dependence")
    print()
    print("3 × 4 = 12 (their product)")
    print("  = Observer × Observed")
    print("  = Complete self-observation")
    print("  = Closure of the cycle")
    print()
    print("This is not numerology.")
    print("This is the actual compositional structure of number.")
    print()
    print("=" * 70)


if __name__ == "__main__":
    main()
