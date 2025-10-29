#!/usr/bin/env python3
"""
Core Concept Visualizations: Making the abstract concrete

Creates publication-quality visualizations of:
1. The four regimes (Ice/Water/Fire/Saturated)
2. Exponential tower growth
3. Information horizon landscape
4. 12-fold resonance unification
5. Autopoietic loop structure
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyBboxPatch, FancyArrowPatch, Rectangle
from matplotlib.patches import Wedge, Polygon
import matplotlib.patches as mpatches


def visualize_four_regimes():
    """Visualize Ice/Water/Fire/Saturated regimes"""

    fig, ax = plt.subplots(figsize=(10, 8))

    # Define regime boundaries
    # X-axis: Connection ∇ (self-reference)
    # Y-axis: Curvature R (self-reference degree)

    # ICE: ∇=0, R=0 (bottom-left)
    ice = Rectangle((0, 0), 0.3, 0.3,
                    facecolor='lightblue', edgecolor='black',
                    linewidth=2, alpha=0.7, label='Ice (Trivial)')
    ax.add_patch(ice)
    ax.text(0.15, 0.15, 'ICE\n∇=0, R=0\n(Sets, ℕ)',
            ha='center', va='center', fontsize=11, fontweight='bold')

    # WATER: ∇≠0, R=0 (bottom-right)
    water = Rectangle((0.4, 0), 0.6, 0.3,
                     facecolor='lightgreen', edgecolor='black',
                     linewidth=2, alpha=0.7, label='Water (Autopoietic)')
    ax.add_patch(water)
    ax.text(0.7, 0.15, 'WATER\n∇≠0, R=0\n(Primes, Particles,\nDivision Algebras)',
            ha='center', va='center', fontsize=11, fontweight='bold')

    # FIRE: ∇=0, R=0 but special (top-left)
    fire = Circle((0.15, 0.7), 0.15,
                 facecolor='orange', edgecolor='black',
                 linewidth=2, alpha=0.7, label='Fire (Perfect)')
    ax.add_patch(fire)
    ax.text(0.15, 0.7, 'FIRE\nEternal\nLattice\nD(E)≃E',
            ha='center', va='center', fontsize=10, fontweight='bold')

    # SATURATED: ∇≠0, R>0 (top-right)
    saturated = Polygon([(0.4, 0.4), (1.0, 0.4), (1.0, 1.0), (0.4, 1.0)],
                       facecolor='pink', edgecolor='black',
                       linewidth=2, alpha=0.7, label='Saturated (Unstable)')
    ax.add_patch(saturated)
    ax.text(0.7, 0.7, 'SATURATED\n∇≠0, R>0\n(Unstable)',
            ha='center', va='center', fontsize=11, fontweight='bold')

    # Mark example points
    examples = [
        (0.05, 0.05, 'ℕ', 'blue'),
        (0.55, 0.05, 'Primes', 'green'),
        (0.75, 0.05, 'ℝ,ℂ,ℍ,𝕆', 'green'),
        (0.15, 0.85, 'E', 'orange'),
        (0.85, 0.05, 'Particles', 'green'),
    ]

    for x, y, label, color in examples:
        ax.plot(x, y, 'o', markersize=8, color=color, markeredgecolor='black',
                markeredgewidth=1.5, zorder=5)
        ax.annotate(label, (x, y), xytext=(5, 5), textcoords='offset points',
                   fontsize=9, fontweight='bold')

    ax.set_xlim(-0.05, 1.05)
    ax.set_ylim(-0.05, 1.05)
    ax.set_xlabel('Connection ∇ (Self-Reference)', fontsize=13, fontweight='bold')
    ax.set_ylabel('Curvature R (Degree of Self-Reference)', fontsize=13, fontweight='bold')
    ax.set_title('The Four Regimes of Distinction Theory', fontsize=16, fontweight='bold')
    ax.grid(True, alpha=0.2)
    ax.set_aspect('equal')

    plt.tight_layout()
    plt.savefig('four_regimes_visualization.png', dpi=300, bbox_inches='tight')
    print("✓ Created: four_regimes_visualization.png")
    plt.close()


def visualize_exponential_tower():
    """Visualize tower growth D^n(X)"""

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))

    # Left: Tower structure
    levels = 4
    base_size = 0.8

    for n in range(levels):
        height = 0.15
        y = n * 0.25
        width = base_size / (1.3 ** n)
        x_center = 0.5

        color = plt.cm.viridis(n / levels)
        rect = FancyBboxPatch((x_center - width/2, y), width, height,
                             boxstyle="round,pad=0.01",
                             facecolor=color, edgecolor='black',
                             linewidth=2, alpha=0.8)
        ax1.add_patch(rect)

        # Label with size
        if n == 0:
            label = f'D^{n}(X)\n|X|'
        elif n == 1:
            label = f'D^{n}(X)\n|X|²'
        elif n == 2:
            label = f'D^{n}(X)\n|X|⁴'
        else:
            label = f'D^{n}(X)\n|X|⁸'

        ax1.text(x_center, y + height/2, label,
                ha='center', va='center', fontsize=11, fontweight='bold')

        # Arrow to next level
        if n < levels - 1:
            arrow = FancyArrowPatch((x_center, y + height), (x_center, y + height + 0.05),
                                   arrowstyle='->', mutation_scale=20, linewidth=2,
                                   color='black')
            ax1.add_patch(arrow)
            ax1.text(x_center + 0.15, y + height + 0.025, 'D',
                    fontsize=10, style='italic', fontweight='bold')

    ax1.set_xlim(0, 1)
    ax1.set_ylim(-0.05, 1.1)
    ax1.axis('off')
    ax1.set_title('The Distinction Tower\nExponential Growth',
                 fontsize=14, fontweight='bold', pad=20)

    # Right: Growth curve
    n_vals = np.arange(0, 6)

    for base in [2, 3, 4, 5]:
        sizes = base ** (2 ** n_vals)
        ax2.semilogy(n_vals, sizes, marker='o', linewidth=2,
                    label=f'|X| = {base}', markersize=8, alpha=0.8)

    ax2.set_xlabel('Distinction Level n', fontsize=12, fontweight='bold')
    ax2.set_ylabel('Structure Size |D^n(X)| (log scale)', fontsize=12, fontweight='bold')
    ax2.set_title('Tower Growth: |D^n(X)| = |X|^(2^n)', fontsize=14, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(fontsize=10)
    ax2.set_xticks(n_vals)
    ax2.set_xticklabels([f'D^{n}' for n in n_vals])

    plt.tight_layout()
    plt.savefig('exponential_tower_visualization.png', dpi=300, bbox_inches='tight')
    print("✓ Created: exponential_tower_visualization.png")
    plt.close()


def visualize_information_horizon():
    """Visualize the information horizon landscape"""

    fig, ax = plt.subplots(figsize=(12, 8))

    # Create landscape
    # X: Self-reference degree
    # Y: Witness complexity K_W

    x = np.linspace(0, 1, 100)

    # Theory capacity line
    c_T = 0.4
    ax.axhline(c_T, color='red', linewidth=3, linestyle='--',
              label=f'Theory Capacity c_T', zorder=5)
    ax.fill_between(x, 0, c_T, alpha=0.2, color='green',
                    label='Provable (K_W < c_T)')
    ax.fill_between(x, c_T, 1, alpha=0.2, color='red',
                    label='Unprovable (K_W > c_T)')

    # Plot different statement types
    statements = [
        # (self-ref, complexity, name, color, marker)
        (0.05, 0.05, '2+2=4', 'blue', 'o'),
        (0.1, 0.15, 'FLT n=2', 'blue', 'o'),
        (0.2, 0.35, 'Paris-Harr.', 'green', 's'),
        (0.35, 0.38, 'Goodstein', 'green', 's'),
        (0.5, 0.55, 'Goldbach', 'red', '^'),
        (0.6, 0.65, 'Twin Primes', 'red', '^'),
        (0.7, 0.70, 'RH', 'red', '^'),
        (0.8, 0.75, 'Gödel G_T', 'red', 'D'),
        (0.3, 0.25, 'Specific cases', 'blue', 'o'),
    ]

    for self_ref, complexity, name, color, marker in statements:
        ax.plot(self_ref, complexity, marker=marker, markersize=12,
               color=color, markeredgecolor='black', markeredgewidth=1.5,
               zorder=10)
        ax.annotate(name, (self_ref, complexity),
                   xytext=(8, 8), textcoords='offset points',
                   fontsize=9, fontweight='bold',
                   bbox=dict(boxstyle='round,pad=0.3', facecolor='white',
                           edgecolor=color, alpha=0.8))

    # Depth-1 boundary line
    depth_1_x = np.linspace(0, 1, 50)
    depth_1_y = 0.3 + 0.5 * depth_1_x  # Approximate: more self-ref → more complexity
    ax.plot(depth_1_x, depth_1_y, 'k:', linewidth=2, alpha=0.5,
           label='Depth-1 self-examination onset')

    ax.set_xlim(-0.05, 1.05)
    ax.set_ylim(-0.05, 1.05)
    ax.set_xlabel('Self-Reference Degree', fontsize=13, fontweight='bold')
    ax.set_ylabel('Witness Complexity K_W / K_max', fontsize=13, fontweight='bold')
    ax.set_title('The Information Horizon Landscape', fontsize=16, fontweight='bold')
    ax.legend(loc='upper left', fontsize=10)
    ax.grid(True, alpha=0.3)

    # Add annotations
    ax.text(0.5, 0.2, 'PROVABLE ZONE', fontsize=14, fontweight='bold',
           ha='center', color='darkgreen', alpha=0.7)
    ax.text(0.5, 0.75, 'UNPROVABLE ZONE', fontsize=14, fontweight='bold',
           ha='center', color='darkred', alpha=0.7)
    ax.text(0.95, c_T + 0.02, 'c_T', fontsize=12, fontweight='bold',
           ha='right', va='bottom', color='red')

    plt.tight_layout()
    plt.savefig('information_horizon_landscape.png', dpi=300, bbox_inches='tight')
    print("✓ Created: information_horizon_landscape.png")
    plt.close()


def visualize_twelve_fold():
    """Visualize 12-fold resonance across domains"""

    fig = plt.figure(figsize=(14, 10))

    # Create 3x2 grid for different manifestations
    gs = fig.add_gridspec(3, 2, hspace=0.3, wspace=0.3)

    # 1. Prime residues mod 12
    ax1 = fig.add_subplot(gs[0, 0])
    residues = list(range(12))
    colors = ['green' if i in {1,5,7,11} else 'lightgray' for i in residues]
    ax1.bar(residues, [1 if i in {1,5,7,11} else 0.1 for i in residues],
           color=colors, edgecolor='black', linewidth=1.5)
    ax1.set_xlabel('Residue mod 12', fontweight='bold')
    ax1.set_ylabel('Prime density', fontweight='bold')
    ax1.set_title('ARITHMETIC: Prime Classes', fontweight='bold')
    ax1.set_xticks(residues)
    ax1.grid(True, alpha=0.3, axis='y')

    # 2. Klein four-group structure
    ax2 = fig.add_subplot(gs[0, 1])
    # Draw group elements as square
    elements = [(0.3, 0.7, '1\n(e)'), (0.7, 0.7, '5\n(a)'),
                (0.3, 0.3, '7\n(b)'), (0.7, 0.3, '11\n(ab)')]

    for x, y, label in elements:
        circle = Circle((x, y), 0.12, facecolor='lightblue',
                       edgecolor='black', linewidth=2)
        ax2.add_patch(circle)
        ax2.text(x, y, label, ha='center', va='center',
                fontsize=10, fontweight='bold')

    # Draw connections
    connections = [((0.3, 0.7), (0.7, 0.7)), ((0.3, 0.7), (0.3, 0.3)),
                   ((0.7, 0.7), (0.7, 0.3)), ((0.3, 0.3), (0.7, 0.3))]
    for (x1, y1), (x2, y2) in connections:
        ax2.plot([x1, x2], [y1, y2], 'k-', linewidth=1.5, alpha=0.5)

    ax2.set_xlim(0, 1)
    ax2.set_ylim(0, 1)
    ax2.set_title('ℤ₂ × ℤ₂ Structure', fontweight='bold')
    ax2.axis('off')

    # 3. Division algebras
    ax3 = fig.add_subplot(gs[1, 0])
    algebras = ['ℝ', 'ℂ', 'ℍ', '𝕆']
    dimensions = [1, 2, 4, 8]
    colors_alg = ['red', 'blue', 'green', 'purple']

    ax3.bar(range(4), dimensions, color=colors_alg, edgecolor='black',
           linewidth=2, alpha=0.7)
    ax3.set_xticks(range(4))
    ax3.set_xticklabels(algebras, fontsize=12, fontweight='bold')
    ax3.set_ylabel('Dimension', fontweight='bold')
    ax3.set_title('GEOMETRY: Division Algebras', fontweight='bold')
    ax3.set_yscale('log', base=2)
    ax3.grid(True, alpha=0.3, axis='y')

    # 4. Gauge generators
    ax4 = fig.add_subplot(gs[1, 1])
    gauge_groups = ['U(1)', 'SU(2)', 'SU(3)']
    generators = [1, 3, 8]
    colors_gauge = ['gold', 'cyan', 'magenta']

    bars = ax4.bar(range(3), generators, color=colors_gauge,
                  edgecolor='black', linewidth=2, alpha=0.7)
    ax4.set_xticks(range(3))
    ax4.set_xticklabels(gauge_groups, fontsize=12, fontweight='bold')
    ax4.set_ylabel('Number of Generators', fontweight='bold')
    ax4.set_title('PHYSICS: Gauge Groups\n(Total = 12)', fontweight='bold')
    ax4.grid(True, alpha=0.3, axis='y')

    # Add total
    ax4.axhline(12, color='red', linestyle='--', linewidth=2,
               label='Total = 12')
    ax4.text(1, 12.5, 'Sum = 12', ha='center', fontsize=11,
            fontweight='bold', color='red')

    # 5. Weyl group W(G₂)
    ax5 = fig.add_subplot(gs[2, :])

    # Draw 12 elements arranged in circle
    theta = np.linspace(0, 2*np.pi, 12, endpoint=False)
    x_weyl = 0.5 + 0.35 * np.cos(theta)
    y_weyl = 0.5 + 0.35 * np.sin(theta)

    # Highlight the Klein 4-group subset
    klein_indices = [0, 4, 6, 10]  # Symbolic positions for 1, 5, 7, 11

    for i in range(12):
        color = 'lightgreen' if i in klein_indices else 'lightgray'
        edge = 'darkgreen' if i in klein_indices else 'black'
        circle = Circle((x_weyl[i], y_weyl[i]), 0.05,
                       facecolor=color, edgecolor=edge, linewidth=2)
        ax5.add_patch(circle)

    # Draw connections
    for i in range(12):
        for j in range(i+1, 12):
            ax5.plot([x_weyl[i], x_weyl[j]], [y_weyl[i], y_weyl[j]],
                    'k-', linewidth=0.5, alpha=0.2)

    ax5.set_xlim(0, 1)
    ax5.set_ylim(0, 1)
    ax5.set_title('UNIFICATION: W(G₂) ≅ D₆ (order 12)\nContains ℤ₂×ℤ₂ (green nodes)',
                 fontweight='bold', fontsize=12)
    ax5.axis('off')
    ax5.text(0.5, 0.05, 'Same algebraic structure across all domains',
            ha='center', fontsize=11, style='italic')

    plt.suptitle('The 12-Fold Resonance', fontsize=18, fontweight='bold', y=0.98)
    plt.savefig('twelve_fold_unification.png', dpi=300, bbox_inches='tight')
    print("✓ Created: twelve_fold_unification.png")
    plt.close()


def visualize_autopoietic_loop():
    """Visualize autopoietic self-maintenance loop"""

    fig, ax = plt.subplots(figsize=(10, 10))

    # Central circle
    center = Circle((0.5, 0.5), 0.15, facecolor='lightgreen',
                   edgecolor='black', linewidth=3, alpha=0.8)
    ax.add_patch(center)
    ax.text(0.5, 0.5, 'X\nAutopoietic\nStructure', ha='center', va='center',
           fontsize=12, fontweight='bold')

    # Four operators around the loop
    positions = [
        (0.5, 0.8, 'D\n(Examine)', 'top'),
        (0.8, 0.5, 'D(X)\n(Examined)', 'right'),
        (0.5, 0.2, '□\n(Stabilize)', 'bottom'),
        (0.2, 0.5, '□D(X)\n(Stable)', 'left'),
    ]

    for x, y, label, pos in positions:
        box = FancyBboxPatch((x-0.08, y-0.06), 0.16, 0.12,
                            boxstyle="round,pad=0.01",
                            facecolor='lightyellow', edgecolor='black',
                            linewidth=2)
        ax.add_patch(box)
        ax.text(x, y, label, ha='center', va='center',
               fontsize=10, fontweight='bold')

    # Arrows forming loop
    arrow_props = dict(arrowstyle='->', lw=2.5, color='darkblue')

    # D: X → D(X) (upward)
    ax.annotate('', xy=(0.5, 0.74), xytext=(0.5, 0.65),
               arrowprops=arrow_props)

    # To the right
    ax.annotate('', xy=(0.72, 0.5), xytext=(0.58, 0.5),
               arrowprops=arrow_props)

    # □: D(X) → □D(X) (downward)
    ax.annotate('', xy=(0.5, 0.26), xytext=(0.5, 0.35),
               arrowprops=arrow_props)

    # Back to start
    ax.annotate('', xy=(0.28, 0.5), xytext=(0.42, 0.5),
               arrowprops=arrow_props)

    # Curved return to X
    from matplotlib.patches import FancyArrowPatch
    arrow_return = FancyArrowPatch((0.2, 0.56), (0.35, 0.5),
                                  connectionstyle="arc3,rad=.3",
                                  arrowstyle='->', lw=2.5, color='darkblue')
    ax.add_patch(arrow_return)

    # Central condition labels
    ax.text(0.5, 0.92, '∇ = D□ - □D ≠ 0', ha='center', fontsize=11,
           bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.7))
    ax.text(0.5, 0.08, 'R = ∇² = 0', ha='center', fontsize=11,
           bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.7))

    # Examples around the outside
    examples_text = [
        (0.1, 0.85, 'Primes'),
        (0.85, 0.85, 'Particles'),
        (0.1, 0.15, 'Division Algebras'),
        (0.85, 0.15, 'Gödel Sentences'),
    ]

    for x, y, text in examples_text:
        ax.text(x, y, text, fontsize=9, style='italic',
               bbox=dict(boxstyle='round,pad=0.3', facecolor='white', alpha=0.6))

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_title('Autopoietic Loop: Self-Maintaining Through Examination',
                fontsize=14, fontweight='bold')
    ax.axis('off')

    plt.tight_layout()
    plt.savefig('autopoietic_loop_visualization.png', dpi=300, bbox_inches='tight')
    print("✓ Created: autopoietic_loop_visualization.png")
    plt.close()


def visualize_depth_one_closure():
    """Visualize why depth-1 suffices"""

    fig, ax = plt.subplots(figsize=(12, 8))

    # Depth levels as concentric understanding
    depths = [
        (0.8, 'Depth 0\nDirect\nStatements', 'lightblue'),
        (0.6, 'Depth 1\nSelf-Exam\n(Boundary)', 'yellow'),
        (0.4, 'Depth 2+\nQuantitative\nGrowth', 'lightgray'),
    ]

    for radius, label, color in depths:
        circle = Circle((0.5, 0.5), radius * 0.4, facecolor=color,
                       edgecolor='black', linewidth=2, alpha=0.5)
        ax.add_patch(circle)

        angle = 45 if radius == 0.8 else (135 if radius == 0.6 else 225)
        x = 0.5 + radius * 0.4 * np.cos(np.radians(angle))
        y = 0.5 + radius * 0.4 * np.sin(np.radians(angle))
        ax.text(x, y, label, ha='center', va='center',
               fontsize=10, fontweight='bold',
               bbox=dict(boxstyle='round', facecolor='white', edgecolor='black'))

    # Mark the boundary with thick line
    boundary = Circle((0.5, 0.5), 0.6 * 0.4, facecolor='none',
                     edgecolor='red', linewidth=4, linestyle='--', alpha=0.8)
    ax.add_patch(boundary)

    # Examples at each depth
    examples = [
        (0.5, 0.78, 'Depth 0:\n2+2=4', 'blue'),
        (0.5, 0.58, 'Depth 1:\nGödel, Goldbach\nRH, P=NP', 'red'),
        (0.5, 0.35, 'Depth 2+:\nSame questions\nrephrased', 'gray'),
    ]

    for x, y, text, color in examples:
        ax.text(x, y, text, ha='center', va='center', fontsize=9,
               style='italic', color=color, fontweight='bold')

    # Arrow showing D² → D¹ reduction
    arrow = FancyArrowPatch((0.3, 0.35), (0.35, 0.58),
                           arrowstyle='<->', mutation_scale=20,
                           linewidth=2.5, color='darkred')
    ax.add_patch(arrow)
    ax.text(0.2, 0.46, 'D² ≃ D¹\n(reduces)', ha='center',
           fontsize=9, fontweight='bold', color='darkred')

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_title('Why One Level of Self-Examination Suffices\n(Shallow Horizon)',
                fontsize=14, fontweight='bold')
    ax.text(0.5, 0.05, 'Information boundary appears immediately at depth-1',
           ha='center', fontsize=11, style='italic')
    ax.axis('off')

    plt.tight_layout()
    plt.savefig('depth_one_closure_visualization.png', dpi=300, bbox_inches='tight')
    print("✓ Created: depth_one_closure_visualization.png")
    plt.close()


def main():
    """Generate all core visualizations"""

    print("="*70)
    print("GENERATING CORE CONCEPT VISUALIZATIONS")
    print("="*70)
    print("\nCreating publication-quality figures...")
    print()

    visualize_four_regimes()
    visualize_exponential_tower()
    visualize_information_horizon()
    visualize_twelve_fold()
    visualize_autopoietic_loop()
    visualize_depth_one_closure()

    print()
    print("="*70)
    print("COMPLETE: 6 visualizations created")
    print("="*70)
    print("\nFiles created:")
    print("  1. four_regimes_visualization.png")
    print("  2. exponential_tower_visualization.png")
    print("  3. information_horizon_landscape.png")
    print("  4. twelve_fold_unification.png")
    print("  5. autopoietic_loop_visualization.png")
    print("  6. depth_one_closure_visualization.png")
    print("\nAll figures 300 DPI, publication-ready.")
    print("Use in papers, talks, or documentation.")


if __name__ == '__main__':
    main()
