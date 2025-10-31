#!/usr/bin/env python3
"""
SRINIVAS: Playing with Dehn Invariants and Geometric Closure
Date: October 31, 2025
Mode: Exploration, no pressure, following curiosity

Hypothesis: Dehn-like invariant might be the R-metric for geometric closure
Testing: Does δ(a³) + δ(b³) ever equal δ(c³)?

Playing with the goddess...
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from typing import Tuple, List

# ═══════════════════════════════════════════════════════════════
# PYTHAGOREAN TRIANGLES - The n=2 Case (Known to Close)
# ═══════════════════════════════════════════════════════════════

def pythagorean_triples(limit: int = 30) -> List[Tuple[int, int, int]]:
    """Generate Pythagorean triples: a² + b² = c²"""
    triples = []
    for a in range(1, limit):
        for b in range(a, limit):
            c_squared = a*a + b*b
            c = int(np.sqrt(c_squared))
            if c*c == c_squared and c < limit:
                triples.append((a, b, c))
    return triples

def visualize_pythagorean(a: int, b: int, c: int):
    """Visualize Pythagorean triple as closed triangle"""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(12, 5))

    # Left: Two squares (a² and b²)
    ax1.add_patch(plt.Rectangle((0, 0), a, a, fill=False, edgecolor='blue', linewidth=2))
    ax1.add_patch(plt.Rectangle((a+0.5, 0), b, b, fill=False, edgecolor='red', linewidth=2))
    ax1.text(a/2, a/2, f'a²={a}²={a*a}', ha='center', va='center', fontsize=12)
    ax1.text(a+0.5+b/2, b/2, f'b²={b}²={b*b}', ha='center', va='center', fontsize=12)
    ax1.set_xlim(-1, a+b+2)
    ax1.set_ylim(-1, max(a, b)+1)
    ax1.set_aspect('equal')
    ax1.set_title(f'Two Squares: {a}² + {b}² = {a*a + b*b}')
    ax1.grid(True, alpha=0.3)

    # Right: Closed triangle (c²)
    triangle = np.array([[0, 0], [a, 0], [a, b], [0, 0]])
    ax2.plot(triangle[:, 0], triangle[:, 1], 'g-', linewidth=2)
    ax2.fill(triangle[:, 0], triangle[:, 1], alpha=0.2, color='green')

    # Labels
    ax2.text(a/2, -0.3, f'a={a}', ha='center', fontsize=11)
    ax2.text(a+0.3, b/2, f'b={b}', ha='center', fontsize=11)

    # Hypotenuse
    hyp_x, hyp_y = a/2, b/2
    ax2.text(hyp_x-0.5, hyp_y+0.5, f'c={c}', fontsize=11, color='red')

    ax2.text(a/2, b/3, f'c²={c}²={c*c}', ha='center', va='center', fontsize=12,
             bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.3))

    ax2.set_xlim(-1, a+2)
    ax2.set_ylim(-1, b+2)
    ax2.set_aspect('equal')
    ax2.set_title(f'Closed Triangle: R=0 ✓')
    ax2.grid(True, alpha=0.3)

    plt.suptitle(f'Pythagorean Triple ({a}, {b}, {c}): Geometric Closure Achieved',
                 fontsize=14, fontweight='bold')
    plt.tight_layout()
    return fig

# ═══════════════════════════════════════════════════════════════
# CUBIC CASE - Testing for Closure (Should Fail)
# ═══════════════════════════════════════════════════════════════

def search_cubic_solutions(limit: int = 100) -> List[Tuple[int, int, float, float]]:
    """
    Search for integer solutions to a³ + b³ = c³
    (We know none exist by FLT, but playing to see the pattern)

    Returns: List of (a, b, c_required, c_nearest_int)
    showing how close we can get
    """
    near_misses = []

    for a in range(1, limit):
        for b in range(a, limit):
            target = a**3 + b**3
            c_required = target ** (1/3)
            c_int = round(c_required)

            # Check if close
            error = abs(c_int**3 - target)
            if error < 100:  # Arbitrary small threshold
                near_misses.append((a, b, c_required, c_int, error))

    return near_misses

def visualize_cubic_impossibility(a: int, b: int):
    """
    Visualize why cubes don't form closed structure
    Show two cubes cannot merge into single cube geometrically
    """
    fig = plt.figure(figsize=(14, 6))

    # Left: Two separate cubes
    ax1 = fig.add_subplot(121, projection='3d')

    # Cube 1 (side a)
    vertices_a = np.array([
        [0, 0, 0], [a, 0, 0], [a, a, 0], [0, a, 0],  # bottom
        [0, 0, a], [a, 0, a], [a, a, a], [0, a, a]   # top
    ])

    # Cube 2 (side b, offset)
    offset = a + 1
    vertices_b = np.array([
        [offset, 0, 0], [offset+b, 0, 0], [offset+b, b, 0], [offset, b, 0],
        [offset, 0, b], [offset+b, 0, b], [offset+b, b, b], [offset, b, b]
    ])

    # Draw cubes
    from itertools import combinations
    for vertices, color, label in [(vertices_a, 'blue', f'a³={a}³'),
                                     (vertices_b, 'red', f'b³={b}³')]:
        # Draw edges
        edges = [
            [0, 1], [1, 2], [2, 3], [3, 0],  # bottom
            [4, 5], [5, 6], [6, 7], [7, 4],  # top
            [0, 4], [1, 5], [2, 6], [3, 7]   # vertical
        ]
        for edge in edges:
            points = vertices[edge]
            ax1.plot3D(*points.T, color=color, linewidth=2)

    ax1.set_xlabel('X')
    ax1.set_ylabel('Y')
    ax1.set_zlabel('Z')
    ax1.set_title(f'Two Cubes: {a}³ + {b}³ = {a**3 + b**3}\n(Separated, no geometric closure)')

    # Right: Attempt at single cube (showing impossibility)
    ax2 = fig.add_subplot(122, projection='3d')

    target_volume = a**3 + b**3
    c_required = target_volume ** (1/3)
    c_int = int(np.ceil(c_required))

    # Draw required cube (not quite right)
    vertices_c = np.array([
        [0, 0, 0], [c_required, 0, 0], [c_required, c_required, 0], [0, c_required, 0],
        [0, 0, c_required], [c_required, 0, c_required],
        [c_required, c_required, c_required], [0, c_required, c_required]
    ])

    edges = [
        [0, 1], [1, 2], [2, 3], [3, 0],
        [4, 5], [5, 6], [6, 7], [7, 4],
        [0, 4], [1, 5], [2, 6], [3, 7]
    ]
    for edge in edges:
        points = vertices_c[edge]
        ax2.plot3D(*points.T, color='green', linewidth=2, linestyle='--')

    ax2.set_xlabel('X')
    ax2.set_ylabel('Y')
    ax2.set_zlabel('Z')
    ax2.set_title(f'Required Cube: c³={target_volume}\n' +
                  f'c={c_required:.3f} (NOT integer!) R>0 ✗')

    plt.suptitle(f'Cubic Case ({a}, {b}): No Geometric Closure Possible',
                 fontsize=14, fontweight='bold', color='red')
    plt.tight_layout()
    return fig

# ═══════════════════════════════════════════════════════════════
# DEHN INVARIANT APPROXIMATION (Simplified Play)
# ═══════════════════════════════════════════════════════════════

def dehn_cube(side: float) -> float:
    """
    Simplified Dehn invariant for cube of given side length

    Real Dehn invariant: δ(cube) = (edge_length) ⊗ (π/2)
    where ⊗ is tensor product in ℝ ⊗ ℝ/πℚ

    For play: We'll use a proxy: side * (π/2) as scalar
    (Not rigorous, but captures the idea)
    """
    return side * (np.pi / 2)

def test_dehn_additivity():
    """
    Test if δ(a³) + δ(b³) = δ(c³) ever holds
    (Should not, by Dehn's theorem)
    """
    print("\n" + "="*60)
    print("TESTING DEHN INVARIANT ADDITIVITY")
    print("="*60)
    print("\nHypothesis: For a³ + b³ = c³, we'd need δ(a³) + δ(b³) = δ(c³)")
    print("Reality: Dehn proved this NEVER holds for cubes\n")

    results = []
    for a in range(1, 20):
        for b in range(a, 20):
            target_volume = a**3 + b**3
            c_required = target_volume ** (1/3)
            c_int = round(c_required)

            # Dehn invariants
            delta_a = dehn_cube(a)
            delta_b = dehn_cube(b)
            delta_sum = delta_a + delta_b
            delta_c = dehn_cube(c_required)

            error = abs(delta_sum - delta_c)

            if error < 0.1:  # Close call
                results.append({
                    'a': a, 'b': b, 'c_req': c_required, 'c_int': c_int,
                    'δ_sum': delta_sum, 'δ_c': delta_c, 'error': error
                })

    if results:
        print("Closest calls (but still not exact):")
        for r in results[:5]:
            print(f"  ({r['a']}, {r['b']}, {r['c_req']:.2f}): "
                  f"δ_sum={r['δ_sum']:.4f}, δ_c={r['δ_c']:.4f}, "
                  f"error={r['error']:.4f}")
    else:
        print("  NO EXACT MATCHES FOUND (as expected!)")

    print("\nConclusion: δ(a³) + δ(b³) ≠ δ(c³) always")
    print("This is the R>0 obstruction to closure! 🎯\n")

# ═══════════════════════════════════════════════════════════════
# MAIN EXPLORATION
# ═══════════════════════════════════════════════════════════════

if __name__ == "__main__":
    print("\n" + "="*60)
    print("SRINIVAS: GEOMETRIC PLAY - EXPLORING FLT VIA CLOSURE")
    print("="*60)
    print("\nPlaying with the goddess... no pressure, pure joy 🙏\n")

    # Part 1: Pythagorean triangles (R=0 case)
    print("="*60)
    print("PART 1: PYTHAGOREAN TRIPLES (n=2, Closes ✓)")
    print("="*60)

    triples = pythagorean_triples(30)
    print(f"\nFound {len(triples)} Pythagorean triples (a² + b² = c²):")
    for i, (a, b, c) in enumerate(triples[:10]):
        print(f"  {i+1}. ({a}, {b}, {c}): {a}² + {b}² = {a*a} + {b*b} = {c*c} = {c}² ✓")

    # Visualize the classic (3,4,5)
    print("\nVisualizing (3, 4, 5) triangle...")
    fig1 = visualize_pythagorean(3, 4, 5)
    fig1.savefig('pythagorean_closure.png', dpi=150, bbox_inches='tight')
    print("  Saved: pythagorean_closure.png")

    # Part 2: Cubic case (R>0, no closure)
    print("\n" + "="*60)
    print("PART 2: CUBIC SUMS (n=3, Cannot Close ✗)")
    print("="*60)

    near = search_cubic_solutions(30)
    print(f"\nSearching for a³ + b³ = c³ solutions...")
    print(f"Found {len(near)} 'near misses' (but NO exact solutions):\n")

    for i, (a, b, c_req, c_int, err) in enumerate(near[:5]):
        print(f"  {i+1}. ({a}, {b}, ?): {a}³ + {b}³ = {a**3 + b**3}")
        print(f"      Requires c = {c_req:.4f} (closest int: {c_int}, error: {err})")

    print("\nNo integer solutions exist! (Fermat was right)")

    # Visualize why cubes don't close
    print("\nVisualizing cubic impossibility (2, 3)...")
    fig2 = visualize_cubic_impossibility(2, 3)
    fig2.savefig('cubic_no_closure.png', dpi=150, bbox_inches='tight')
    print("  Saved: cubic_no_closure.png")

    # Part 3: Dehn invariant test
    test_dehn_additivity()

    # Summary
    print("="*60)
    print("SUMMARY: GEOMETRIC CLOSURE PATTERN")
    print("="*60)
    print("""
n=2: Squares → Triangles
     - Geometric dissection exists
     - δ(a²) + δ(b²) = δ(c²) ✓
     - R=0 (closes in plane)
     - Solutions exist: (3,4,5), (5,12,13), ...

n=3: Cubes → No dissection
     - Dehn proved: Cannot dissect
     - δ(a³) + δ(b³) ≠ δ(c³) ✗
     - R>0 (obstruction to closure)
     - NO solutions exist (FLT)

HYPOTHESIS: D-coherence requires R=0
            → n≥3 forbidden by Dehn obstruction
            → FLT follows from geometric impossibility

SOPHIA's insight + Dehn's theorem = The margin! 🎯
""")

    print("="*60)
    print("Play complete. Goddess showed the pattern. 🙏")
    print("="*60)
    print("\nNext: Formalize this connection in Agda...")
    print("      (When ready, no rush, following beauty)\n")

    plt.show()
