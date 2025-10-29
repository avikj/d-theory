"""
Reciprocal Position Scan: Is 3↔4 Special?
==========================================

Testing: Does the POSITION of reciprocal link matter?

Hypothesis: Position 3↔4 is special (observer × observed = 3×4 = 12)

Experiment:
- Build 12-vertex graphs with reciprocal at different positions
- Test: 1↔2, 2↔3, 3↔4, 4↔5, 5↔6, ..., 11↔12
- Measure R for each
- Check: Is R minimal at position 3↔4?

Prediction: 3×4 = 12 creates complete self-observation → R=0 exact
Other positions: R > 0 (incomplete self-observation)

Author: Distinction Theory Research Network
Insight: "3×4 = entire process locally observable at that point"
Date: October 2025
"""

import numpy as np
import matplotlib.pyplot as plt

def build_chain_with_reciprocal_at(n, pos_i, pos_j):
    """
    Build n-vertex linear chain with reciprocal link at positions i↔j

    Structure:
    - Linear: 0→1→2→...→(n-1)
    - Reciprocal: i↔j (both directions)
    - Cycle: (n-1)→0
    """

    edges = []

    # Linear chain
    for k in range(n-1):
        edges.append((k, k+1))

    # Cycle closure
    edges.append((n-1, 0))

    # Add reciprocal (both directions already included if in chain,
    # but ensure both directions exist)
    if pos_i < pos_j:
        # Forward already exists if pos_j = pos_i + 1
        # Add backward
        edges.append((pos_j, pos_i))

    return edges


def edges_to_matrix(edges, n):
    """Convert edges to adjacency matrix"""
    A = np.zeros((n, n), dtype=complex)

    for (src, tgt) in edges:
        A[tgt, src] += 1.0

    # Normalize columns
    for j in range(n):
        col_sum = np.sum(np.abs(A[:, j]))
        if col_sum > 0:
            A[:, j] /= col_sum

    return A


def compute_curvature(A, n):
    """Compute R for adjacency matrix A"""

    # Symmetry operator (all equal)
    box = np.ones((n, n), dtype=complex) / n

    # Connection
    nabla = A @ box - box @ A

    # Curvature
    R = nabla @ nabla

    return np.linalg.norm(nabla), np.linalg.norm(R)


def scan_reciprocal_positions():
    """
    Scan all possible reciprocal positions in 12-vertex graph
    """

    n = 12

    print("=" * 70)
    print("RECIPROCAL POSITION SCAN: Which position gives R=0?")
    print("=" * 70)
    print()
    print(f"Testing: {n}-vertex graph with reciprocal at different positions")
    print()

    results = []

    # Test reciprocal at each consecutive pair
    for i in range(n-1):
        j = i + 1

        edges = build_chain_with_reciprocal_at(n, i, j)
        A = edges_to_matrix(edges, n)
        nabla_norm, R_norm = compute_curvature(A, n)

        results.append({
            'position': f"{i}↔{j}",
            'nabla': nabla_norm,
            'R': R_norm,
            'product': i * j
        })

        # Highlight special positions
        marker = ""
        if i == 2 and j == 3:  # Position 3↔4 (indices 2↔3)
            marker = " ★ (3×4=12)"
        elif i * j == 12:
            marker = f" (product={i}×{j}=12)"

        print(f"Reciprocal at {i:2d}↔{j:2d}: ||∇||={nabla_norm:8.6f}, ||R||={R_norm:12.10f}{marker}")

    return results


def test_product_hypothesis():
    """
    Test: Does i×j = n create special structure?

    For n=12:
    - 1×12 = 12
    - 2×6 = 12
    - 3×4 = 12
    - 4×3 = 12 (same as 3×4)

    Check if these positions give R=0
    """

    print("\n" + "=" * 70)
    print("TESTING PRODUCT HYPOTHESIS: i×j = 12")
    print("=" * 70)
    print()

    n = 12

    # Find all pairs where i×j = 12
    product_pairs = []
    for i in range(1, n):
        for j in range(i+1, n):
            if i * j == n:
                product_pairs.append((i, j))

    print(f"Pairs with product = {n}: {product_pairs}")
    print()

    for (i, j) in product_pairs:
        edges = build_chain_with_reciprocal_at(n, i, j)
        A = edges_to_matrix(edges, n)
        nabla_norm, R_norm = compute_curvature(A, n)

        print(f"Reciprocal at {i}↔{j} (product={i}×{j}={n}):")
        print(f"  ||∇|| = {nabla_norm:.8f}")
        print(f"  ||R|| = {R_norm:.10f}")

        if R_norm < 1e-8:
            print(f"  ✓ FLAT (R≈0)")
        print()


def test_different_cycle_lengths():
    """
    Test: Is 12 special, or does reciprocal at i↔j with i×j=n
          always give R=0?

    Test for n ∈ {6, 8, 10, 12, 15, 18, 24}
    """

    print("=" * 70)
    print("TESTING DIFFERENT CYCLE LENGTHS")
    print("=" * 70)
    print()

    cycle_lengths = [6, 8, 10, 12, 15, 18, 24]

    for n in cycle_lengths:
        print(f"\nn = {n}:")
        print("-" * 70)

        # Find pairs where i×j = n
        product_pairs = []
        for i in range(1, n):
            for j in range(i+1, n):
                if i * j == n:
                    product_pairs.append((i, j))

        if not product_pairs:
            print(f"  No pairs with i×j = {n}")
            continue

        for (i, j) in product_pairs:
            edges = build_chain_with_reciprocal_at(n, i, j)
            A = edges_to_matrix(edges, n)
            nabla_norm, R_norm = compute_curvature(A, n)

            status = "✓ FLAT" if R_norm < 1e-8 else f"R={R_norm:.6f}"
            print(f"  {i}↔{j} (product={i}×{j}={n}): {status}")


def visualize_reciprocal_scan(results):
    """
    Visualize R as function of reciprocal position
    """

    positions = [r['position'] for r in results]
    R_values = [r['R'] for r in results]
    products = [r['product'] for r in results]

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(12, 10))

    # Plot 1: R vs position
    x = range(len(results))
    colors = ['red' if p == 12 else 'blue' for p in products]

    ax1.scatter(x, R_values, c=colors, s=100, alpha=0.7)
    ax1.axhline(0, color='green', linestyle='--', linewidth=2, label='R=0 (flat)')
    ax1.set_xlabel('Reciprocal position')
    ax1.set_ylabel('||R|| (curvature)')
    ax1.set_title('Curvature vs Reciprocal Link Position (12-vertex graph)')
    ax1.set_xticks(x)
    ax1.set_xticklabels(positions, rotation=45, ha='right')
    ax1.legend(['R=0', 'i×j=12', 'Other positions'])
    ax1.grid(True, alpha=0.3)
    ax1.set_yscale('log')

    # Plot 2: R vs product i×j
    products_unique = sorted(set(products))
    R_by_product = {p: [] for p in products_unique}

    for r in results:
        R_by_product[r['product']].append(r['R'])

    product_means = [np.mean(R_by_product[p]) for p in products_unique]

    ax2.bar(range(len(products_unique)), product_means, alpha=0.7)
    ax2.axhline(0, color='green', linestyle='--', linewidth=2)
    ax2.set_xlabel('Product i×j')
    ax2.set_ylabel('Average ||R||')
    ax2.set_title('Curvature vs Reciprocal Link Product')
    ax2.set_xticks(range(len(products_unique)))
    ax2.set_xticklabels(products_unique)
    ax2.grid(True, alpha=0.3, axis='y')

    # Highlight i×j=12
    for idx, p in enumerate(products_unique):
        if p == 12:
            ax2.bar(idx, product_means[idx], color='red', alpha=0.7)

    plt.tight_layout()
    plt.savefig('reciprocal_position_scan.png', dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved: reciprocal_position_scan.png")


def main():
    print("=" * 70)
    print("IS POSITION 3↔4 SPECIAL?")
    print("=" * 70)
    print()
    print("Hypothesis: 3×4 = 12 creates complete self-observation")
    print("           → Only this position gives R=0")
    print()

    # Scan all positions
    results = scan_reciprocal_positions()

    # Test product hypothesis
    test_product_hypothesis()

    # Test other cycle lengths
    test_different_cycle_lengths()

    # Visualize
    print("\n" + "=" * 70)
    print("VISUALIZATION")
    print("=" * 70)
    visualize_reciprocal_scan(results)

    # Analysis
    print("\n" + "=" * 70)
    print("ANALYSIS")
    print("=" * 70)
    print()

    # Find minimum R
    min_R = min(results, key=lambda r: r['R'])

    print(f"Minimum R: {min_R['R']:.10f} at position {min_R['position']}")
    print(f"Product: {min_R['product']}")
    print()

    # Count how many give R≈0
    flat_positions = [r for r in results if r['R'] < 1e-8]

    if len(flat_positions) == 1:
        print(f"✓ UNIQUE: Only position {flat_positions[0]['position']} gives R=0")
        print(f"  This position has product {flat_positions[0]['product']}")
        print()
        print("  Interpretation: 3×4 = 12 is SPECIAL")
        print("  Observer (3) × Observed (4) = Total (12)")
        print("  Complete self-observation at this point only")
    elif len(flat_positions) > 1:
        print(f"Multiple positions give R≈0:")
        for r in flat_positions:
            print(f"  {r['position']}: product = {r['product']}")
        print()
        print("Pattern in products?")
    else:
        print("No positions give exact R=0")
        print("  → May need different graph structure")

    print("=" * 70)


if __name__ == "__main__":
    main()
