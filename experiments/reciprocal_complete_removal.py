"""
Complete Reciprocal Removal: Does R Increase?
==============================================

Testing: What if we REMOVE the reciprocal entirely?

Structure 1: Pure linear chain 0→1→2→3→4→...→11→0 (no 3↔4)
Structure 2: With reciprocal 3↔4
Structure 3: With MULTIPLE reciprocal links

Measure R for each.

Hypothesis: Removing reciprocal → R increases (matter emerges)

Author: Anonymous Research Network, Berkeley CA
Date: October 2024
"""

import numpy as np
import matplotlib.pyplot as plt

def build_pure_chain(n):
    """Pure directed cycle, no reciprocal"""
    edges = [(i, (i+1) % n) for i in range(n)]
    return edges

def build_with_reciprocal(n, recip_i, recip_j):
    """Chain with one reciprocal link"""
    edges = [(i, (i+1) % n) for i in range(n)]
    # Add backward edge
    edges.append((recip_j, recip_i))
    return edges

def build_with_multiple_reciprocals(n, pairs):
    """Chain with multiple reciprocal links"""
    edges = [(i, (i+1) % n) for i in range(n)]
    for (i, j) in pairs:
        edges.append((j, i))  # Add backward
    return edges

def edges_to_matrix(edges, n):
    A = np.zeros((n, n), dtype=complex)
    for edge in edges:
        if len(edge) == 2:
            src, tgt = edge
        else:
            src, tgt, _ = edge
        A[tgt, src] += 1.0

    for j in range(n):
        col_sum = np.sum(np.abs(A[:, j]))
        if col_sum > 0:
            A[:, j] /= col_sum
    return A

def compute_R(edges, n):
    A = edges_to_matrix(edges, n)
    box = np.ones((n, n), dtype=complex) / n
    nabla = A @ box - box @ A
    R = nabla @ nabla
    return np.linalg.norm(nabla), np.linalg.norm(R)

def main():
    print("=" * 70)
    print("RECIPROCAL REMOVAL: Testing Matter Emergence")
    print("=" * 70)
    print()

    n = 12

    # Test 1: No reciprocal (pure chain)
    edges1 = build_pure_chain(n)
    nabla1, R1 = compute_R(edges1, n)
    print(f"NO RECIPROCAL (pure cycle):")
    print(f"  Edges: {len(edges1)}")
    print(f"  ||∇|| = {nabla1:.8f}")
    print(f"  ||R|| = {R1:.10f}")
    print()

    # Test 2: One reciprocal at 3↔4
    edges2 = build_with_reciprocal(n, 2, 3)  # Indices 2,3 = positions 3,4
    nabla2, R2 = compute_R(edges2, n)
    print(f"ONE RECIPROCAL (3↔4):")
    print(f"  Edges: {len(edges2)}")
    print(f"  ||∇|| = {nabla2:.8f}")
    print(f"  ||R|| = {R2:.10f}")
    print()

    # Test 3: Multiple reciprocals
    pairs = [(2,3), (5,6), (8,9)]  # Three reciprocal links
    edges3 = build_with_multiple_reciprocals(n, pairs)
    nabla3, R3 = compute_R(edges3, n)
    print(f"MULTIPLE RECIPROCALS (3↔4, 6↔7, 9↔10):")
    print(f"  Edges: {len(edges3)}")
    print(f"  ||∇|| = {nabla3:.8f}")
    print(f"  ||R|| = {R3:.10f}")
    print()

    # Test 4: ALL pairs reciprocal (complete graph)
    pairs_all = [(i, i+1) for i in range(n-1)] + [(11, 0)]
    edges4 = build_with_multiple_reciprocals(n, pairs_all)
    nabla4, R4 = compute_R(edges4, n)
    print(f"ALL RECIPROCAL (complete bidirectional):")
    print(f"  Edges: {len(edges4)}")
    print(f"  ||∇|| = {nabla4:.8f}")
    print(f"  ||R|| = {R4:.10f}")
    print()

    # Comparison
    print("=" * 70)
    print("COMPARISON")
    print("=" * 70)
    print()

    results = [
        ("No reciprocal (pure chain)", R1),
        ("One reciprocal (3↔4)", R2),
        ("Three reciprocals", R3),
        ("All reciprocal", R4),
    ]

    for name, R in results:
        status = "✓ FLAT (R=0)" if R < 1e-8 else f"CURVED (R={R:.6f})"
        print(f"{name:30s}: {status}")

    print()
    print("=" * 70)
    print("REVELATION")
    print("=" * 70)
    print()

    if R1 < 1e-8:
        print("🤯 EVEN PURE CHAIN GIVES R=0!")
        print()
        print("This means:")
        print("  The cycle closure itself (12→0) creates flatness")
        print("  Reciprocal links maintain R=0 (don't create it)")
        print()
        print("Re-interpretation needed:")
        print("  What actually creates R≠0?")
        print("  If cycles give R=0, where does curvature come from?")
        print()
        print("Hypothesis: R≠0 requires BREAKING the cycle")
        print("  Open chain (no closure) → R≠0")
        print("  Closed loop → R=0 (always!)")
        print()
        print("Testing this hypothesis...")

        # Test: Open chain (no cycle closure)
        edges_open = [(i, i+1) for i in range(n-1)]  # No 11→0
        nabla_open, R_open = compute_R(edges_open, n)

        print()
        print(f"OPEN CHAIN (no cycle closure):")
        print(f"  ||R|| = {R_open:.10f}")
        print()

        if R_open > 1e-8:
            print("✓ OPEN CHAIN GIVES R≠0!")
            print()
            print("CONCLUSION:")
            print("  Closed loops → R=0 (autopoietic)")
            print("  Open chains → R≠0 (not autopoietic)")
            print()
            print("  Matter = breaking the cycle (birth without return)")
            print("  Vacuum = closed cycle (eternal return)")

    print()
    print("=" * 70)

if __name__ == "__main__":
    main()
