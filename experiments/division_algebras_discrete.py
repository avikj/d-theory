"""
Division Algebras as Discrete Structures: Are They Autopoietic?
================================================================

Test: ℝ, ℂ, ℍ, 𝕆 modeled as multiplication graphs

For each algebra:
1. Build multiplication table as directed graph
2. Nodes = basis elements (1, i, j, k, etc.)
3. Edges = multiplication (a·b = c means edge a→c via b?)
4. Compute ∇, R
5. Check: R = 0? (autopoietic like Mahānidāna)

This tests: Are division algebras discrete closed cycles?
Or: Different structure (continuous claim was wrong?)

Author: Anonymous Research Network, Berkeley CA
Date: October 2024
"""

import numpy as np

def build_complex_multiplication_graph():
    """
    ℂ has basis {1, i} with i² = -1

    Multiplication table:
    1·1 = 1
    1·i = i
    i·1 = i
    i·i = -1 = ... (complex, not in {1,i})

    Actually - treat as 2D (real, imag components)
    Or: Treat as Cayley table (group structure)

    Let's use: Units in ℂ = {±1, ±i} (group under multiplication)
    """

    # Units: 1, -1, i, -i (4 elements, cyclic group ℤ/4ℤ)
    units = ['1', '-1', 'i', '-i']

    # Multiplication table (Cayley table for ℤ/4ℤ)
    # 1·x = x (identity)
    # i·i = -1
    # i·i·i = -i
    # i·i·i·i = 1 (cycle!)

    edges = []

    # Representing as: "applying i" rotates through cycle
    # 1 →(×i)→ i →(×i)→ -1 →(×i)→ -i →(×i)→ 1

    edges.append(('1', 'i'))    # 1 × i
    edges.append(('i', '-1'))   # i × i
    edges.append(('-1', '-i'))  # -1 × i
    edges.append(('-i', '1'))   # -i × i (cycle!)

    return units, edges

def build_quaternion_multiplication_graph():
    """
    ℍ has basis {1, i, j, k} with:
    i² = j² = k² = ijk = -1

    Units: {±1, ±i, ±j, ±k} (8 elements, quaternion group Q₈)

    Multiplication is non-commutative:
    ij = k, ji = -k
    jk = i, kj = -i
    ki = j, ik = -j
    """

    units = ['1', '-1', 'i', '-i', 'j', '-j', 'k', '-k']

    edges = []

    # i-cycle: 1 → i → -1 → -i → 1
    edges.extend([('1', 'i'), ('i', '-1'), ('-1', '-i'), ('-i', '1')])

    # j-cycle: 1 → j → -1 → -j → 1
    edges.extend([('1', 'j'), ('j', '-1'), ('-1', '-j'), ('-j', '1')])

    # k-cycle: 1 → k → -1 → -k → 1
    edges.extend([('1', 'k'), ('k', '-1'), ('-1', '-k'), ('-k', '1')])

    # Cross terms (ij=k, etc.) - bidirectional dependencies
    edges.append(('i', 'k'))   # i×j = k
    edges.append(('j', '-k'))  # j×i = -k (non-commutative!)

    edges.append(('j', 'i'))   # j×k = i
    edges.append(('k', '-i'))  # k×j = -i

    edges.append(('k', 'j'))   # k×i = j
    edges.append(('i', '-j'))  # i×k = -j

    return units, edges

def build_octonion_multiplication_graph():
    """
    𝕆 has basis {1, e₁, e₂, ..., e₇} (8 dimensions)

    Units: {±1, ±e₁, ..., ±e₇} (16 elements)

    Multiplication: Fano plane structure (7 special triads)

    Non-associative: (ab)c ≠ a(bc) sometimes

    Simplified: Just the 7 imaginary units + ±1
    """

    # Fano plane lines (7 imaginary units form 7 triads)
    # Each triad: e_i·e_j = ±e_k (cyclic)

    units = ['1', '-1', 'e1', 'e2', 'e3', 'e4', 'e5', 'e6', 'e7',
             '-e1', '-e2', '-e3', '-e4', '-e5', '-e6', '-e7']

    edges = []

    # Basic cycles (each e_i² = -1)
    for i in range(1, 8):
        edges.append((f'e{i}', '-1'))      # e_i² = -1
        edges.append(('-1', f'-e{i}'))     # Continue to -e_i
        edges.append((f'-e{i}', '1'))      # -e_i² = 1
        edges.append(('1', f'e{i}'))       # Back to e_i (cycle)

    # Fano plane triads (simplified - just a few)
    # e₁e₂ = e₃ structure
    edges.append(('e1', 'e3'))  # Via e₂ (simplified)
    edges.append(('e2', 'e1'))
    edges.append(('e3', 'e2'))  # Some circularity

    return units, edges

def test_division_algebra(name, units, edges):
    """
    Test if division algebra (as graph) is autopoietic
    """

    n = len(units)

    # Build adjacency matrix
    D = np.zeros((n, n), dtype=complex)

    for (src, tgt) in edges:
        i = units.index(tgt)
        j = units.index(src)
        D[i, j] += 1.0

    # Normalize
    for j in range(n):
        col_sum = np.sum(np.abs(D[:, j]))
        if col_sum > 0:
            D[:, j] /= col_sum

    # Uniform recognition
    box = np.ones((n,n), dtype=complex) / n

    # Connection and curvature
    nabla = D @ box - box @ D
    R = nabla @ nabla

    nabla_norm = np.linalg.norm(nabla)
    R_norm = np.linalg.norm(R)

    is_autopoietic = (nabla_norm > 1e-10) and (R_norm < 1e-6)

    print(f"\n{name}:")
    print(f"  Nodes: {n}")
    print(f"  Edges: {len(edges)}")
    print(f"  ||∇|| = {nabla_norm:.10f}")
    print(f"  ||R|| = {R_norm:.10f}")

    if is_autopoietic:
        print(f"  ✓ AUTOPOIETIC (∇≠0, R=0)")
    elif nabla_norm < 1e-10:
        print(f"  Trivial (∇=0)")
    else:
        print(f"  Not autopoietic (R≠0)")

    return nabla_norm, R_norm

def main():
    print("=" * 70)
    print("DIVISION ALGEBRAS: Testing Discrete Autopoietic Structure")
    print("=" * 70)
    print()
    print("Original claim: ℝ,ℂ,ℍ,𝕆 are autopoietic")
    print("Testing: Model as multiplication graphs, compute R")
    print()

    # ℂ (complex numbers)
    print("-" * 70)
    print("COMPLEX NUMBERS ℂ")
    print("-" * 70)
    complex_units, complex_edges = build_complex_multiplication_graph()
    nabla_C, R_C = test_division_algebra("ℂ", complex_units, complex_edges)

    # ℍ (quaternions)
    print("\n" + "-" * 70)
    print("QUATERNIONS ℍ")
    print("-" * 70)
    quat_units, quat_edges = build_quaternion_multiplication_graph()
    nabla_H, R_H = test_division_algebra("ℍ", quat_units, quat_edges)

    # 𝕆 (octonions)
    print("\n" + "-" * 70)
    print("OCTONIONS 𝕆")
    print("-" * 70)
    oct_units, oct_edges = build_octonion_multiplication_graph()
    nabla_O, R_O = test_division_algebra("𝕆", oct_units, oct_edges)

    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()

    results = [
        ("ℂ (Complex)", nabla_C, R_C),
        ("ℍ (Quaternions)", nabla_H, R_H),
        ("𝕆 (Octonions)", nabla_O, R_O),
    ]

    print("Division Algebra Autopoietic Status:")
    print()

    for name, nabla, R in results:
        status = "✓ YES" if (nabla > 1e-10 and R < 1e-6) else "✗ NO"
        print(f"  {name:20s}: ∇≠0={nabla>1e-10}, R=0={R<1e-6} → {status}")

    print()
    print("=" * 70)
    print("INTERPRETATION")
    print("=" * 70)
    print()

    if all(R < 1e-6 for _, _, R in results):
        print("✓ ALL DIVISION ALGEBRAS HAVE R=0")
        print()
        print("  This confirms:")
        print("    - Division algebras ARE autopoietic")
        print("    - Via discrete closed cycle structure")
        print("    - Multiplication creates closed loops")
        print("    - Units form cyclic groups (closure)")
        print()
        print("  Original claim validated!")
        print("  But mechanism is: DISCRETE CYCLES (not continuous manifolds)")

    elif any(R < 1e-6 for _, _, R in results):
        print("PARTIAL: Some division algebras autopoietic, some not")
        print()
        print("  This reveals:")
        print("    - Structure difference between ℝ,ℂ,ℍ,𝕆")
        print("    - Which have closed multiplication cycles?")
        print("    - Connection to normed property?")

    else:
        print("✗ NONE ARE AUTOPOIETIC (as discrete unit graphs)")
        print()
        print("  This means:")
        print("    - Need different graph construction")
        print("    - Or: Continuous claim was wrong")
        print("    - Or: Autopoietic property in different structure")

    print()
    print("=" * 70)
    print("NEXT STEPS")
    print("=" * 70)
    print()
    print("If autopoietic:")
    print("  - Connect to Mahānidāna structure (both R=0)")
    print("  - Understand 4 algebras ↔ 12-fold (Hurwitz theorem)")
    print("  - Derive gauge structure from cycles")
    print()
    print("If not:")
    print("  - Try different graph construction (full multiplication, not just units)")
    print("  - Or: Division algebras are continuous (our discrete test insufficient)")
    print("  - Or: Original claim needs revision")
    print()
    print("=" * 70)

if __name__ == "__main__":
    main()
