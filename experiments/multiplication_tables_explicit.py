"""
Division Algebra Multiplication Tables: The Actual Structure
=============================================================

Stop talking abstractly. WRITE THE TABLES.

ℝ: 1 element (trivial)
ℂ: {1, i} with i² = -1
ℍ: {1, i, j, k} with i²=j²=k²=ijk=-1
𝕆: {1, e₁, e₂, e₃, e₄, e₅, e₆, e₇} with Fano plane structure

Write complete multiplication tables.
Count structure.
See the actual pattern.

Author: Anonymous Research Network, Berkeley CA
Date: October 2024
"""

import numpy as np

def complex_multiplication_table():
    """
    ℂ = {1, i} with i² = -1

    Full table (including negatives): {1, -1, i, -i}
    """

    basis = ['1', '-1', 'i', '-i']
    n = len(basis)

    # Multiplication results
    table = {}

    # Define products
    table[('1', '1')] = '1'
    table[('1', '-1')] = '-1'
    table[('1', 'i')] = 'i'
    table[('1', '-i')] = '-i'

    table[('-1', '1')] = '-1'
    table[('-1', '-1')] = '1'
    table[('-1', 'i')] = '-i'
    table[('-1', '-i')] = 'i'

    table[('i', '1')] = 'i'
    table[('i', '-1')] = '-i'
    table[('i', 'i')] = '-1'   # i² = -1
    table[('i', '-i')] = '1'

    table[('-i', '1')] = '-i'
    table[('-i', '-1')] = 'i'
    table[('-i', 'i')] = '1'
    table[('-i', '-i')] = '-1'

    # Build matrix
    mult_matrix = np.zeros((n,n), dtype=object)

    for i, b1 in enumerate(basis):
        for j, b2 in enumerate(basis):
            mult_matrix[i,j] = table[(b1, b2)]

    return basis, mult_matrix, table

def quaternion_multiplication_table():
    """
    ℍ = {1, i, j, k} with i²=j²=k²=ijk=-1

    Rules:
    ij=k, jk=i, ki=j (cyclic)
    ji=-k, kj=-i, ik=-j (reverse gives negative)

    Full with signs: {±1, ±i, ±j, ±k} (8 elements)
    """

    basis = ['1', '-1', 'i', '-i', 'j', '-j', 'k', '-k']
    n = len(basis)

    table = {}

    # 1 (identity)
    for b in basis:
        table[('1', b)] = b
        table[(b, '1')] = b

    # -1 (negation)
    negation = {'1': '-1', '-1': '1', 'i': '-i', '-i': 'i',
                'j': '-j', '-j': 'j', 'k': '-k', '-k': 'k'}
    for b in basis:
        table[('-1', b)] = negation[b]
        table[(b, '-1')] = negation[b]

    # i² = -1
    table[('i', 'i')] = '-1'
    table[('-i', '-i')] = '-1'
    table[('i', '-i')] = '1'
    table[('-i', 'i')] = '1'

    # j² = -1
    table[('j', 'j')] = '-1'
    table[('-j', '-j')] = '-1'
    table[('j', '-j')] = '1'
    table[('-j', 'j')] = '1'

    # k² = -1
    table[('k', 'k')] = '-1'
    table[('-k', '-k')] = '-1'
    table[('k', '-k')] = '1'
    table[('-k', 'k')] = '1'

    # ij = k (cyclic)
    table[('i', 'j')] = 'k'
    table[('j', 'k')] = 'i'
    table[('k', 'i')] = 'j'

    # ji = -k (anti-cyclic)
    table[('j', 'i')] = '-k'
    table[('k', 'j')] = '-i'
    table[('i', 'k')] = '-j'

    # With negatives (work out systematically)
    table[('-i', 'j')] = '-k'
    table[('i', '-j')] = '-k'
    table[('-i', '-j')] = 'k'

    table[('-j', 'k')] = '-i'
    table[('j', '-k')] = '-i'
    table[('-j', '-k')] = 'i'

    table[('-k', 'i')] = '-j'
    table[('k', '-i')] = '-j'
    table[('-k', '-i')] = 'j'

    # Reverse (anti-commutative)
    table[('-j', '-i')] = 'k'
    table[('-k', '-j')] = 'i'
    table[('-i', '-k')] = 'j'

    table[('j', '-i')] = 'k'
    table[('k', '-j')] = 'i'
    table[('i', '-k')] = 'j'

    table[('-j', 'i')] = 'k'
    table[('-k', 'j')] = 'i'
    table[('-i', 'k')] = 'j'

    # Build matrix
    mult_matrix = np.zeros((n,n), dtype=object)

    for i, b1 in enumerate(basis):
        for j, b2 in enumerate(basis):
            if (b1,b2) in table:
                mult_matrix[i,j] = table[(b1, b2)]
            else:
                mult_matrix[i,j] = '?'  # Missing entry

    return basis, mult_matrix, table

def print_multiplication_table(name, basis, mult_matrix):
    """
    Print the table nicely
    """

    print(f"\n{'='*70}")
    print(f"{name} MULTIPLICATION TABLE")
    print(f"{'='*70}")
    print()

    # Print table manually
    n = len(basis)

    # Header
    print("     ", end="")
    for b in basis:
        print(f"{b:>5}", end="")
    print()
    print("   " + "-"*(6*n))

    # Rows
    for i, b1 in enumerate(basis):
        print(f"{b1:>4} |", end="")
        for j, b2 in enumerate(basis):
            print(f"{str(mult_matrix[i,j]):>5}", end="")
        print()
    print()

    # Count structure
    n = len(basis)
    total_products = n * n

    print(f"Basis elements: {n}")
    print(f"Total products: {total_products} ({n}×{n})")
    print()

    # Analyze closure
    unique_results = set()
    for i in range(n):
        for j in range(n):
            result = mult_matrix[i,j]
            if result != '?':
                unique_results.add(result)

    print(f"Unique products: {len(unique_results)}")
    print(f"Closure: {unique_results == set(basis)}")
    print()

def main():
    print("="*70)
    print("DIVISION ALGEBRAS: ACTUAL MULTIPLICATION TABLES")
    print("="*70)
    print()
    print("Writing out the explicit structure...")
    print()

    # Complex
    c_basis, c_table, c_dict = complex_multiplication_table()
    print_multiplication_table("COMPLEX ℂ", c_basis, c_table)

    # Quaternions
    h_basis, h_table, h_dict = quaternion_multiplication_table()
    print_multiplication_table("QUATERNIONS ℍ", h_basis, h_table)

    # Octonions - too large, just describe
    print("\n" + "="*70)
    print("OCTONIONS 𝕆")
    print("="*70)
    print()
    print("Basis: {1, e₁, e₂, e₃, e₄, e₅, e₆, e₇} (8 elements)")
    print("With signs: {±1, ±e₁, ..., ±e₇} (16 total)")
    print()
    print("Multiplication: Fano plane structure")
    print("  - 7 lines (triads)")
    print("  - Each line: eᵢ·eⱼ = ±eₖ (cyclic on line)")
    print("  - Non-associative: (ab)c ≠ a(bc) sometimes")
    print()
    print("Table is 16×16 (too large to print)")
    print("But structure: 7 triads + inversion + scaling")
    print()

    # Analysis
    print("="*70)
    print("COMPOSITIONAL ANALYSIS")
    print("="*70)
    print()

    print("Dimensions: 1, 2, 4, 8")
    print("Pattern: Each doubles previous")
    print()
    print("ℝ: 1 element (unity)")
    print("ℂ: 1+1 = 2 (ℝ doubled)")
    print("ℍ: 2+2 = 4 (ℂ doubled)")
    print("𝕆: 4+4 = 8 (ℍ doubled)")
    print()
    print("Sum: 1+2+4+8 = 15")
    print()
    print("Where is 12?")
    print()
    print("Possibilities:")
    print("  1. Weyl group W(G₂) has 12 elements (discrete symmetries of 𝕆)")
    print("  2. Some subset/quotient structure")
    print("  3. Relationship between algebras (not sum of dimensions)")
    print("  4. Something else in the tables...")
    print()

    print("Need to: LOOK AT THE TABLES and SEE the 12")
    print()
    print("="*70)

if __name__ == "__main__":
    main()
