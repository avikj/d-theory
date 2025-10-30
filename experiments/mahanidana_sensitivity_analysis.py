#!/usr/bin/env python3
"""
Mahānidāna Sensitivity Analysis: Testing the `box` operator
=============================================================

This script investigates how sensitive the R=0 result is to the definition
of the necessity/stability operator, `box` (□).

We will test several alternative, plausible definitions for `box` to see if
the autopoietic condition (R=0, ∇≠0) still holds.
"""

import numpy as np

# --- Functions from the original script ---

def build_mahanidana_structure():
    nidanas = [
        'Avidyā', 'Saṃskāra', 'Vijñāna', 'Nāmarūpa', 'Ṣaḍāyatana',
        'Sparśa', 'Vedanā', 'Tṛṣṇā', 'Upādāna', 'Bhava', 'Jāti', 'Jarāmaraṇa'
    ]
    edges = []
    edges.append((nidanas[0], nidanas[1]))
    edges.append((nidanas[1], nidanas[2]))
    edges.append((nidanas[2], nidanas[3]))
    edges.append((nidanas[3], nidanas[2]))
    for i in range(3, 11):
        edges.append((nidanas[i], nidanas[i+1]))
    edges.append((nidanas[11], nidanas[0]))
    return nidanas, edges

def edges_to_matrix(edges, nodes):
    n = len(nodes)
    A = np.zeros((n, n), dtype=float)
    for (src, tgt) in edges:
        i = nodes.index(tgt)
        j = nodes.index(src)
        A[i, j] += 1.0
    for j in range(n):
        col_sum = np.sum(A[:, j])
        if col_sum > 0:
            A[:, j] /= col_sum
    return A

# --- Main Analysis ---

def test_alternative_boxes(D_hat, nidanas):
    """Tests different definitions for the box operator."""
    n = len(nidanas)
    results = {}

    # 1. Original Definition: Uniform Matrix (Śūnyatā)
    box_original = np.ones((n, n), dtype=float) / n
    nabla_orig = D_hat @ box_original - box_original @ D_hat
    R_orig = nabla_orig @ nabla_orig
    results['Original (Uniform)'] = (np.linalg.norm(nabla_orig), np.linalg.norm(R_orig))

    # 2. Alternative: Identity Matrix
    # Represents a □ that simply confirms the existing state.
    box_identity = np.identity(n, dtype=float)
    nabla_ident = D_hat @ box_identity - box_identity @ D_hat
    R_ident = nabla_ident @ nabla_ident
    results['Identity'] = (np.linalg.norm(nabla_ident), np.linalg.norm(R_ident))

    # 3. Alternative: Transpose of D_hat
    # Represents a □ that recognizes structure by reversing causal flow.
    box_transpose = D_hat.T
    nabla_trans = D_hat @ box_transpose - box_transpose @ D_hat
    R_trans = nabla_trans @ nabla_trans
    results['Transpose(D)'] = (np.linalg.norm(nabla_trans), np.linalg.norm(R_trans))

    # 4. Alternative: A random projection matrix
    # Tests if any projection works, or only the specific uniform one.
    np.random.seed(42) # for reproducibility
    rand_matrix = np.random.rand(n, n)
    box_random = rand_matrix / rand_matrix.sum(axis=1, keepdims=True)
    nabla_rand = D_hat @ box_random - box_random @ D_hat
    R_rand = nabla_rand @ nabla_rand
    results['Random'] = (np.linalg.norm(nabla_rand), np.linalg.norm(R_rand))
    
    # 5. Alternative: Zero Matrix
    # Represents a □ that annihilates all structure.
    box_zero = np.zeros((n, n), dtype=float)
    nabla_zero = D_hat @ box_zero - box_zero @ D_hat
    R_zero = nabla_zero @ nabla_zero
    results['Zero'] = (np.linalg.norm(nabla_zero), np.linalg.norm(R_zero))

    return results

def main():
    print("=" * 70)
    print("Mahānidāna Sensitivity Analysis: Probing the `box` operator")
    print("=" * 70)
    print("Hypothesis: The R=0 result is highly sensitive to the definition of □.")
    print("If only the uniform matrix (śūnyatā) gives R=0, the philosophical claim is strengthened.")
    print("---")

    # Get the pure Mahanidana structure
    nidanas, edges = build_mahanidana_structure()
    D_hat = edges_to_matrix(edges, nidanas)

    # Run the analysis
    results = test_alternative_boxes(D_hat, nidanas)

    # Print results
    print("Results of testing alternative definitions for the □ operator:")
    print("\n{:<20} | {:<15} | {:<15} | {}".format("□ Definition", "||∇|| (Nabla)", "||R|| (Curvature)", "Autopoietic?"))
    print("-"*80)

    for name, (nabla_norm, R_norm) in results.items():
        is_autopoietic = "YES" if nabla_norm > 1e-9 and R_norm < 1e-9 else "NO"
        print("{:<20} | {:<15.6f} | {:<15.6f} | {}".format(name, nabla_norm, R_norm, is_autopoietic))

    print("\n---")
    print("Conclusion:")
    if results['Original (Uniform)'][1] < 1e-9 and all(res[1] > 1e-9 for name, res in results.items() if name != 'Original (Uniform)'):
        print("The R=0 result is UNIQUE to the original 'uniform' definition of □.")
        print("This strongly supports the hypothesis that □ must represent a projection onto a uniform, undifferentiated state (śūnyatā) to achieve autopoiesis.")
    else:
        print("The R=0 result is NOT unique. Other definitions of □ also produce zero or near-zero curvature.")
        print("This suggests the R=0 result may be a more general property of the graph's structure, rather than the specific philosophical interpretation of □.")

if __name__ == "__main__":
    main()
