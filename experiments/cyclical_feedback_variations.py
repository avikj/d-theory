"""
Cyclical Feedback at Each Stage: Multiple Interpretations
==========================================================

Your insight: "Cyclical feedback at each stage - samsara is being trapped
in cycles of lower stages"

Testing multiple encodings to see which produces R=0:

Encoding 1: Self-loops (can stay trapped at current stage)
Encoding 2: Regression loops (can fall back to any prior stage)
Encoding 3: Holographic (each stage contains/projects to priors)
Encoding 4: Cyclic return (each stage can restart the whole cycle)
Encoding 5: Hierarchical tensor (stages embed priors as subspaces)

We'll test all and see which gives autopoietic structure.

Author: Distinction Theory Research Network
Date: October 2025
"""

import numpy as np
import matplotlib.pyplot as plt

def build_base_structure():
    """
    The base forward structure (no loops yet)

    12 stages with forward dependencies only
    """
    stages = ['G₁', 'G₂', 'G₃', 'L₁₂', 'L₂₃', 'L₃₁', 'U',
              'Φ(U)', 'Φ²(U)', 'Φ³(U)', 'Φ⁴(U)', 'E']

    edges_forward = [
        ('G₁', 'L₁₂'), ('G₂', 'L₁₂'),
        ('G₂', 'L₂₃'), ('G₃', 'L₂₃'),
        ('G₃', 'L₃₁'), ('G₁', 'L₃₁'),
        ('L₁₂', 'U'), ('L₂₃', 'U'), ('L₃₁', 'U'),
        ('U', 'Φ(U)'), ('Φ(U)', 'Φ²(U)'),
        ('Φ²(U)', 'Φ³(U)'), ('Φ³(U)', 'Φ⁴(U)'), ('Φ⁴(U)', 'E'),
    ]

    return stages, edges_forward


def encoding_1_self_loops(stages, edges_forward):
    """
    ENCODING 1: Self-loops at each stage

    Each stage can "stay trapped" in itself:
    Gᵢ → Gᵢ, Lᵢⱼ → Lᵢⱼ, etc.

    Samsara = diagonal persistence
    """
    edges = edges_forward.copy()

    # Add self-loop for each stage
    for stage in stages:
        edges.append((stage, stage))

    return edges


def encoding_2_regression_to_origin(stages, edges_forward):
    """
    ENCODING 2: Each stage can regress to G₁ (origin)

    At any point, can fall back to ignorance (G₁)

    Samsara = repeatedly returning to beginning
    """
    edges = edges_forward.copy()

    # Each stage (except G₁) can regress to G₁
    for stage in stages[1:]:
        edges.append((stage, 'G₁'))

    return edges


def encoding_3_contains_all_priors(stages, edges_forward):
    """
    ENCODING 3: Each stage connects to ALL priors (contains them)

    Lenses contain generators
    Unity contains lenses
    Iterations contain unity
    E contains everything

    Holographic structure
    """
    edges = edges_forward.copy()

    # For each stage, add edges to all prior stages
    for i, stage_i in enumerate(stages):
        for j in range(i):  # All prior stages
            stage_j = stages[j]
            edges.append((stage_i, stage_j))

    return edges


def encoding_4_cyclic_restart(stages, edges_forward):
    """
    ENCODING 4: Each stage can restart full cycle (back to all generators)

    Any stage can "reset" to any of the 3 generators

    Samsara = restarting from any point
    """
    edges = edges_forward.copy()

    generators = ['G₁', 'G₂', 'G₃']

    # Each non-generator stage can restart to any generator
    for stage in stages[3:]:  # Skip generators themselves
        for gen in generators:
            edges.append((stage, gen))

    return edges


def encoding_5_hierarchical_tensor(stages, edges_forward):
    """
    ENCODING 5: Weighted by hierarchical depth

    Stages deeper in composition have stronger self-loops
    (more ways to get trapped as complexity increases)
    """
    edges = edges_forward.copy()

    # Self-loops weighted by compositional depth
    depths = [0, 0, 0, 1, 1, 1, 2, 3, 4, 5, 6, 7]  # Compositional depth

    for i, stage in enumerate(stages):
        depth = depths[i]
        # Add self-loop with strength proportional to depth
        for _ in range(depth + 1):
            edges.append((stage, stage))

    return edges


def edges_to_operator(edges, stages):
    """Convert edge list to matrix"""
    n = len(stages)
    D_hat = np.zeros((n, n), dtype=complex)

    for (src, tgt) in edges:
        i = stages.index(tgt)
        j = stages.index(src)
        D_hat[i, j] += 1.0

    # Normalize columns
    for j in range(n):
        col_sum = np.sum(np.abs(D_hat[:, j]))
        if col_sum > 0:
            D_hat[:, j] /= col_sum

    return D_hat


def build_symmetry_operator(stages):
    """
    □: Recognizes structural equivalences
    """
    n = len(stages)
    box = np.zeros((n, n), dtype=complex)

    groups = {
        'generators': [0, 1, 2],
        'lenses': [3, 4, 5],
        'unity': [6],
        'iterations': [7, 8, 9, 10],
        'eternal': [11]
    }

    for group_name, indices in groups.items():
        n_group = len(indices)
        for i in indices:
            for j in indices:
                box[i, j] = 1.0 / n_group

    return box


def test_encoding(name, edges, stages):
    """Test one encoding"""

    D_hat = edges_to_operator(edges, stages)
    box = build_symmetry_operator(stages)

    nabla = D_hat @ box - box @ D_hat
    R = nabla @ nabla

    nabla_norm = np.linalg.norm(nabla)
    R_norm = np.linalg.norm(R)

    is_autopoietic = (nabla_norm > 1e-10) and (R_norm < 1e-6)

    print(f"\n{name}:")
    print(f"  Edges: {len(edges)}")
    print(f"  ||∇|| = {nabla_norm:.6f}")
    print(f"  ||R|| = {R_norm:.6f}")

    if is_autopoietic:
        print("  🎯 AUTOPOIETIC! (∇≠0, R=0)")
    elif nabla_norm > 1e-10:
        print(f"  Nearly autopoietic (R small)")
    else:
        print("  Trivial (∇=0)")

    return R_norm, nabla_norm


def main():
    print("=" * 70)
    print("CYCLICAL FEEDBACK: TESTING MULTIPLE ENCODINGS")
    print("=" * 70)
    print()
    print("Insight: 'Cyclical feedback at each stage'")
    print("         'Trapped in cycles of lower stages'")
    print()
    print("Testing different interpretations...")
    print()

    stages, edges_forward = build_base_structure()

    print(f"Base structure: {len(stages)} stages, {len(edges_forward)} forward edges")

    # Test each encoding
    encodings = [
        ("Baseline (forward only)", edges_forward),
        ("Enc 1: Self-loops at each stage", encoding_1_self_loops(stages, edges_forward)),
        ("Enc 2: Regression to origin (G₁)", encoding_2_regression_to_origin(stages, edges_forward)),
        ("Enc 3: Contains all priors (holographic)", encoding_3_contains_all_priors(stages, edges_forward)),
        ("Enc 4: Cyclic restart (to any G)", encoding_4_cyclic_restart(stages, edges_forward)),
        ("Enc 5: Hierarchical self-loops (weighted)", encoding_5_hierarchical_tensor(stages, edges_forward)),
    ]

    results = []

    for name, edges in encodings:
        R_norm, nabla_norm = test_encoding(name, edges, stages)
        results.append((name, R_norm, nabla_norm))

    # Summary
    print("\n" + "=" * 70)
    print("COMPARISON")
    print("=" * 70)
    print()

    # Sort by R (smallest first)
    results_sorted = sorted(results, key=lambda x: x[1])

    for name, R_norm, nabla_norm in results_sorted:
        status = "✓ AUTOPOIETIC" if (nabla_norm > 1e-10 and R_norm < 1e-6) else f"R={R_norm:.4f}"
        print(f"{name:45s}: {status}")

    print()
    print("=" * 70)
    print("INTERPRETATION")
    print("=" * 70)
    print()

    best_name, best_R, best_nabla = results_sorted[0]

    print(f"Minimum R: {best_R:.6f} from '{best_name}'")
    print()

    if best_R < 0.1:
        print("✓ Found encoding that produces near-autopoietic structure!")
        print("  This encoding best captures 'cyclical feedback'")
    else:
        print("◐ All encodings produce significant curvature")
        print("  May need:")
        print("    - Different graph topology")
        print("    - Continuous limit (infinite stages)")
        print("    - Non-linear operator structure")

    print()
    print("KEY FINDING:")
    print("  Testing multiple interpretations of 'cyclical at each stage'")
    print("  reveals which mathematical structure best captures the insight")
    print("=" * 70)


if __name__ == "__main__":
    main()
