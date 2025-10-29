"""
Mahānidāna Sutta Structure: The Buddha's Actual Teaching
=========================================================

From DN 15 (Mahānidāna Sutta), the precise causal structure:

LINEAR CHAIN:
1. Avidyā (ignorance) → 2. Saṃskāra (formations) → 3. Vijñāna (consciousness)

RECIPROCAL LOOP:
3. Vijñāna (consciousness) ⟷ 4. Nāmarūpa (name-form)
"Like two reeds leaning on each other"

CONTINUATION:
4. Nāmarūpa → 5. Ṣaḍāyatana (six sense bases) → 6. Sparśa (contact)
→ 7. Vedanā (feeling) → 8. Tṛṣṇā (craving) → 9. Upādāna (clinging)
→ 10. Bhava (becoming) → 11. Jāti (birth) → 12. Jarāmaraṇa (aging/death)

CYCLE CLOSURE:
12. Jarāmaraṇa → 1. Avidyā (death returns to ignorance)

KEY INSIGHT: The reciprocal conditioning between 3↔4 creates
a STABLE LOOP (two reeds) - this might be where R=0 emerges!

Author: Distinction Theory Research Network
Source: Mahānidāna Sutta (DN 15), Pāli Canon
Date: October 2025
"""

import numpy as np
import matplotlib.pyplot as plt

def build_mahanidana_structure():
    """
    Build the EXACT structure from Buddha's teaching

    12 nidānas with:
    - Linear chain (1→2→3, 4→5→...→12)
    - RECIPROCAL between 3↔4 (consciousness ⟷ name-form)
    - Cycle closure (12→1)
    """

    nidanas = [
        'Avidyā',      # 0: Ignorance
        'Saṃskāra',    # 1: Formations
        'Vijñāna',     # 2: Consciousness
        'Nāmarūpa',    # 3: Name-form
        'Ṣaḍāyatana',  # 4: Six senses
        'Sparśa',      # 5: Contact
        'Vedanā',      # 6: Feeling
        'Tṛṣṇā',      # 7: Craving
        'Upādāna',     # 8: Clinging
        'Bhava',       # 9: Becoming
        'Jāti',        # 10: Birth
        'Jarāmaraṇa'   # 11: Aging/death
    ]

    edges = []

    # Linear chain: 1→2→3
    edges.append((nidanas[0], nidanas[1]))
    edges.append((nidanas[1], nidanas[2]))

    # RECIPROCAL: 3↔4 (THE KEY STRUCTURE!)
    edges.append((nidanas[2], nidanas[3]))  # Consciousness → Name-form
    edges.append((nidanas[3], nidanas[2]))  # Name-form → Consciousness

    # Linear continuation: 4→5→...→12
    for i in range(3, 11):
        edges.append((nidanas[i], nidanas[i+1]))

    # Cycle closure: 12→1
    edges.append((nidanas[11], nidanas[0]))

    return nidanas, edges


def build_mahanidana_with_selfloops():
    """
    Add self-loops for "being trapped" at each stage

    Your insight: Samsara = trapped in cycles of lower stages
    """

    nidanas, edges = build_mahanidana_structure()

    # Add self-loop at each nidāna (can persist in that state)
    for nidana in nidanas:
        edges.append((nidana, nidana))

    return nidanas, edges


def build_mahanidana_hierarchical():
    """
    Hierarchical self-loops based on compositional depth

    Deeper nidānas have more self-loops (more ways to get stuck)

    Insight: Later stages have accumulated all prior conditioning,
             so more "weight" of samsara
    """

    nidanas, edges = build_mahanidana_structure()

    # Self-loops proportional to position in chain
    # (later nidānas are "heavier" with karma)
    for i, nidana in enumerate(nidanas):
        # Add (i+1) self-loops
        for _ in range(i + 1):
            edges.append((nidana, nidana))

    return nidanas, edges


def edges_to_matrix(edges, nodes):
    """Convert edge list to adjacency matrix"""
    n = len(nodes)
    A = np.zeros((n, n), dtype=complex)

    for (src, tgt) in edges:
        i = nodes.index(tgt)
        j = nodes.index(src)
        A[i, j] += 1.0

    # Normalize columns (probability conservation)
    for j in range(n):
        col_sum = np.sum(np.abs(A[:, j]))
        if col_sum > 0:
            A[:, j] /= col_sum

    return A


def build_symmetry_operator(nidanas):
    """
    □: Recognizes emptiness of all nidānas

    All nidānas are empty (śūnyatā) - structurally equivalent
    in ultimate truth
    """

    n = len(nidanas)
    box = np.ones((n, n), dtype=complex) / n

    return box


def test_structure(name, nidanas, edges):
    """Test one structural encoding"""

    D_hat = edges_to_matrix(edges, nidanas)
    box = build_symmetry_operator(nidanas)

    nabla = D_hat @ box - box @ D_hat
    R = nabla @ nabla

    nabla_norm = np.linalg.norm(nabla)
    R_norm = np.linalg.norm(R)

    print(f"\n{name}:")
    print(f"  Edges: {len(edges)}")
    print(f"  ||∇|| = {nabla_norm:.8f}")
    print(f"  ||R|| = {R_norm:.8f}")

    if nabla_norm > 1e-10 and R_norm < 1e-6:
        print("  🎯 AUTOPOIETIC!")
    elif nabla_norm > 1e-10:
        print(f"  Nearly autopoietic (R small: {R_norm:.6f})")
    else:
        print("  Trivial (∇=0)")

    return D_hat, box, nabla, R, R_norm


def visualize_mahanidana_structure(results_dict):
    """
    Visualize the different structures and their curvatures
    """

    fig, axes = plt.subplots(2, 2, figsize=(14, 12))

    # Plot each structure's D̂ matrix
    structures = list(results_dict.keys())[:4]  # First 4

    for idx, name in enumerate(structures):
        ax = axes[idx // 2, idx % 2]
        D_hat = results_dict[name]['D_hat']

        im = ax.imshow(np.abs(D_hat), cmap='Blues', aspect='auto')
        ax.set_title(f'{name}\nR = {results_dict[name]["R_norm"]:.6f}')
        ax.set_ylabel('To nidāna')
        ax.set_xlabel('From nidāna')

        # Labels
        if D_hat.shape[0] <= 12:
            ax.set_yticks(range(D_hat.shape[0]))
            ax.set_yticklabels(range(1, D_hat.shape[0]+1), fontsize=8)
            ax.set_xticks(range(D_hat.shape[1]))
            ax.set_xticklabels(range(1, D_hat.shape[1]+1), fontsize=8)

        plt.colorbar(im, ax=ax, fraction=0.046)

    plt.tight_layout()
    plt.savefig('mahanidana_structure_comparison.png', dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved: mahanidana_structure_comparison.png")


def main():
    print("=" * 70)
    print("MAHĀNIDĀNA SUTTA: BUDDHA'S ACTUAL TEACHING")
    print("=" * 70)
    print()
    print("Source: DN 15 (Pāli Canon)")
    print("Key feature: RECIPROCAL conditioning between Vijñāna↔Nāmarūpa")
    print()

    # Test different encodings
    results = {}

    # Structure 1: Pure Buddha's teaching (linear + reciprocal + cycle)
    nidanas1, edges1 = build_mahanidana_structure()
    print("STRUCTURE 1: Buddha's Teaching (Pure)")
    print("-" * 70)
    print("Linear chain: 1→2→3, 4→5→...→12→1")
    print("RECIPROCAL: 3↔4 (consciousness ⟷ name-form)")
    D1, box1, nabla1, R1, R_norm1 = test_structure("Buddha's structure", nidanas1, edges1)
    results["Buddha's structure"] = {'D_hat': D1, 'R_norm': R_norm1}

    # Structure 2: + uniform self-loops
    nidanas2, edges2 = build_mahanidana_with_selfloops()
    print("\nSTRUCTURE 2: + Self-loops (samsara at each stage)")
    print("-" * 70)
    D2, box2, nabla2, R2, R_norm2 = test_structure("+ Self-loops", nidanas2, edges2)
    results["+ Self-loops"] = {'D_hat': D2, 'R_norm': R_norm2}

    # Structure 3: + hierarchical self-loops
    nidanas3, edges3 = build_mahanidana_hierarchical()
    print("\nSTRUCTURE 3: + Hierarchical self-loops")
    print("-" * 70)
    D3, box3, nabla3, R3, R_norm3 = test_structure("+ Hierarchical loops", nidanas3, edges3)
    results["+ Hierarchical loops"] = {'D_hat': D3, 'R_norm': R_norm3}

    # Visualize
    print("\n" + "=" * 70)
    print("GENERATING VISUALIZATIONS")
    print("=" * 70)
    visualize_mahanidana_structure(results)

    # Analysis
    print("\n" + "=" * 70)
    print("KEY FINDINGS")
    print("=" * 70)
    print()

    print("The reciprocal 3↔4 relationship (Vijñāna↔Nāmarūpa):")
    print("  Creates STABLE LOOP in the chain")
    print("  'Like two reeds leaning on each other'")
    print()

    sorted_results = sorted(results.items(), key=lambda x: x[1]['R_norm'])

    print("Curvature comparison:")
    for name, data in sorted_results:
        print(f"  {name:25s}: R = {data['R_norm']:.8f}")

    print()

    best_name = sorted_results[0][0]
    best_R = sorted_results[0][1]['R_norm']

    if best_R < 0.01:
        print(f"✓ '{best_name}' achieves R ≈ {best_R:.6f}")
        print("  NEARLY AUTOPOIETIC!")
        print()
        print("  This is the structure of dependent origination:")
        print("  - Linear progression (most links)")
        print("  - Reciprocal stability (consciousness↔name-form)")
        print("  - Hierarchical depth (later stages heavier)")
        print("  - Cyclical closure (death→ignorance)")
        print()
        print("  Recognition of this complete structure → R≈0")

    print("=" * 70)


if __name__ == "__main__":
    main()
