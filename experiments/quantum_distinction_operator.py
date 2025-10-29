"""
Quantum Distinction Operator: Empirical Test
=============================================

Tests whether quantum self-examination exhibits predicted exponential structure.

Theory predicts:
- D̂ operator eigenvalues: λₙ = 2ⁿ
- Exponential growth from self-examination

This experiment:
1. Defines D̂ on 2-qubit system (4-dimensional Hilbert space)
2. Computes eigenvalues numerically
3. Tests prediction: do we get powers of 2?

Author: Distinction Theory Research Network
Date: October 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.linalg import eig

# Quantum basis states for 2 qubits
# |00⟩, |01⟩, |10⟩, |11⟩
# Represented as vectors in C^4

def computational_basis_2qubits():
    """Standard computational basis for 2 qubits"""
    basis = {
        '00': np.array([1, 0, 0, 0]),
        '01': np.array([0, 1, 0, 0]),
        '10': np.array([0, 0, 1, 0]),
        '11': np.array([0, 0, 0, 1])
    }
    return basis


def construct_distinction_operator_v1():
    """
    First attempt: D̂ as "examine all pairs"

    For 2-qubit system, D̂ should:
    - Take each basis state |i⟩
    - Form superposition of all pairs (|i⟩, |j⟩)
    - Weight by "path" between them

    In discrete case with n=4 states:
    D̂|i⟩ = Σⱼ |i,j⟩⟨j|

    But we need to map back to 4-dim space...
    This gives us the distinction structure.
    """

    # Strategy: D̂ examines by creating superpositions
    # D̂ = Σᵢⱼ |i⟩⟨j| ⊗ (phase factor for distinction)

    # Simplest version: symmetric examination
    # D̂ = I ⊗ I + X ⊗ X + Y ⊗ Y + Z ⊗ Z
    # (all ways qubits can relate)

    I = np.eye(2)
    X = np.array([[0, 1], [1, 0]])  # Pauli X
    Y = np.array([[0, -1j], [1j, 0]])  # Pauli Y
    Z = np.array([[1, 0], [0, -1]])  # Pauli Z

    # Tensor products
    II = np.kron(I, I)
    XX = np.kron(X, X)
    YY = np.kron(Y, Y)
    ZZ = np.kron(Z, Z)

    # D̂ = sum of all correlations (symmetric examination)
    D_hat = II + XX + YY + ZZ

    return D_hat


def construct_distinction_operator_v2():
    """
    Second attempt: D̂ as path-weighted operator

    For n states, distinction forms n×n matrix where
    D̂ᵢⱼ = ⟨i|path|j⟩

    In simplest case: D̂ᵢⱼ = 1 for all i,j (all pairs exist)
    This is D̂ = 𝟙·𝟙ᵀ (outer product of all-ones vector)

    For 4 states: 4×4 matrix of all ones
    """
    n = 4
    D_hat = np.ones((n, n))
    return D_hat


def construct_distinction_operator_v3():
    """
    Third attempt: D̂ derived from path structure

    D(X) = Σ_{x,y:X} Path(x,y)

    For discrete X with 4 points, paths are adjacency structure.
    Let's use: complete graph (all pairs connected)

    D̂ᵢⱼ = { 1 if i≠j (path exists between different states)
           { 2 if i=j (path from state to itself = identity + loop)

    This gives diagonal bonus for self-loops.
    """
    n = 4
    D_hat = np.ones((n, n))  # All pairs connected
    np.fill_diagonal(D_hat, 2)  # Self-examination gets weight 2
    return D_hat


def analyze_eigenspectrum(D_hat, name="D̂"):
    """
    Compute and analyze eigenvalues of distinction operator

    Returns:
        eigenvalues: sorted eigenvalues
        eigenvectors: corresponding eigenvectors
        analysis: dict with properties
    """
    eigenvalues, eigenvectors = eig(D_hat)

    # Sort by magnitude
    idx = np.argsort(np.abs(eigenvalues))[::-1]
    eigenvalues = eigenvalues[idx]
    eigenvectors = eigenvectors[:, idx]

    # Check if they follow 2^n pattern
    powers_of_two = np.array([2**i for i in range(len(eigenvalues))])

    # Compute how close to 2^n
    if np.allclose(eigenvalues.real, 0):
        relative_error = np.inf
    else:
        # Try to find best fit: λ = a·2^n
        log_eigs = np.log2(np.abs(eigenvalues) + 1e-10)
        expected_logs = np.arange(len(eigenvalues))[::-1]  # [3,2,1,0] for n=4

        # Correlation
        if np.std(log_eigs) > 1e-10:
            correlation = np.corrcoef(log_eigs, expected_logs)[0,1]
        else:
            correlation = 0.0

    analysis = {
        'eigenvalues': eigenvalues,
        'real_parts': eigenvalues.real,
        'imag_parts': eigenvalues.imag,
        'powers_of_two_correlation': correlation if 'correlation' in locals() else 0,
        'is_hermitian': np.allclose(D_hat, D_hat.conj().T),
        'is_real': np.allclose(eigenvalues.imag, 0)
    }

    return eigenvalues, eigenvectors, analysis


def visualize_spectrum(results_dict):
    """
    Visualize eigenspectra for different D̂ constructions
    """
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    for idx, (name, data) in enumerate(results_dict.items()):
        ax = axes[idx // 2, idx % 2]

        eigs = data['eigenvalues'].real
        n = len(eigs)

        # Plot eigenvalues
        ax.scatter(range(n), eigs, s=100, alpha=0.7, label='Computed')

        # Plot predicted 2^n pattern (scaled to match largest eigenvalue)
        if eigs[0] != 0:
            scale = eigs[0] / (2**(n-1))
            predicted = scale * np.array([2**i for i in range(n-1, -1, -1)])
            ax.plot(range(n), predicted, 'r--', alpha=0.5, label='2ⁿ pattern')

        ax.set_xlabel('Eigenvalue index')
        ax.set_ylabel('Eigenvalue')
        ax.set_title(f'{name}\nCorr with log₂: {data["powers_of_two_correlation"]:.3f}')
        ax.legend()
        ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('/Users/avikjain/Desktop/Distinction Theory/experiments/quantum_D_eigenspectrum.png',
                dpi=150, bbox_inches='tight')
    print("✓ Eigenspectrum visualization saved")

    return fig


def test_tower_growth():
    """
    CORRECT TEST: Tower growth D^n dimensions

    Theory says: dim(D^n(X)) = dim(X)^(2^n)

    For 2-qubit system (dim=4):
    - D⁰: dim = 4
    - D¹: dim = 4² = 16
    - D²: dim = 16² = 256
    - D³: dim = 65536 (too large to simulate)

    But eigenvalues of D on the n-th level should show 2^n growth.

    Let's test: if we apply D operator that maps 4-dim → 16-dim,
    does it have the right structure?
    """
    print("\n" + "=" * 60)
    print("TOWER GROWTH TEST (CORRECT INTERPRETATION)")
    print("=" * 60)

    # For 2-qubit system, D should map C^4 → C^16
    # D(ψ) = all pairs of states with paths

    # In practice: D acts by tensor product with itself
    # D: V → V ⊗ V (dimension doubles via pairing)

    # Eigenvalues: if D has eigenvalues λᵢ,
    # then D⊗D has eigenvalues λᵢ·λⱼ

    # Start with simpler operator: scaling by 2
    # If D = 2·I, then Dⁿ = 2ⁿ·I → eigenvalues 2ⁿ ✓

    # But D is more complex...
    # Let's try: D defined such that ||D(ψ)||² = 2·||ψ||²

    # For a 4-level system, simplest D with ||Dψ|| = √2·||ψ||:
    D_simple = np.sqrt(2) * np.eye(4)

    eigs = np.linalg.eigvals(D_simple)
    print(f"\nSimplest D (scaling by √2):")
    print(f"Eigenvalues: {eigs}")
    print(f"D^n eigenvalues: {eigs[0]}^n = (√2)^n")
    print(f"  n=0: {eigs[0]**0:.4f}")
    print(f"  n=1: {eigs[0]**1:.4f}")
    print(f"  n=2: {eigs[0]**2:.4f} = 2")
    print(f"  n=3: {eigs[0]**3:.4f} = 2√2")
    print(f"  n=4: {eigs[0]**4:.4f} = 4")

    print(f"\n→ Pattern: eigenvalues grow as (√2)^n, NOT 2^n")
    print(f"→ This suggests: dimension growth (2^n) ≠ eigenvalue growth")

    return D_simple


def main():
    """
    Main experimental protocol (REVISED)
    """
    print("=" * 60)
    print("QUANTUM DISTINCTION OPERATOR: EIGENSPECTRUM TEST")
    print("=" * 60)
    print()
    print("IMPORTANT: First attempts showed no 2^n pattern.")
    print("Reason: confused eigenvalues with dimension growth.")
    print()
    print("Theory says: dim(D^n(X)) = dim(X)^(2^n)")
    print("  For 4-dim system: D¹ → 16-dim, D² → 256-dim")
    print()
    print("Eigenvalues are DIFFERENT from dimension!")
    print("=" * 60)

    # Original tests (for comparison)
    constructions = {
        'v1: Pauli correlation': construct_distinction_operator_v1(),
        'v2: All-pairs uniform': construct_distinction_operator_v2(),
        'v3: Self-loop enhanced': construct_distinction_operator_v3()
    }

    results = {}

    for name, D_hat in constructions.items():
        print(f"\n{name}")
        print("-" * 60)

        eigs, vecs, analysis = analyze_eigenspectrum(D_hat, name)

        print(f"Eigenvalues: {eigs.real}")
        print(f"Correlation with 2ⁿ: {analysis['powers_of_two_correlation']:.4f}")

        results[name] = analysis

    # NEW: Tower growth test
    D_simple = test_tower_growth()

    # Visualize
    print("\n" + "=" * 60)
    print("GENERATING VISUALIZATIONS...")
    print("=" * 60)
    visualize_spectrum(results)

    # REVISED Summary
    print("\n" + "=" * 60)
    print("CORRECTED UNDERSTANDING")
    print("=" * 60)
    print()
    print("The 2^n pattern appears in DIMENSION growth, not eigenvalues:")
    print("  dim(D(X)) = dim(X)²")
    print("  dim(D²(X)) = dim(X)^4")
    print("  dim(D^n(X)) = dim(X)^(2^n)")
    print()
    print("For 2-qubit system (4-dimensional):")
    print("  D⁰: 4 dimensions")
    print("  D¹: 16 dimensions")
    print("  D²: 256 dimensions")
    print("  D³: 65536 dimensions (too large to simulate)")
    print()
    print("NEXT STEP: Test dimension doubling explicitly")
    print("  (construct D: C^4 → C^16, verify structure)")
    print("=" * 60)


if __name__ == "__main__":
    main()
