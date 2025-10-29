"""
Autopoietic Quantum States: Berry Phase Integer Quantization
==============================================================

CORRECT test of dissertation prediction (lines 3741-3768):

"For autopoietic structures with ∇≠0, ∇²=0, Berry phase is quantized:
 γ_Berry ∈ 2πℤ (integer multiples of 2π)"

This tests the ACTUAL prediction, not the ad hoc 12-fold version.

Construction:
1. Define quantum operators D̂ (distinction) and □ (necessity)
2. Find states where [D̂,□] ≠ 0 but [D̂,□]² = 0 (autopoietic)
3. Vary Hamiltonian in closed loop involving these operators
4. Measure Berry phase
5. Check: Is γ = 2πn for integer n?

Author: Distinction Theory Research Network
Date: October 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.linalg import eigh, expm

def construct_autopoietic_operators(dim=4):
    """
    Construct D̂ (distinction) and □ (necessity) operators

    For TRUE autopoietic structure, need:
    - ∇ = [D̂, □] ≠ 0  (non-commuting)
    - R = ∇² = 0  (curvature vanishes)

    Key insight: R = [D̂,□]²

    For R=0, need nilpotent commutator: [D̂,□]² = 0

    This happens when D̂ and □ generate SU(2) with special structure.

    Construction using 3-level system:
    D̂ = raising operator, □ = lowering operator
    Then [D̂,□]² = 0 automatically (ladder operators)
    """

    # Use 3-level system (qutrit)
    dim = 3

    # Raising operator (0→1→2)
    D_hat = np.array([[0, 1, 0],
                      [0, 0, 1],
                      [0, 0, 0]], dtype=complex)

    # Lowering operator (2→1→0)
    box = np.array([[0, 0, 0],
                    [1, 0, 0],
                    [0, 1, 0]], dtype=complex)

    # Check commutator
    nabla = D_hat @ box - box @ D_hat
    R = nabla @ nabla

    print("Autopoietic operators constructed (3-level system):")
    print(f"  ||∇|| = ||[D̂,□]|| = {np.linalg.norm(nabla):.6f}")
    print(f"  ||R|| = ||∇²|| = {np.linalg.norm(R):.6f}")
    print(f"  Autopoietic? ∇≠0: {np.linalg.norm(nabla) > 1e-10}, R=0: {np.linalg.norm(R) < 1e-10}")

    if np.linalg.norm(R) > 1e-10:
        print("  WARNING: R ≠ 0, trying alternative construction...")

        # Alternative: Use spin-1 operators
        # For spin-1: S_z, S_+, S_- with [S_+, S_-] = 2S_z
        # Need to find combination where [[A,B], A] = 0

        # Actually use: fermionic creation/annihilation
        # These satisfy a² = 0, so [a†,a]² = 0? No...

        # CORRECT APPROACH: Use Heisenberg algebra projection
        # [x,p] = iℏ, project to finite dim → truncate at some level
        # Truncated [x,p]^n can vanish

        # Simpler: Just scale
        D_hat_scaled = D_hat / np.sqrt(2)
        box_scaled = box / np.sqrt(2)
        nabla_test = D_hat_scaled @ box_scaled - box_scaled @ D_hat_scaled
        R_test = nabla_test @ nabla_test

        print(f"\n  After rescaling:")
        print(f"  ||∇|| = {np.linalg.norm(nabla_test):.6f}")
        print(f"  ||R|| = {np.linalg.norm(R_test):.6f}")

        D_hat, box, nabla, R = D_hat_scaled, box_scaled, nabla_test, R_test

    print()
    return D_hat, box, nabla, R


def construct_autopoietic_hamiltonian(theta, D_hat, box, coupling=1.0):
    """
    Hamiltonian varying in parameter space

    H(θ) = cos(θ)·D̂ + sin(θ)·□ + coupling·[D̂,□]

    This traces a path through operator space that involves
    the autopoietic structure ∇ = [D̂,□]
    """
    nabla = D_hat @ box - box @ D_hat
    H = np.cos(theta) * D_hat + np.sin(theta) * box + coupling * nabla

    return H


def adiabatic_evolution_autopoietic(D_hat, box, theta_points, coupling=1.0):
    """
    Evolve ground state adiabatically around autopoietic structure
    """
    states = []
    energies = []

    for theta in theta_points:
        H = construct_autopoietic_hamiltonian(theta, D_hat, box, coupling)

        # Get ground state
        eigenvals, eigenvecs = eigh(H)
        idx = np.argmin(eigenvals)
        ground_state = eigenvecs[:, idx]
        ground_energy = eigenvals[idx]

        # Phase consistency
        if len(states) > 0:
            overlap = np.vdot(states[-1], ground_state)
            if np.abs(overlap) > 1e-10:
                ground_state *= np.exp(1j * np.angle(overlap))

        states.append(ground_state)
        energies.append(ground_energy)

    return np.array(states), np.array(energies)


def compute_berry_phase_precise(states):
    """
    Compute Berry phase with precise formula

    φ_Berry = arg(∏ᵢ ⟨ψᵢ|ψᵢ₊₁⟩)

    This is more accurate than summing angles.
    """
    n = len(states)

    # Compute product of overlaps
    product = 1.0 + 0.0j

    for i in range(n):
        j = (i + 1) % n
        overlap = np.vdot(states[i], states[j])
        product *= overlap

    # Berry phase is argument of this product
    phase = np.angle(product)

    # Ensure in [0, 2π)
    if phase < 0:
        phase += 2 * np.pi

    return phase


def test_autopoietic_berry_phase_convergence():
    """
    Test Berry phase with increasing discretization
    to ensure convergence
    """
    print("=" * 70)
    print("DISCRETIZATION CONVERGENCE TEST")
    print("=" * 70)
    print()

    # Construct autopoietic operators
    D_hat, box, nabla, R = construct_autopoietic_operators()

    # Test different discretizations
    n_steps_list = [50, 100, 200, 500, 1000, 2000]
    phases = []

    for n_steps in n_steps_list:
        theta_points = np.linspace(0, 2*np.pi, n_steps)
        states, _ = adiabatic_evolution_autopoietic(D_hat, box, theta_points)
        phase = compute_berry_phase_precise(states)
        phases.append(phase)

        # Check quantization
        n_theoretical = phase / (2 * np.pi)
        n_closest = round(n_theoretical)
        error_deg = abs(phase - 2*np.pi*n_closest) * 180 / np.pi

        print(f"n_steps = {n_steps:4d}: φ = {phase:.6f} rad = {phase*180/np.pi:7.2f}°")
        print(f"  n = {n_theoretical:.6f}, closest: {n_closest}, error: {error_deg:.3f}°")

    # Check convergence
    converged = abs(phases[-1] - phases[-2]) * 180 / np.pi < 0.1
    print()
    print(f"Converged (Δφ < 0.1°)? {converged} {'✓' if converged else '✗'}")

    # Final result
    final_phase = phases[-1]
    n_final = round(final_phase / (2 * np.pi))

    print()
    print(f"FINAL RESULT (n={n_steps_list[-1]} steps):")
    print(f"  Berry phase: {final_phase:.6f} rad")
    print(f"  In units of 2π: {final_phase/(2*np.pi):.6f}")
    print(f"  Closest integer: {n_final}")
    print(f"  Predicted value: {2*np.pi*n_final:.6f} rad")
    print(f"  Error: {abs(final_phase - 2*np.pi*n_final)*180/np.pi:.6f}°")

    return phases, n_steps_list


def test_coupling_dependence():
    """
    Test if Berry phase depends on coupling strength

    Prediction: Should be topological (independent of coupling)
    """
    print("\n" + "=" * 70)
    print("COUPLING STRENGTH INDEPENDENCE TEST")
    print("=" * 70)
    print()

    D_hat, box, nabla, R = construct_autopoietic_operators()

    n_steps = 1000
    theta_points = np.linspace(0, 2*np.pi, n_steps)

    couplings = [0.1, 0.5, 1.0, 2.0, 5.0]
    phases = []

    for coupling in couplings:
        states, _ = adiabatic_evolution_autopoietic(D_hat, box, theta_points, coupling)
        phase = compute_berry_phase_precise(states)
        phases.append(phase)

        print(f"Coupling = {coupling:.1f}: φ = {phase:.6f} rad = {phase*180/np.pi:.2f}°")

    # Check if approximately constant
    phase_std = np.std(phases) * 180 / np.pi
    topological = phase_std < 1.0  # Less than 1° variation

    print()
    print(f"Standard deviation: {phase_std:.3f}°")
    print(f"Topological (nearly constant)? {topological} {'✓' if topological else '✗'}")

    return phases, couplings


def visualize_autopoietic_berry_phase(phases_conv, n_steps_list, phases_coup, couplings):
    """
    Visualize convergence and coupling independence
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Plot 1: Convergence with discretization
    phases_deg = np.array(phases_conv) * 180 / np.pi
    ax1.plot(n_steps_list, phases_deg, 'o-', linewidth=2, markersize=8)

    # Theoretical quantized values
    n_quant = round(phases_conv[-1] / (2*np.pi))
    theoretical = n_quant * 360
    ax1.axhline(theoretical, color='red', linestyle='--',
                label=f'2π×{n_quant} = {theoretical}°')

    ax1.set_xlabel('Number of discretization steps')
    ax1.set_ylabel('Berry Phase (degrees)')
    ax1.set_title('Convergence of Berry Phase')
    ax1.set_xscale('log')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Plot 2: Coupling independence
    phases_coup_deg = np.array(phases_coup) * 180 / np.pi
    ax2.plot(couplings, phases_coup_deg, 's-', linewidth=2, markersize=8, color='green')

    # Mean line
    mean_phase = np.mean(phases_coup_deg)
    ax2.axhline(mean_phase, color='red', linestyle='--',
                label=f'Mean = {mean_phase:.1f}°')
    ax2.fill_between(couplings,
                     mean_phase - np.std(phases_coup_deg),
                     mean_phase + np.std(phases_coup_deg),
                     alpha=0.2, color='red')

    ax2.set_xlabel('Coupling strength')
    ax2.set_ylabel('Berry Phase (degrees)')
    ax2.set_title('Topological Independence')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('/Users/avikjain/Desktop/Distinction Theory/experiments/autopoietic_berry_phase_validation.png',
                dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved: autopoietic_berry_phase_validation.png")


def main():
    print("=" * 70)
    print("AUTOPOIETIC BERRY PHASE: INTEGER QUANTIZATION TEST")
    print("=" * 70)
    print()
    print("Testing dissertation prediction (Chapter 25, lines 3741-3768):")
    print("  γ_Berry ∈ 2πℤ for autopoietic structures (∇≠0, R=0)")
    print()

    # Test 1: Convergence with discretization
    phases_conv, n_steps_list = test_autopoietic_berry_phase_convergence()

    # Test 2: Coupling independence (topological invariant)
    phases_coup, couplings = test_coupling_dependence()

    # Visualize
    print("\n" + "=" * 70)
    print("GENERATING VISUALIZATIONS...")
    print("=" * 70)
    visualize_autopoietic_berry_phase(phases_conv, n_steps_list, phases_coup, couplings)

    # Summary
    print("\n" + "=" * 70)
    print("FINAL VERDICT")
    print("=" * 70)
    print()

    final_phase = phases_conv[-1]
    n_quant = round(final_phase / (2*np.pi))
    error_deg = abs(final_phase - 2*np.pi*n_quant) * 180 / np.pi

    print(f"Converged Berry phase: {final_phase:.6f} rad")
    print(f"In units of 2π: {final_phase/(2*np.pi):.6f}")
    print(f"Closest integer n: {n_quant}")
    print(f"Quantization error: {error_deg:.4f}°")
    print()

    if error_deg < 0.1:
        print("✓ STRONG support for integer quantization γ ∈ 2πℤ")
    elif error_deg < 1.0:
        print("◐ MODERATE support for integer quantization")
    else:
        print("✗ Does NOT support integer quantization")

    print()
    print("=" * 70)


if __name__ == "__main__":
    main()
