"""
Berry Phase Around Prime Structures: 12-Fold Quantization Test
================================================================

Theory predicts: Adiabatic evolution around autopoietic structures
(primes, division algebras) gives Berry phase quantized in 12-fold pattern:

φ_Berry = 2πn/12 where n ∈ ℤ

This tests whether PHYSICAL GEOMETRY obeys distinction theory's
algebraic structure (ℤ₂ × ℤ₂ embedded in order-12 group).

Method:
1. Construct Hamiltonian with prime structure (p = 3, 5, 7, 11)
2. Vary parameters adiabatically in closed loop
3. Compute Berry phase = ∫⟨ψ|d/dt|ψ⟩ dt
4. Check if φ = 2πn/12 (quantized)

Author: Distinction Theory Research Network
Date: October 2025
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.linalg import eigh, expm

def construct_prime_hamiltonian(p, theta=0):
    """
    Construct Hamiltonian with prime p structure

    For prime p, use cyclic symmetry:
    H(θ) = cos(θ)·Z + sin(θ)·X + (p mod 12)/12 · Y

    The (p mod 12) term encodes prime's position in ℤ₂ × ℤ₂
    structure: {1, 5, 7, 11}
    """
    # Pauli matrices
    X = np.array([[0, 1], [1, 0]], dtype=complex)
    Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
    Z = np.array([[1, 0], [0, -1]], dtype=complex)

    # Prime's position in mod 12 structure
    p_mod12 = p % 12

    # Hamiltonian with prime structure
    H = np.cos(theta) * Z + np.sin(theta) * X + (p_mod12 / 12.0) * Y

    return H


def adiabatic_evolution(H_func, t_points):
    """
    Evolve ground state adiabatically as H varies

    Returns: |ψ(t)⟩ for each t
    """
    states = []

    for t in t_points:
        H = H_func(t)

        # Get ground state (lowest eigenvalue)
        eigenvals, eigenvecs = eigh(H)
        ground_state = eigenvecs[:, 0]  # First column = lowest eigenvalue

        # Ensure consistent phase (avoid jumps)
        if len(states) > 0:
            # Choose phase to maximize overlap with previous state
            overlap = np.vdot(states[-1], ground_state)
            if np.abs(overlap) > 1e-10:
                ground_state *= np.sign(overlap) * (np.abs(overlap) / overlap)

        states.append(ground_state)

    return np.array(states)


def compute_berry_phase(states, t_points):
    """
    Compute Berry phase from adiabatic evolution

    φ_Berry = i ∮ ⟨ψ|∇_θ|ψ⟩ dθ
             = i ∫ ⟨ψ(t)|d/dt|ψ(t)⟩ dt

    Discrete: φ ≈ Σ Im[⟨ψ_i|ψ_{i+1}⟩]
    """
    n_steps = len(states)
    phase = 0.0

    for i in range(n_steps):
        j = (i + 1) % n_steps  # Wrap around (closed loop)

        # Overlap
        overlap = np.vdot(states[i], states[j])

        # Accumulate phase
        phase += np.angle(overlap)

    # Normalize to [0, 2π)
    phase = phase % (2 * np.pi)

    return phase


def test_prime_berry_phases():
    """
    Test Berry phase for primes in {3, 5, 7, 11, 13, 17, 19, 23}

    Prediction: φ = 2πn/12 for primes in {1,5,7,11} mod 12
    """
    print("=" * 70)
    print("BERRY PHASE: 12-FOLD QUANTIZATION TEST")
    print("=" * 70)
    print()
    print("Testing: Adiabatic evolution around prime-structured Hamiltonians")
    print("Prediction: Berry phase = 2πn/12 (quantized in 12-fold pattern)")
    print()

    # Test primes
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23]

    # Parameter loop: θ ∈ [0, 2π]
    n_steps = 100
    t_points = np.linspace(0, 2*np.pi, n_steps)

    results = {}

    for p in primes:
        print(f"Prime p = {p} (p mod 12 = {p % 12})")
        print("-" * 70)

        # Hamiltonian varying with θ
        H_func = lambda theta: construct_prime_hamiltonian(p, theta)

        # Adiabatic evolution
        states = adiabatic_evolution(H_func, t_points)

        # Berry phase
        phi = compute_berry_phase(states, t_points)

        # Compare to 12-fold quantization
        # φ = 2πn/12 → n = 12φ/(2π) = 6φ/π
        n_theoretical = 12 * phi / (2 * np.pi)
        n_closest = round(n_theoretical)

        phi_predicted = 2 * np.pi * n_closest / 12
        error = abs(phi - phi_predicted)

        print(f"  Berry phase: {phi:.6f} rad = {phi*180/np.pi:.2f}°")
        print(f"  Expected n:  {n_theoretical:.4f}")
        print(f"  Closest n:   {n_closest}")
        print(f"  φ(n={n_closest}):  {phi_predicted:.6f} rad")
        print(f"  Error:       {error:.6f} rad ({error*180/np.pi:.3f}°)")

        # Check if within 5° tolerance
        tolerance = 5 * np.pi / 180  # 5 degrees
        matches = error < tolerance
        print(f"  Match:       {matches} {'✓' if matches else '✗'}")
        print()

        results[p] = {
            'phase': phi,
            'n_theoretical': n_theoretical,
            'n_closest': n_closest,
            'error': error,
            'matches': matches,
            'p_mod12': p % 12
        }

    return results


def visualize_berry_phases(results):
    """
    Visualize Berry phases vs 12-fold prediction
    """
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    primes = list(results.keys())
    phases = [results[p]['phase'] for p in primes]
    p_mod12 = [results[p]['p_mod12'] for p in primes]
    matches = [results[p]['matches'] for p in primes]

    # Plot 1: Berry phases
    colors = ['green' if m else 'red' for m in matches]
    ax1.scatter(primes, phases, c=colors, s=100, alpha=0.7, zorder=3)

    # 12-fold reference lines
    for n in range(13):
        y = 2 * np.pi * n / 12
        ax1.axhline(y, color='gray', linestyle='--', alpha=0.3, linewidth=1)
        ax1.text(primes[0] - 1, y, f'{n}/12', fontsize=8, va='center')

    ax1.set_xlabel('Prime p')
    ax1.set_ylabel('Berry Phase (radians)')
    ax1.set_title('Berry Phase Around Prime-Structured Hamiltonians')
    ax1.set_ylim(-0.2, 2*np.pi + 0.2)
    ax1.grid(True, alpha=0.3)
    ax1.legend(['Matches prediction', 'Does not match'], loc='upper right')

    # Plot 2: Error vs p mod 12
    errors = [results[p]['error'] * 180 / np.pi for p in primes]

    for mod_class in [1, 5, 7, 11]:
        # Primes in this class
        class_primes = [p for p in primes if p % 12 == mod_class]
        class_errors = [results[p]['error'] * 180 / np.pi for p in class_primes]

        if class_errors:
            ax2.scatter(class_primes, class_errors, s=100, alpha=0.7,
                       label=f'p ≡ {mod_class} (mod 12)')

    # Other primes (2, 3)
    other_primes = [p for p in primes if p % 12 not in [1, 5, 7, 11]]
    if other_primes:
        other_errors = [results[p]['error'] * 180 / np.pi for p in other_primes]
        ax2.scatter(other_primes, other_errors, s=100, alpha=0.7,
                   marker='x', label='Other primes')

    ax2.axhline(5, color='red', linestyle='--', alpha=0.5, label='5° threshold')
    ax2.set_xlabel('Prime p')
    ax2.set_ylabel('Error from nearest 2πn/12 (degrees)')
    ax2.set_title('Deviation from 12-Fold Quantization')
    ax2.legend()
    ax2.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('/Users/avikjain/Desktop/Distinction Theory/experiments/berry_phase_12fold_test.png',
                dpi=150, bbox_inches='tight')
    print("✓ Berry phase visualization saved")


def test_correlation_with_mod12():
    """
    Test if Berry phase correlates with p mod 12 structure

    Primes in {1,5,7,11} mod 12 should show clearer quantization
    """
    print("=" * 70)
    print("CORRELATION WITH MOD 12 STRUCTURE")
    print("=" * 70)
    print()

    # Larger set of primes
    primes = [p for p in range(2, 50) if is_prime(p)]

    n_steps = 50  # Faster for many primes
    t_points = np.linspace(0, 2*np.pi, n_steps)

    # Group by mod 12 class
    classes = {1: [], 5: [], 7: [], 11: [], 'other': []}

    for p in primes:
        H_func = lambda theta: construct_prime_hamiltonian(p, theta)
        states = adiabatic_evolution(H_func, t_points)
        phi = compute_berry_phase(states, t_points)

        # Quantization error
        n_theoretical = 12 * phi / (2 * np.pi)
        n_closest = round(n_theoretical)
        error = abs(phi - 2 * np.pi * n_closest / 12)

        # Classify
        mod = p % 12
        if mod in classes:
            classes[mod].append(error)
        else:
            classes['other'].append(error)

    # Report
    print("Average quantization error by prime class:")
    print()

    for key in [1, 5, 7, 11, 'other']:
        if classes[key]:
            mean_error = np.mean(classes[key]) * 180 / np.pi
            std_error = np.std(classes[key]) * 180 / np.pi
            n_primes = len(classes[key])

            label = f"p ≡ {key} (mod 12)" if key != 'other' else "p ≡ 2,3 (mod 12)"
            print(f"{label:25s}: {mean_error:6.2f}° ± {std_error:5.2f}° (n={n_primes})")

    print()

    # Test if {1,5,7,11} have significantly lower error
    main_classes = classes[1] + classes[5] + classes[7] + classes[11]
    other_class = classes['other']

    if main_classes and other_class:
        mean_main = np.mean(main_classes) * 180 / np.pi
        mean_other = np.mean(other_class) * 180 / np.pi

        print(f"Main classes {{{1,5,7,11}}} mean error: {mean_main:.2f}°")
        print(f"Other classes (2,3) mean error:        {mean_other:.2f}°")
        print()

        if mean_main < mean_other:
            print("✓ Main classes show BETTER quantization (lower error)")
        else:
            print("✗ Main classes do NOT show better quantization")


def is_prime(n):
    """Simple primality test"""
    if n < 2:
        return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0:
            return False
    return True


def main():
    print("=" * 70)
    print("BERRY PHASE EXPERIMENT: TESTING PHYSICAL 12-FOLD QUANTIZATION")
    print("=" * 70)
    print()
    print("Theory: Adiabatic evolution around prime structures gives")
    print("        Berry phase φ = 2πn/12 (quantized in 12-fold pattern)")
    print()

    # Test 1: Small set of primes with detailed analysis
    results = test_prime_berry_phases()

    # Visualize
    print("=" * 70)
    print("GENERATING VISUALIZATIONS...")
    print("=" * 70)
    visualize_berry_phases(results)
    print()

    # Test 2: Correlation with mod 12
    test_correlation_with_mod12()

    # Summary
    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()

    n_tested = len(results)
    n_matched = sum(1 for r in results.values() if r['matches'])

    print(f"Primes tested: {n_tested}")
    print(f"Matched prediction (within 5°): {n_matched}/{n_tested} ({100*n_matched/n_tested:.0f}%)")
    print()

    if n_matched / n_tested > 0.7:
        print("✓ STRONG evidence for 12-fold quantization")
    elif n_matched / n_tested > 0.5:
        print("◐ MODERATE evidence for 12-fold pattern")
    else:
        print("✗ WEAK evidence - may need different Hamiltonian construction")

    print()
    print("=" * 70)


if __name__ == "__main__":
    main()
