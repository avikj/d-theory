#!/usr/bin/env python3
"""
12-Fold Resonance Test: Do primes really cluster in 4 residue classes mod 12?

Tests the prediction that primes > 3 occupy exactly {1, 5, 7, 11} mod 12,
forming the Klein four-group ℤ₂ × ℤ₂.
"""

import numpy as np
import matplotlib.pyplot as plt
from collections import Counter


def is_prime(n):
    """Simple primality test"""
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    for i in range(3, int(np.sqrt(n)) + 1, 2):
        if n % i == 0:
            return False
    return True


def generate_primes(max_n=10000):
    """Generate all primes up to max_n"""
    return [n for n in range(2, max_n) if is_prime(n)]


def test_twelve_fold():
    """Test 12-fold structure in prime distribution"""

    print("="*70)
    print("12-FOLD RESONANCE TEST")
    print("="*70)
    print("\nPrediction: Primes > 3 occupy exactly {1, 5, 7, 11} mod 12")
    print("These form Klein four-group: ℤ₂ × ℤ₂")
    print("="*70)

    # Generate primes
    max_n = 100000
    primes = generate_primes(max_n)

    print(f"\nGenerated {len(primes)} primes up to {max_n}")

    # Count residues mod 12
    residues = Counter([p % 12 for p in primes if p > 3])

    print("\n" + "="*70)
    print("RESIDUE CLASS DISTRIBUTION (mod 12)")
    print("="*70)

    total = sum(residues.values())

    print(f"\n{'Residue':<10} {'Count':<10} {'Fraction':<12} {'Prediction':<15}")
    print("-"*47)

    expected = {1, 5, 7, 11}
    forbidden = {0, 2, 3, 4, 6, 8, 9, 10}

    for i in range(12):
        count = residues.get(i, 0)
        fraction = count / total if total > 0 else 0

        if i in expected:
            pred = "✓ EXPECTED"
        elif i in forbidden:
            pred = "✗ FORBIDDEN"
        else:
            pred = "? (2 or 3)"

        print(f"{i:<10} {count:<10} {fraction:<12.6f} {pred:<15}")

    # Check if forbidden classes are truly absent
    print("\n" + "="*70)
    print("VALIDATION")
    print("="*70)

    forbidden_found = sum(residues.get(i, 0) for i in forbidden)
    expected_found = sum(residues.get(i, 0) for i in expected)

    print(f"\nPrimes in expected classes {expected}: {expected_found} ({100*expected_found/total:.2f}%)")
    print(f"Primes in forbidden classes {forbidden}: {forbidden_found} ({100*forbidden_found/total:.2f}%)")

    # Special cases
    print(f"\nSpecial primes:")
    print(f"  p = 2 (mod 12 = {2 % 12}): Only even prime")
    print(f"  p = 3 (mod 12 = {3 % 12}): Only prime ≡ 3 mod 12")
    print(f"  All others must avoid multiples of 2 and 3")

    if forbidden_found == 0:
        print(f"\n✅ PERFECT: No primes in forbidden classes!")
        print(f"   Prediction CONFIRMED: Primes > 3 occupy exactly {{1,5,7,11}} mod 12")
    else:
        print(f"\n❌ VIOLATION: Found {forbidden_found} primes in forbidden classes")

    # Statistical uniformity test
    print("\n" + "="*70)
    print("UNIFORMITY WITHIN EXPECTED CLASSES")
    print("="*70)

    expected_counts = [residues.get(i, 0) for i in expected]
    mean_count = np.mean(expected_counts)
    std_count = np.std(expected_counts)

    print(f"\nCounts in {{1, 5, 7, 11}}:")
    for i in expected:
        count = residues.get(i, 0)
        deviation = (count - mean_count) / mean_count if mean_count > 0 else 0
        print(f"  {i}: {count} ({deviation:+.2%} from mean)")

    print(f"\nMean: {mean_count:.1f}")
    print(f"Std dev: {std_count:.1f} ({100*std_count/mean_count:.1f}% of mean)")

    if std_count / mean_count < 0.05:
        print(f"\n✅ HIGHLY UNIFORM: Distribution within ±5% of mean")
    else:
        print(f"\n→ Variance: {100*std_count/mean_count:.1f}%")

    # Plot
    plot_results(residues, max_n)

    # Klein four-group structure
    print("\n" + "="*70)
    print("KLEIN FOUR-GROUP STRUCTURE")
    print("="*70)

    print("\nℤ₂ × ℤ₂ = {e, a, b, ab} with operations:")
    print("  1 = e    (identity)")
    print("  5 = a    (generator 1)")
    print("  7 = b    (generator 2)")
    print("  11 = ab  (product)")

    print("\nVerify group properties:")
    print("  5 · 5 ≡ 25 ≡ 1 (mod 12) ✓ (a² = e)")
    print("  7 · 7 ≡ 49 ≡ 1 (mod 12) ✓ (b² = e)")
    print("  5 · 7 ≡ 35 ≡ 11 (mod 12) ✓ (ab)")
    print("  11 · 11 ≡ 121 ≡ 1 (mod 12) ✓ ((ab)² = e)")

    print("\n→ This is exactly ℤ₂ × ℤ₂ structure")


def plot_results(residues, max_n):
    """Visualize residue distribution"""

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Bar chart
    classes = list(range(12))
    counts = [residues.get(i, 0) for i in classes]

    colors = ['green' if i in {1, 5, 7, 11} else
              'blue' if i in {2, 3} else
              'red' for i in classes]

    ax1.bar(classes, counts, color=colors, alpha=0.7, edgecolor='black')
    ax1.set_xlabel('Residue class (mod 12)', fontweight='bold')
    ax1.set_ylabel('Number of primes', fontweight='bold')
    ax1.set_title(f'Prime Distribution mod 12 (primes < {max_n})', fontweight='bold', fontsize=14)
    ax1.set_xticks(classes)
    ax1.grid(True, alpha=0.3, axis='y')

    # Legend
    from matplotlib.patches import Patch
    legend_elements = [
        Patch(facecolor='green', label='Expected: {1,5,7,11}'),
        Patch(facecolor='blue', label='Special: {2,3}'),
        Patch(facecolor='red', label='Forbidden: others')
    ]
    ax1.legend(handles=legend_elements, loc='upper right')

    # Cumulative distribution
    primes = [n for n in range(2, max_n) if is_prime(n)]
    prime_residues = [p % 12 for p in primes if p > 3]

    # Track running fractions
    n_points = min(len(prime_residues), 1000)
    indices = np.linspace(0, len(prime_residues)-1, n_points, dtype=int)

    fractions = {i: [] for i in range(12)}

    for idx in indices:
        subset = prime_residues[:idx+1]
        counts = Counter(subset)
        total = len(subset)
        for i in range(12):
            fractions[i].append(counts.get(i, 0) / total if total > 0 else 0)

    # Plot expected classes
    for i in {1, 5, 7, 11}:
        ax2.plot(indices, fractions[i], label=f'Class {i}', alpha=0.7, linewidth=2)

    # Plot forbidden (should be 0)
    forbidden_total = [sum(fractions[i][j] for i in {0, 4, 6, 8, 9, 10})
                      for j in range(len(indices))]
    ax2.plot(indices, forbidden_total, label='Forbidden (sum)',
            color='red', linestyle='--', alpha=0.7, linewidth=2)

    ax2.axhline(0.25, color='gray', linestyle=':', alpha=0.5, label='25% (uniform)')
    ax2.set_xlabel('Number of primes', fontweight='bold')
    ax2.set_ylabel('Fraction in residue class', fontweight='bold')
    ax2.set_title('Convergence to 4-Class Structure', fontweight='bold', fontsize=14)
    ax2.legend(fontsize=8)
    ax2.grid(True, alpha=0.3)
    ax2.set_ylim([0, 0.35])

    plt.tight_layout()
    plt.savefig('twelve_fold_validation.png', dpi=300, bbox_inches='tight')
    print(f"\n📊 Plot saved: twelve_fold_validation.png")
    plt.close()


if __name__ == '__main__':
    test_twelve_fold()
