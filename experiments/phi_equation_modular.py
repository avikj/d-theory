"""
x² = x + 1 in Modular Fields: The Golden Equation
==================================================

Testing: For which primes p does x² ≡ x + 1 (mod p) have solutions?

Connection to:
- φ (golden ratio in ℝ)
- Primes mod 12 structure
- Goldbach symmetry

Hypothesis: Solution structure relates to p mod 12 classes {1,5,7,11}

Author: Distinction Theory Research Network
Date: October 2024
"""

import numpy as np
import matplotlib.pyplot as plt

def is_prime(n):
    """Simple primality test"""
    if n < 2:
        return False
    for i in range(2, int(n**0.5) + 1):
        if n % i == 0:
            return False
    return True


def solve_phi_equation_mod_p(p):
    """
    Solve x² ≡ x + 1 (mod p)

    Returns: list of solutions in {0,1,...,p-1}
    """
    solutions = []

    for x in range(p):
        if (x*x) % p == (x + 1) % p:
            solutions.append(x)

    return solutions


def analyze_solution_pattern():
    """
    Test x² ≡ x+1 (mod p) for all primes up to 200

    Check if solution count/structure relates to p mod 12
    """

    print("=" * 70)
    print("GOLDEN EQUATION IN MODULAR FIELDS: x² ≡ x + 1 (mod p)")
    print("=" * 70)
    print()

    primes = [p for p in range(2, 200) if is_prime(p)]

    results = []

    print("Prime p | p mod 12 | Solutions | Count")
    print("-" * 70)

    for p in primes[:30]:  # First 30 primes
        sols = solve_phi_equation_mod_p(p)
        p_mod12 = p % 12

        sols_str = str(sols) if len(sols) <= 4 else f"{len(sols)} solutions"

        print(f"{p:7d} | {p_mod12:8d} | {sols_str:20s} | {len(sols)}")

        results.append({
            'p': p,
            'p_mod12': p_mod12,
            'solutions': sols,
            'count': len(sols)
        })

    return results


def group_by_mod12(results):
    """
    Group results by p mod 12 class
    """

    print("\n" + "=" * 70)
    print("PATTERN BY MOD 12 CLASS")
    print("=" * 70)
    print()

    classes = {}
    for r in results:
        mod_class = r['p_mod12']
        if mod_class not in classes:
            classes[mod_class] = []
        classes[mod_class].append(r)

    for mod_class in sorted(classes.keys()):
        primes_in_class = classes[mod_class]
        counts = [r['count'] for r in primes_in_class]

        if counts:
            avg_count = np.mean(counts)
            print(f"p ≡ {mod_class:2d} (mod 12): {len(primes_in_class):3d} primes, avg solutions: {avg_count:.2f}")

            # Show first few examples
            examples = primes_in_class[:3]
            for ex in examples:
                print(f"  p={ex['p']:3d}: {ex['count']} solutions {ex['solutions']}")


def test_frobenius_trace():
    """
    The number of solutions relates to Frobenius trace

    For x² = x + 1, this is quadratic form
    Solutions counted by Legendre symbol and quadratic reciprocity
    """

    print("\n" + "=" * 70)
    print("QUADRATIC RECIPROCITY ANALYSIS")
    print("=" * 70)
    print()

    print("For x² - x - 1 = 0 (mod p):")
    print("Discriminant Δ = 1 + 4 = 5")
    print()
    print("By quadratic reciprocity:")
    print("  Solutions exist iff 5 is quadratic residue mod p")
    print("  iff (5/p) = 1 (Legendre symbol)")
    print()

    # Test this
    primes = [p for p in range(3, 100) if is_prime(p)]

    for p in primes[:20]:
        sols = solve_phi_equation_mod_p(p)

        # Compute (5/p) - whether 5 is QR mod p
        is_qr = any((5 * x) % p == (y*y) % p for x in range(p) for y in range(p))

        has_solutions = len(sols) > 0

        match = "✓" if (is_qr == has_solutions) else "✗"

        print(f"p={p:3d}: 5 is QR? {is_qr}, has solutions? {has_solutions} {match}")


def test_connection_to_12fold():
    """
    Check if primes in {1,5,7,11} mod 12 have special behavior
    """

    print("\n" + "=" * 70)
    print("CONNECTION TO 12-FOLD PRIME STRUCTURE")
    print("=" * 70)
    print()

    primes = [p for p in range(2, 500) if is_prime(p)]

    # Group by mod 12 class
    prime_classes = {1: [], 5: [], 7: [], 11: [], 'other': []}

    for p in primes:
        if p in [2, 3]:
            prime_classes['other'].append(p)
        else:
            mod_class = p % 12
            if mod_class in prime_classes:
                prime_classes[mod_class].append(p)

    print("Testing x² ≡ x+1 (mod p) for each mod 12 class:")
    print()

    for cls in [1, 5, 7, 11]:
        primes_in_cls = prime_classes[cls]

        # Test each
        solution_counts = []
        for p in primes_in_cls:
            sols = solve_phi_equation_mod_p(p)
            solution_counts.append(len(sols))

        avg = np.mean(solution_counts) if solution_counts else 0

        # Check consistency
        unique_counts = set(solution_counts)

        print(f"p ≡ {cls} (mod 12): {len(primes_in_cls)} primes tested")
        print(f"  Solution counts: {unique_counts}")
        print(f"  Average: {avg:.2f}")
        print(f"  Pattern: {'Consistent' if len(unique_counts) <= 2 else 'Variable'}")
        print()


def visualize_solution_structure(results):
    """
    Visualize solutions across primes
    """

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    primes = [r['p'] for r in results]
    counts = [r['count'] for r in results]
    mod12 = [r['p_mod12'] for r in results]

    # Plot 1: Solution count vs prime
    colors = ['red' if m in [1,5,7,11] else 'gray' for m in mod12]
    ax1.scatter(primes, counts, c=colors, alpha=0.6)
    ax1.set_xlabel('Prime p')
    ax1.set_ylabel('Number of solutions')
    ax1.set_title('Solutions to x² ≡ x+1 (mod p)')
    ax1.axhline(2, color='blue', linestyle='--', alpha=0.3, label='2 solutions')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Plot 2: By mod 12 class
    classes = {1: [], 5: [], 7: [], 11: [], 'other': []}
    for r in results:
        if r['p'] in [2,3]:
            classes['other'].append(r['count'])
        else:
            mod = r['p_mod12']
            if mod in classes:
                classes[mod].append(r['count'])

    class_labels = ['1', '5', '7', '11']
    class_means = [np.mean(classes[int(c)]) if classes[int(c)] else 0 for c in class_labels]

    ax2.bar(class_labels, class_means, alpha=0.7)
    ax2.set_xlabel('p mod 12')
    ax2.set_ylabel('Average solution count')
    ax2.set_title('Solutions by Prime Class')
    ax2.axhline(2, color='blue', linestyle='--', alpha=0.3)
    ax2.grid(True, alpha=0.3, axis='y')

    plt.tight_layout()
    plt.savefig('phi_equation_modular.png', dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved: phi_equation_modular.png")


def main():
    print("Testing Golden Equation Across Modular Fields")
    print()
    print("Question: Does x² = x+1 solution structure relate to")
    print("          prime position in mod 12 classification?")
    print()

    # Analyze solution pattern
    results = analyze_solution_pattern()

    # Group by mod 12
    group_by_mod12(results)

    # Frobenius/QR analysis
    test_frobenius_trace()

    # 12-fold connection
    test_connection_to_12fold()

    # Visualize
    visualize_solution_structure(results)

    print("\n" + "=" * 70)
    print("SYNTHESIS")
    print("=" * 70)
    print()
    print("The golden equation x² = x+1:")
    print("  • Has 2 solutions in ℝ (φ and -1/φ)")
    print("  • Behavior in ℤ_p depends on p")
    print("  • Related to quadratic reciprocity (discriminant = 5)")
    print("  • Connection to 12-fold structure...")
    print()
    print("Next: Test in quaternions ℍ (infinite solutions)")
    print("      Explore why dimensionality changes solution space")
    print("=" * 70)


if __name__ == "__main__":
    main()
