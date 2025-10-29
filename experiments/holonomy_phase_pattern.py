"""
Holonomy Phase Pattern: Why 1.5π?
==================================

Test different cycle lengths to find pattern in holonomy phases.

For n-cycle with reciprocal at canonical position (floor(n/3), floor(n/3)+1):
- Compute holonomy around full cycle
- Extract phase
- Look for formula: phase = f(n)?

Hypothesis: Phase = π(n-2)/n or similar

Author: Anonymous Research Network, Berkeley CA
Date: October 2024
"""

import numpy as np
import matplotlib.pyplot as plt

def build_cycle_with_reciprocal(n):
    """Build n-cycle with reciprocal at canonical position"""
    edges = [(i, (i+1) % n) for i in range(n)]

    # Add reciprocal at ~n/3 position (like 3↔4 for n=12)
    recip_i = n // 3
    recip_j = recip_i + 1
    edges.append((recip_j, recip_i))

    return edges, (recip_i, recip_j)

def compute_holonomy_phase(edges, n, recip_pos):
    """Simplified holonomy computation"""
    recip_i, recip_j = recip_pos
    # Build adjacency
    D = np.zeros((n,n), dtype=complex)
    for (src, tgt) in edges:
        D[tgt, src] += 1.0

    # Normalize
    for j in range(n):
        s = np.sum(np.abs(D[:,j]))
        if s > 0:
            D[:,j] /= s

    # Uniform box
    box = np.ones((n,n), dtype=complex) / n

    # Connection
    nabla = D @ box - box @ D

    # Holonomy = product of exponentials around cycle (simplified)
    # For small ∇: exp(∇) ≈ I + ∇
    # Product around cycle ≈ exp(sum of ∇ along edges)

    # Extract phase from eigenvalues of ∇
    eigvals = np.linalg.eigvals(nabla)

    # Holonomy phase ~ sum of eigenvalue phases
    phase_estimate = np.sum(np.angle(eigvals))

    # Also: Direct trace-based estimate
    # For cycle: Holonomy ~ det(exp(∇)) = exp(Tr(∇))
    trace_nabla = np.trace(nabla)
    phase_from_trace = np.imag(trace_nabla) * n  # Scaled

    # Measure R
    R = nabla @ nabla
    R_norm = np.linalg.norm(R)

    return phase_estimate, R_norm, (recip_i, recip_j)

def main():
    print("=" * 70)
    print("HOLONOMY PHASE PATTERN ANALYSIS")
    print("=" * 70)
    print()

    cycle_lengths = [6, 8, 10, 12, 15, 18, 24, 30, 36]

    results = []

    print(f"{'n':>3} | {'Recip':>6} | {'Phase':>10} | {'R':>12} | {'Ratio':>8}")
    print("-" * 70)

    for n in cycle_lengths:
        edges, (i,j) = build_cycle_with_reciprocal(n)
        phase, R_norm, (ri, rj) = compute_holonomy_phase(edges, n, (i,j))

        # Normalize phase to [0, 2π)
        phase_mod = phase % (2 * np.pi)

        # Check ratio
        ratio = phase / np.pi if np.abs(phase) > 1e-6 else 0

        results.append({
            'n': n,
            'recip': f"{ri}↔{rj}",
            'phase': phase,
            'phase_mod': phase_mod,
            'R': R_norm,
            'ratio': ratio,
            'i': ri,
            'j': rj
        })

        print(f"{n:3d} | {ri}↔{rj:2d} | {phase:9.6f} | {R_norm:12.10f} | {ratio:7.4f}π")

    print()
    print("=" * 70)
    print("PATTERN ANALYSIS")
    print("=" * 70)
    print()

    # Look for pattern
    print("Testing hypotheses:")
    print()

    for idx, r in enumerate(results):
        n = r['n']
        phase = r['phase']
        i, j = r['i'], r['j']

        # Hypothesis 1: phase = π(n-2)/n
        pred1 = np.pi * (n - 2) / n
        err1 = abs(phase - pred1)

        # Hypothesis 2: phase = π(1 - 2/n)
        pred2 = np.pi * (1 - 2.0/n)
        err2 = abs(phase - pred2)

        # Hypothesis 3: phase = π(product)/(n) where product=i×j
        product = i * j
        pred3 = np.pi * product / n
        err3 = abs(phase - pred3)

        # Best fit
        best_err = min(err1, err2, err3)
        best = ['(n-2)/n', '(1-2/n)', 'ij/n'][np.argmin([err1, err2, err3])]

        print(f"n={n:2d}: phase={phase/np.pi:.4f}π, best={best} (err={best_err:.4f})")

    print()
    print("=" * 70)

    # If pattern found
    phases_over_pi = [r['phase']/np.pi for r in results]

    # Check if linear in 1/n
    n_vals = [r['n'] for r in results]
    inv_n = [1.0/n for n in n_vals]

    # Linear fit
    coeffs = np.polyfit(inv_n, phases_over_pi, 1)
    a, b = coeffs

    print()
    print(f"Linear fit: phase/π = {a:.4f}(1/n) + {b:.4f}")
    print()

    if abs(a + 2) < 0.1 and abs(b - 1) < 0.1:
        print("✓ PATTERN FOUND: phase ≈ π(1 - 2/n)")
        print()
        print("  Interpretation:")
        print("    For n=12: phase = π(1 - 2/12) = π(10/12) = 5π/6")
        print("    Measured: ~1.5π = 9π/6 (close but not exact)")
        print()
        print("  May indicate topological invariant related to n")

    # Visualize
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Phase vs n
    ax1.plot(n_vals, phases_over_pi, 'bo-', markersize=8, linewidth=2)
    ax1.axhline(1.5, color='red', linestyle='--', label='1.5π (n=12 measured)')
    ax1.set_xlabel('Cycle length n', fontsize=12)
    ax1.set_ylabel('Phase / π', fontsize=12)
    ax1.set_title('Holonomy Phase vs Cycle Length', fontsize=14, weight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.legend()

    # Phase vs 1/n (check linearity)
    ax2.plot(inv_n, phases_over_pi, 'ro-', markersize=8, linewidth=2)
    ax2.plot(inv_n, a*np.array(inv_n) + b, 'b--', linewidth=2,
            label=f'Fit: {a:.2f}/n + {b:.2f}')
    ax2.set_xlabel('1/n', fontsize=12)
    ax2.set_ylabel('Phase / π', fontsize=12)
    ax2.set_title('Phase Scaling Test', fontsize=14, weight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend()

    plt.tight_layout()
    plt.savefig('holonomy_phase_pattern.png', dpi=150, bbox_inches='tight')
    print("\n✓ Visualization saved: holonomy_phase_pattern.png")

    print()
    print("=" * 70)

if __name__ == "__main__":
    main()
