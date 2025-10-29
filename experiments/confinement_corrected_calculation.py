"""
Confinement Corrected: Open vs Closed Energy
=============================================

The issue: Weakening reciprocal ≠ removing it (still closed, just weaker)

CORRECT test:
- Closed: q ↔ q̄ (bidirectional)
- Open: q → q̄ only (unidirectional, no back-link)

Measure R for each.
Compute energy difference.

This is the REAL confinement energy (cost to go from closed to open).

Author: Anonymous Research Network, Berkeley CA
Date: October 2024
"""

import numpy as np
import matplotlib.pyplot as plt

def build_meson_closed():
    """
    Closed q-q̄ system (bidirectional link)
    """
    n = 2  # Just q and q̄

    D = np.zeros((n,n), dtype=complex)

    # q → q̄
    D[1, 0] = 1.0
    # q̄ → q (RECIPROCAL)
    D[0, 1] = 1.0

    # Normalize
    for j in range(n):
        s = np.sum(np.abs(D[:,j]))
        if s > 0:
            D[:,j] /= s

    box = np.ones((n,n), dtype=complex) / n

    nabla = D @ box - box @ D
    R = nabla @ nabla

    return D, nabla, R

def build_meson_open():
    """
    Open q-q̄ system (unidirectional only)
    """
    n = 2

    D = np.zeros((n,n), dtype=complex)

    # q → q̄ ONLY (no back-link)
    D[1, 0] = 1.0
    # NO: D[0,1] = 0 (this is the breaking)

    # Normalize
    for j in range(n):
        s = np.sum(np.abs(D[:,j]))
        if s > 0:
            D[:,j] /= s

    box = np.ones((n,n), dtype=complex) / n

    nabla = D @ box - box @ D
    R = nabla @ nabla

    return D, nabla, R

def main():
    print("=" * 70)
    print("CONFINEMENT: Closed vs Open Energy Difference")
    print("=" * 70)
    print()

    # Closed (bound hadron)
    print("CLOSED SYSTEM (q ↔ q̄, reciprocal):")
    D_closed, nabla_closed, R_closed = build_meson_closed()
    R_closed_norm = np.linalg.norm(R_closed)
    nabla_closed_norm = np.linalg.norm(nabla_closed)

    print(f"  ||∇|| = {nabla_closed_norm:.10f}")
    print(f"  ||R|| = {R_closed_norm:.10f}")
    print()

    # Open (free quarks - forbidden)
    print("OPEN SYSTEM (q → q̄ only, no reciprocal):")
    D_open, nabla_open, R_open = build_meson_open()
    R_open_norm = np.linalg.norm(R_open)
    nabla_open_norm = np.linalg.norm(nabla_open)

    print(f"  ||∇|| = {nabla_open_norm:.10f}")
    print(f"  ||R|| = {R_open_norm:.10f}")
    print()

    # Energy difference
    print("=" * 70)
    print("CONFINEMENT ENERGY")
    print("=" * 70)
    print()

    E_closed = R_closed_norm  # Energy ~ R (curvature)
    E_open = R_open_norm

    Delta_E = E_open - E_closed

    print(f"E_closed (bound state): {E_closed:.10f}")
    print(f"E_open (free quarks):   {E_open:.10f}")
    print(f"ΔE = E_open - E_closed: {Delta_E:.10f}")
    print()

    if Delta_E > 0:
        print("✓ OPEN STATE HAS HIGHER ENERGY (R≠0 > R=0)")
        print()
        print("  Interpretation:")
        print("    Closed (R=0) is ground state (stable)")
        print("    Open (R≠0) costs energy (unstable)")
        print()
        print(f"  Energy cost to open: ΔE = {Delta_E:.6f} (in natural units)")
        print()
        print("  For infinite separation:")
        print("    Would need: Remove reciprocal completely")
        print("    Cost: Finite ΔE in 2-node model")
        print("    But: In QCD with gluons → ΔE → ∞ (string formation)")
    else:
        print("⚠️  Closed and open have same energy (unexpected)")

    # The issue
    print("\n" + "=" * 70)
    print("THE ISSUE WITH 2-NODE MODEL")
    print("=" * 70)
    print()
    print("2-node network is TOO SIMPLE:")
    print("  - Even 'open' (q→q̄) still has path back via vacuum")
    print("  - Need: Model with actual spatial separation")
    print("  - Or: Include gluon field (mediates at distance)")
    print()
    print("NEXT: Build realistic model with:")
    print("  - Spatial lattice (nodes at positions)")
    print("  - Distance-dependent coupling")
    print("  - Gluon flux tube between quarks")
    print()
    print("=" * 70)

if __name__ == "__main__":
    main()
