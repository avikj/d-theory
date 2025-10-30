
"""
Cycle Breaking Energy Spectrum
==============================

This experiment directly tests the core axiom of Cycle Physics: that breaking a
closed cycle costs energy, and this energy corresponds to the emergence of
non-zero curvature R.

Method:
1.  Construct a closed, reciprocal n-cycle (representing vacuum/bound state).
2.  Gradually weaken the closing link from 1 (fully closed) to 0 (fully open).
3.  At each step, compute the norm of the curvature, ||R||, which is proportional
    to the system's energy.
4.  Plot Energy (||R||) vs. Link Strength (a measure of openness).

Expected Result:
-   Link strength = 1 (closed) ==> ||R|| = 0 (zero energy ground state).
-   As link strength -> 0 (opening) ==> ||R|| > 0 (energy increases).
-   The resulting curve is the energy spectrum of cycle breaking.
"""

import numpy as np
import matplotlib.pyplot as plt

def build_cycle(n_nodes, link_strength):
    """Builds an n-cycle with one link having a variable strength."""
    D = np.zeros((n_nodes, n_nodes))

    # Build the main chain
    for i in range(n_nodes - 1):
        D[i+1, i] = 1.0  # Forward link

    # Add the closing link with variable strength
    D[0, n_nodes-1] = link_strength

    # Normalize to be column-stochastic
    for j in range(n_nodes):
        col_sum = np.sum(D[:, j])
        if col_sum > 0:
            D[:, j] /= col_sum

    return D

def compute_curvature(D):
    """Computes the curvature R for a given distinction matrix D."""
    n = D.shape[0]
    box = np.ones((n, n)) / n
    nabla = D @ box - box @ D
    R = nabla @ nabla
    return np.linalg.norm(R)

def run_experiment():
    """Runs the cycle breaking experiment."""
    n_nodes = 12  # A 12-cycle, mirroring the 12-fold resonance
    link_strengths = np.linspace(0, 1, 101)  # From fully open to fully closed
    energies = []

    for strength in link_strengths:
        D = build_cycle(n_nodes, strength)
        energy = compute_curvature(D)
        energies.append(energy)

    return link_strengths, energies

def plot_results(strengths, energies):
    """Plots the energy spectrum."""
    plt.style.use('seaborn-v0_8-whitegrid')
    fig, ax = plt.subplots(figsize=(10, 6))

    ax.plot(strengths, energies, lw=2, color='purple')

    ax.set_xlabel('Link Strength (α)', fontsize=12, fontweight='bold')
    ax.set_ylabel('Energy ∝ ||R||', fontsize=12, fontweight='bold')
    ax.set_title('Energy Spectrum of Cycle Breaking', fontsize=16, fontweight='bold')
    ax.text(0.5, 0.95, f'N = {len(strengths)-1} steps, {len(energies)} energies calculated', transform=ax.transAxes, ha='center', va='top', style='italic')

    # Annotations
    ax.axvline(1.0, color='green', linestyle='--', label='Fully Closed (α=1, R=0)')
    ax.axvline(0.0, color='red', linestyle='--', label='Fully Open (α=0, R>0)')
    ax.text(0.98, 0.1, 'Vacuum State\n(Bound / Confined)', transform=ax.transAxes, ha='right', color='green')
    ax.text(0.02, 0.1, 'Matter State\n(Free / Deconfined)', transform=ax.transAxes, ha='left', color='red')

    ax.legend()
    plt.tight_layout()
    plt.savefig('cycle_breaking_energy_spectrum.png', dpi=300)
    print('Plot saved to cycle_breaking_energy_spectrum.png')

if __name__ == '__main__':
    print('Running Cycle Breaking Energy Spectrum experiment...')
    strengths, energies = run_experiment()
    plot_results(strengths, energies)
    print('Experiment complete.')
