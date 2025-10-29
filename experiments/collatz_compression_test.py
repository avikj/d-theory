#!/usr/bin/env python3
"""
Collatz Compression Test: Are trajectories incompressible?

Tests whether Collatz trajectories have high Kolmogorov complexity
(incompressible) as predicted by error-correction theory.

If trajectories are incompressible, that supports the claim that
witness complexity K_W(Collatz) exceeds theory capacity.
"""

import numpy as np
import gzip
import bz2
import zlib
from collections import Counter
import matplotlib.pyplot as plt


def collatz_trajectory(n, max_steps=10000):
    """Compute Collatz trajectory until reaching 1"""
    trajectory = [n]
    current = n
    steps = 0

    while current != 1 and steps < max_steps:
        if current % 2 == 0:
            current = current // 2
        else:
            current = 3 * current + 1
        trajectory.append(current)
        steps += 1

    return trajectory


def trajectory_to_bytes(trajectory):
    """Convert trajectory to byte string"""
    # Simple encoding: each number as 8 bytes (int64)
    return np.array(trajectory, dtype=np.int64).tobytes()


def compress_data(data, method='gzip'):
    """Compress byte data using various algorithms"""
    if method == 'gzip':
        return gzip.compress(data)
    elif method == 'bz2':
        return bz2.compress(data)
    elif method == 'zlib':
        return zlib.compress(data)
    else:
        raise ValueError(f"Unknown method: {method}")


def compression_ratio(original, compressed):
    """Ratio of compressed to original size"""
    return len(compressed) / len(original)


def entropy_estimate(trajectory):
    """Estimate Shannon entropy of trajectory"""
    # Compute mod 10 distribution (rough measure)
    mods = [x % 10 for x in trajectory]
    counts = Counter(mods)
    total = len(mods)
    probs = [counts[i] / total for i in range(10)]

    # Shannon entropy
    H = -sum(p * np.log2(p) if p > 0 else 0 for p in probs)
    return H


def test_collatz_compression():
    """Test compression of Collatz trajectories"""

    print("="*70)
    print("COLLATZ COMPRESSION TEST")
    print("="*70)
    print("\nHypothesis: Collatz trajectories are incompressible")
    print("(High Kolmogorov complexity → K_W(Collatz) large)")
    print("\nIf true: Compression ratio → 1 (no compression)")
    print("If false: Compression ratio << 1 (pattern found)")
    print("="*70)

    # Test various starting values
    test_values = [
        27,      # Famous: long trajectory
        31,      # Another long one
        127,     # Larger
        255,     # Power of 2 minus 1
        1000,    # Round number
        2**16-1, # Large
        999999,  # Near million
        123456,  # Random-looking
    ]

    results = []

    for n in test_values:
        trajectory = collatz_trajectory(n)
        traj_bytes = trajectory_to_bytes(trajectory)

        # Try different compression algorithms
        gzip_comp = compress_data(traj_bytes, 'gzip')
        bz2_comp = compress_data(traj_bytes, 'bz2')
        zlib_comp = compress_data(traj_bytes, 'zlib')

        # Compute ratios
        ratio_gzip = compression_ratio(traj_bytes, gzip_comp)
        ratio_bz2 = compression_ratio(traj_bytes, bz2_comp)
        ratio_zlib = compression_ratio(traj_bytes, zlib_comp)

        # Entropy
        H = entropy_estimate(trajectory)

        results.append({
            'n': n,
            'length': len(trajectory),
            'original_bytes': len(traj_bytes),
            'gzip': ratio_gzip,
            'bz2': ratio_bz2,
            'zlib': ratio_zlib,
            'entropy': H
        })

        print(f"\nn = {n:>7d}:")
        print(f"  Trajectory length: {len(trajectory):>5d} steps")
        print(f"  Original size: {len(traj_bytes):>7d} bytes")
        print(f"  Compression ratios:")
        print(f"    gzip: {ratio_gzip:.4f}")
        print(f"    bz2:  {ratio_bz2:.4f}")
        print(f"    zlib: {ratio_zlib:.4f}")
        print(f"  Shannon entropy (mod 10): {H:.3f} bits")
        print(f"  Best compression: {min(ratio_gzip, ratio_bz2, ratio_zlib):.4f}")

    # Analysis
    print("\n" + "="*70)
    print("STATISTICAL ANALYSIS")
    print("="*70)

    avg_gzip = np.mean([r['gzip'] for r in results])
    avg_bz2 = np.mean([r['bz2'] for r in results])
    avg_zlib = np.mean([r['zlib'] for r in results])
    avg_entropy = np.mean([r['entropy'] for r in results])

    print(f"\nAverage compression ratios:")
    print(f"  gzip: {avg_gzip:.4f}")
    print(f"  bz2:  {avg_bz2:.4f}")
    print(f"  zlib: {avg_zlib:.4f}")
    print(f"\nAverage Shannon entropy: {avg_entropy:.3f} bits (max 10 for uniform)")

    # Interpretation
    print("\n" + "="*70)
    print("INTERPRETATION")
    print("="*70)

    best_ratio = min(avg_gzip, avg_bz2, avg_zlib)

    if best_ratio > 0.8:
        print(f"\n✅ INCOMPRESSIBLE (ratio = {best_ratio:.3f} > 0.8)")
        print("   Trajectories have high Kolmogorov complexity")
        print("   Supports: K_W(Collatz) large → unprovability hypothesis")
    elif best_ratio > 0.5:
        print(f"\n⚠️  MODERATE COMPRESSION (ratio = {best_ratio:.3f})")
        print("   Some pattern detected but significant complexity remains")
    else:
        print(f"\n❌ HIGHLY COMPRESSIBLE (ratio = {best_ratio:.3f} < 0.5)")
        print("   Strong patterns found")
        print("   Challenges: High K_W hypothesis")

    # Comparison to random data
    print("\n" + "="*70)
    print("COMPARISON TO RANDOM DATA")
    print("="*70)

    # Generate random sequence of same length
    random_traj = np.random.randint(1, 1000000, size=500)
    random_bytes = random_traj.tobytes()
    random_comp = compress_data(random_bytes, 'gzip')
    random_ratio = compression_ratio(random_bytes, random_comp)

    print(f"\nRandom trajectory compression: {random_ratio:.4f}")
    print(f"Collatz average compression: {avg_gzip:.4f}")
    print(f"Difference: {abs(random_ratio - avg_gzip):.4f}")

    if abs(random_ratio - avg_gzip) < 0.1:
        print("\n→ Collatz trajectories similar to random (incompressible)")
    else:
        print(f"\n→ Collatz trajectories {'more' if avg_gzip < random_ratio else 'less'} compressible than random")

    # Plot
    plot_results(results)

    return results


def plot_results(results):
    """Visualize compression results"""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Plot 1: Compression ratios
    n_values = [r['n'] for r in results]
    gzip_ratios = [r['gzip'] for r in results]
    bz2_ratios = [r['bz2'] for r in results]
    zlib_ratios = [r['zlib'] for r in results]

    x = np.arange(len(n_values))
    width = 0.25

    ax1.bar(x - width, gzip_ratios, width, label='gzip', alpha=0.8)
    ax1.bar(x, bz2_ratios, width, label='bz2', alpha=0.8)
    ax1.bar(x + width, zlib_ratios, width, label='zlib', alpha=0.8)

    ax1.axhline(1.0, color='red', linestyle='--', alpha=0.5, label='No compression')
    ax1.axhline(0.5, color='green', linestyle='--', alpha=0.5, label='50% compression')

    ax1.set_xlabel('Starting value n', fontweight='bold')
    ax1.set_ylabel('Compression ratio', fontweight='bold')
    ax1.set_title('Collatz Trajectory Compression', fontweight='bold', fontsize=14)
    ax1.set_xticks(x)
    ax1.set_xticklabels([f"{r['n']}" for r in results], rotation=45, ha='right')
    ax1.legend()
    ax1.grid(True, alpha=0.3, axis='y')

    # Plot 2: Trajectory length vs compression
    lengths = [r['length'] for r in results]
    best_ratios = [min(r['gzip'], r['bz2'], r['zlib']) for r in results]

    ax2.scatter(lengths, best_ratios, s=100, alpha=0.7, color='steelblue')
    ax2.axhline(1.0, color='red', linestyle='--', alpha=0.5)
    ax2.set_xlabel('Trajectory length (steps)', fontweight='bold')
    ax2.set_ylabel('Best compression ratio', fontweight='bold')
    ax2.set_title('Length vs Compressibility', fontweight='bold', fontsize=14)
    ax2.grid(True, alpha=0.3)

    # Add annotations
    for r in results:
        best_r = min(r['gzip'], r['bz2'], r['zlib'])
        ax2.annotate(str(r['n']), (r['length'], best_r),
                    fontsize=8, alpha=0.7, xytext=(3, 3),
                    textcoords='offset points')

    plt.tight_layout()
    plt.savefig('collatz_compression_results.png', dpi=300, bbox_inches='tight')
    print(f"\n📊 Plot saved: collatz_compression_results.png")
    plt.close()


if __name__ == '__main__':
    results = test_collatz_compression()

    print("\n" + "="*70)
    print("CONCLUSION")
    print("="*70)
    print("\nCollatz trajectories tested for compressibility.")
    print("If incompressible → high K complexity → supports unprovability")
    print("If compressible → pattern exists → challenges framework")
    print("\nResults reveal actual information content of Collatz dynamics.")
