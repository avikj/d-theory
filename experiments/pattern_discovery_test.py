#!/usr/bin/env python3
"""
Pattern Discovery: What structure do neural networks find?

Train networks on different sequences and see what depth they need.
This tests whether "hidden structure" correlates with required depth.
"""

import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import pearsonr


class SimpleNN:
    """Minimal network for sequence prediction"""

    def __init__(self, input_dim, depth, width=32):
        self.depth = depth
        self.layers = []

        # Build layers
        dims = [input_dim] + [width] * depth + [1]
        for i in range(len(dims) - 1):
            W = np.random.randn(dims[i], dims[i+1]) * np.sqrt(2/dims[i])
            b = np.zeros(dims[i+1])
            self.layers.append((W, b))

    def forward(self, x):
        h = x
        for i, (W, b) in enumerate(self.layers):
            h = h @ W + b
            if i < len(self.layers) - 1:  # ReLU except last layer
                h = np.maximum(0, h)
        return h

    def train(self, X, y, epochs=500, lr=0.01):
        """Simple gradient descent"""
        best_loss = float('inf')
        patience = 0

        for epoch in range(epochs):
            # Forward
            pred = self.forward(X)
            loss = np.mean((pred - y.reshape(-1, 1))**2)

            # Backward (simplified - just output layer for speed)
            grad_out = 2 * (pred - y.reshape(-1, 1)) / len(X)

            # Update last layer only (simplified)
            W, b = self.layers[-1]
            if self.depth > 0:
                h = X
                for W_i, b_i in self.layers[:-1]:
                    h = np.maximum(0, h @ W_i + b_i)
            else:
                h = X

            grad_W = h.T @ grad_out
            grad_b = np.sum(grad_out, axis=0)

            self.layers[-1] = (W - lr * grad_W, b - lr * grad_b)

            if loss < best_loss:
                best_loss = loss
                patience = 0
            else:
                patience += 1

            if patience > 50:
                break

        return best_loss


def generate_sequence(seq_type, n=100):
    """Generate different types of sequences"""

    if seq_type == 'linear':
        # Simple: f(x) = 2x + 1
        x = np.arange(n)
        y = 2 * x + 1
        complexity = 1

    elif seq_type == 'quadratic':
        # Quadratic: f(x) = x²
        x = np.arange(n)
        y = x ** 2
        complexity = 2

    elif seq_type == 'fibonacci':
        # Fibonacci: depth-2 recursion
        fib = [1, 1]
        for i in range(2, n):
            fib.append(fib[-1] + fib[-2])
        x = np.arange(n)
        y = np.array(fib)
        complexity = 2

    elif seq_type == 'collatz_lengths':
        # Collatz stopping times: irregular
        x = np.arange(1, n+1)
        y = np.array([len(collatz_trajectory(i)) for i in x])
        complexity = 3  # Predicted

    elif seq_type == 'primes':
        # Nth prime: irregular
        primes = []
        num = 2
        while len(primes) < n:
            is_prime = all(num % p != 0 for p in primes if p * p <= num)
            if is_prime or num == 2:
                primes.append(num)
            num += 1
        x = np.arange(n)
        y = np.array(primes)
        complexity = 3

    elif seq_type == 'random':
        # Random: no pattern
        x = np.arange(n)
        y = np.random.randint(0, 1000, n)
        complexity = 5  # High (no structure)

    else:
        raise ValueError(f"Unknown sequence type: {seq_type}")

    # Normalize
    y = (y - np.mean(y)) / (np.std(y) + 1e-8)

    return x, y, complexity


def collatz_trajectory(n):
    """Compute Collatz trajectory"""
    steps = 0
    while n != 1 and steps < 10000:
        n = n // 2 if n % 2 == 0 else 3*n + 1
        steps += 1
    return list(range(steps + 1))


def test_sequence_learning(seq_type, max_depth=5, window=5):
    """Test what depth is needed to learn sequence"""

    x, y, expected_complexity = generate_sequence(seq_type, n=100)

    # Create windowed input (predict next from previous window)
    X = []
    Y = []
    for i in range(window, len(x)):
        X.append(y[i-window:i])
        Y.append(y[i])
    X = np.array(X)
    Y = np.array(Y)

    # Test different depths
    results = []
    for depth in range(max_depth + 1):
        losses = []
        for trial in range(3):  # Multiple trials
            model = SimpleNN(window, depth, width=32)
            loss = model.train(X, Y, epochs=500, lr=0.001)
            losses.append(loss)

        avg_loss = np.mean(losses)
        results.append(avg_loss)
        print(f"  Depth {depth}: Loss = {avg_loss:.6f}")

    # Find minimum depth where loss < threshold
    threshold = 0.01
    min_depth = max_depth
    for d, loss in enumerate(results):
        if loss < threshold:
            min_depth = d
            break

    return {
        'type': seq_type,
        'expected_complexity': expected_complexity,
        'min_depth': min_depth,
        'depths': list(range(max_depth + 1)),
        'losses': results
    }


def main():
    """Run pattern discovery experiment"""

    print("="*70)
    print("PATTERN DISCOVERY: What depth reveals what structure?")
    print("="*70)

    sequences = ['linear', 'quadratic', 'fibonacci', 'primes', 'collatz_lengths', 'random']

    all_results = []

    for seq_type in sequences:
        print(f"\n{'='*60}")
        print(f"Sequence: {seq_type.upper()}")
        print(f"{'='*60}")
        result = test_sequence_learning(seq_type, max_depth=5)
        all_results.append(result)
        print(f"→ Minimum depth: {result['min_depth']}")
        print(f"→ Expected complexity: {result['expected_complexity']}")

    # Analyze correlation
    print("\n" + "="*70)
    print("CORRELATION ANALYSIS")
    print("="*70)

    expected = [r['expected_complexity'] for r in all_results]
    empirical = [r['min_depth'] for r in all_results]

    r, p = pearsonr(expected, empirical)

    print(f"\nExpected complexity vs Empirical depth:")
    print(f"  Pearson r = {r:.4f}")
    print(f"  P-value = {p:.4f}")

    if p < 0.05:
        print(f"\n✅ SIGNIFICANT CORRELATION")
        print(f"   Sequence complexity predicts required depth")
    else:
        print(f"\n❌ NO SIGNIFICANT CORRELATION")

    # Results table
    print("\n" + "="*70)
    print("RESULTS")
    print("="*70)
    print(f"{'Sequence':<20} {'Expected':<12} {'Empirical':<12} {'Error':<8}")
    print("-"*52)
    for r in all_results:
        error = abs(r['expected_complexity'] - r['min_depth'])
        print(f"{r['type']:<20} {r['expected_complexity']:<12} {r['min_depth']:<12} {error:<8}")

    # Plot
    fig, ax = plt.subplots(figsize=(10, 6))

    for r in all_results:
        ax.plot(r['depths'], r['losses'], marker='o',
               label=f"{r['type']} (complexity={r['expected_complexity']})",
               alpha=0.7)

    ax.set_xlabel('Network Depth', fontweight='bold')
    ax.set_ylabel('Prediction Loss (MSE)', fontweight='bold')
    ax.set_title('Learning Curves: Different Sequence Types', fontweight='bold', fontsize=14)
    ax.set_yscale('log')
    ax.legend()
    ax.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig('pattern_discovery_results.png', dpi=300, bbox_inches='tight')
    print(f"\n📊 Plot saved: pattern_discovery_results.png")
    plt.close()


if __name__ == '__main__':
    main()
