#!/usr/bin/env python3
"""
Prediction 3: Neural Network Depth vs Spectral Page (NumPy Implementation)

REAL implementation using pure NumPy (no PyTorch dependency).
Tests whether minimum network depth correlates with spectral page.
"""

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import List, Tuple, Callable
from scipy.stats import pearsonr, spearmanr


# =============================================================================
# NEURAL NETWORK (Pure NumPy)
# =============================================================================

def sigmoid(x):
    return 1 / (1 + np.exp(-np.clip(x, -500, 500)))

def relu(x):
    return np.maximum(0, x)

def softmax(x):
    exp_x = np.exp(x - np.max(x, axis=1, keepdims=True))
    return exp_x / np.sum(exp_x, axis=1, keepdims=True)


class MLPClassifier:
    """Multi-layer perceptron with variable depth (NumPy implementation)"""

    def __init__(self, input_dim: int, output_dim: int, depth: int, width: int = 64):
        self.input_dim = input_dim
        self.output_dim = output_dim
        self.depth = depth
        self.width = width

        # Initialize weights
        self.weights = []
        self.biases = []

        if depth == 0:
            # Just linear (logistic regression)
            self.weights.append(np.random.randn(input_dim, output_dim) * 0.1)
            self.biases.append(np.zeros(output_dim))
        else:
            # Input layer
            self.weights.append(np.random.randn(input_dim, width) * np.sqrt(2/input_dim))
            self.biases.append(np.zeros(width))

            # Hidden layers
            for _ in range(depth - 1):
                self.weights.append(np.random.randn(width, width) * np.sqrt(2/width))
                self.biases.append(np.zeros(width))

            # Output layer
            self.weights.append(np.random.randn(width, output_dim) * np.sqrt(2/width))
            self.biases.append(np.zeros(output_dim))

    def forward(self, X, return_activations=False):
        """Forward pass"""
        activations = [X]
        h = X

        for i, (W, b) in enumerate(zip(self.weights, self.biases)):
            z = h @ W + b
            if i < len(self.weights) - 1:  # Hidden layers
                h = relu(z)
            else:  # Output layer
                h = z  # Raw logits
            activations.append(h)

        if return_activations:
            return h, activations
        return h

    def train(self, X_train, y_train, X_test, y_test,
              epochs=200, lr=0.01, batch_size=32, patience=20, verbose=False):
        """Train with SGD and early stopping"""
        n_samples = X_train.shape[0]
        best_accuracy = 0
        patience_counter = 0

        for epoch in range(epochs):
            # Shuffle
            indices = np.random.permutation(n_samples)
            X_shuffled = X_train[indices]
            y_shuffled = y_train[indices]

            # Mini-batch SGD
            for i in range(0, n_samples, batch_size):
                X_batch = X_shuffled[i:i+batch_size]
                y_batch = y_shuffled[i:i+batch_size]

                # Forward
                logits, activations = self.forward(X_batch, return_activations=True)
                probs = softmax(logits)

                # Cross-entropy loss gradient
                grad_logits = probs.copy()
                grad_logits[range(len(y_batch)), y_batch] -= 1
                grad_logits /= len(y_batch)

                # Backward
                gradients_W = []
                gradients_b = []

                for layer in range(len(self.weights) - 1, -1, -1):
                    # Gradient w.r.t weights and biases
                    grad_W = activations[layer].T @ grad_logits
                    grad_b = np.sum(grad_logits, axis=0)

                    gradients_W.insert(0, grad_W)
                    gradients_b.insert(0, grad_b)

                    if layer > 0:
                        # Backprop through ReLU
                        grad_h = grad_logits @ self.weights[layer].T
                        grad_logits = grad_h * (activations[layer] > 0)

                # Update weights
                for layer in range(len(self.weights)):
                    self.weights[layer] -= lr * gradients_W[layer]
                    self.biases[layer] -= lr * gradients_b[layer]

            # Evaluate on test set
            test_acc = self.accuracy(X_test, y_test)

            if test_acc > best_accuracy:
                best_accuracy = test_acc
                patience_counter = 0
            else:
                patience_counter += 1

            if verbose and epoch % 40 == 0:
                print(f"    Epoch {epoch:3d}: Test Acc = {test_acc:.4f}")

            if patience_counter >= patience:
                if verbose:
                    print(f"    Early stopping at epoch {epoch}")
                break

        return best_accuracy

    def predict(self, X):
        """Predict class labels"""
        logits = self.forward(X)
        return np.argmax(logits, axis=1)

    def accuracy(self, X, y):
        """Compute accuracy"""
        predictions = self.predict(X)
        return np.mean(predictions == y)


# =============================================================================
# TASK DEFINITIONS
# =============================================================================

@dataclass
class Task:
    name: str
    spectral_page: int
    input_dim: int
    output_dim: int
    generate_data: Callable
    description: str


def generate_xor(n_samples=1000):
    """XOR: Classic non-linearly separable"""
    X = np.random.randint(0, 2, (n_samples, 2)).astype(float)
    y = (X[:, 0] != X[:, 1]).astype(int)
    return X, y


def generate_parity(n_samples=1000, n_bits=4):
    """Parity: Count 1s modulo 2"""
    X = np.random.randint(0, 2, (n_samples, n_bits)).astype(float)
    y = (X.sum(axis=1) % 2).astype(int)
    return X, y


def generate_nested_xor(n_samples=1000):
    """Nested: (x1 XOR x2) XOR (x3 XOR x4)"""
    X = np.random.randint(0, 2, (n_samples, 4)).astype(float)
    xor1 = (X[:, 0] != X[:, 1]).astype(int)
    xor2 = (X[:, 2] != X[:, 3]).astype(int)
    y = (xor1 != xor2).astype(int)
    return X, y


def generate_simple(n_samples=1000):
    """Simple linear classification"""
    X = np.random.randn(n_samples, 4)
    y = (X[:, 0] + X[:, 1] > 0).astype(int)
    return X, y


def generate_three_xor(n_samples=1000):
    """Three-way composition: depth-3"""
    X = np.random.randint(0, 2, (n_samples, 8)).astype(float)
    xor1 = (X[:, 0] != X[:, 1]).astype(int)
    xor2 = (X[:, 2] != X[:, 3]).astype(int)
    xor3 = (X[:, 4] != X[:, 5]).astype(int)
    xor4 = (X[:, 6] != X[:, 7]).astype(int)
    temp1 = (xor1 != xor2).astype(int)
    temp2 = (xor3 != xor4).astype(int)
    y = (temp1 != temp2).astype(int)
    return X, y


TASKS = [
    Task("Linear", 1, 4, 2, generate_simple, "Linear separable → depth 1"),
    Task("XOR", 1, 2, 2, generate_xor, "Single non-linearity → depth 1"),
    Task("Nested-XOR", 2, 4, 2, generate_nested_xor, "Composition → depth 2"),
    Task("Parity-4", 2, 4, 2, lambda n: generate_parity(n, 4), "4-bit parity → depth 2"),
    Task("Parity-8", 2, 8, 2, lambda n: generate_parity(n, 8), "8-bit parity → depth 2"),
    Task("Triple-XOR", 3, 8, 2, generate_three_xor, "3-way composition → depth 3"),
]


# =============================================================================
# EXPERIMENT
# =============================================================================

@dataclass
class ExperimentResult:
    task_name: str
    spectral_page_theory: int
    min_depth_empirical: int
    depths_tested: List[int]
    mean_accuracies: List[float]
    std_accuracies: List[float]


def evaluate_depth(task, depth, n_trials=3, n_train=1500, n_test=500):
    """Evaluate network of given depth on task"""
    accuracies = []

    for trial in range(n_trials):
        X_train, y_train = task.generate_data(n_train)
        X_test, y_test = task.generate_data(n_test)

        model = MLPClassifier(task.input_dim, task.output_dim, depth, width=64)
        best_acc = model.train(X_train, y_train, X_test, y_test, verbose=False)
        accuracies.append(best_acc)

    return np.mean(accuracies), np.std(accuracies)


def run_experiment(task, max_depth=4, threshold=0.85, n_trials=3, verbose=True):
    """Run depth ablation study"""
    if verbose:
        print(f"\n{'='*60}")
        print(f"{task.name} (predicted page: {task.spectral_page})")
        print(f"{task.description}")
        print(f"{'='*60}")

    depths = list(range(max_depth + 1))
    mean_accs = []
    std_accs = []

    for depth in depths:
        mean, std = evaluate_depth(task, depth, n_trials)
        mean_accs.append(mean)
        std_accs.append(std)
        if verbose:
            print(f"  Depth {depth}: {mean:.3f} ± {std:.3f}")

    # Find minimum depth achieving threshold
    min_depth = max_depth
    for d, acc in zip(depths, mean_accs):
        if acc >= threshold:
            min_depth = d
            break

    if verbose:
        print(f"\n→ Min depth for {threshold*100}% acc: {min_depth}")
        print(f"→ Predicted: {task.spectral_page}")
        print(f"→ Error: {abs(min_depth - task.spectral_page)}")

    return ExperimentResult(
        task_name=task.name,
        spectral_page_theory=task.spectral_page,
        min_depth_empirical=min_depth,
        depths_tested=depths,
        mean_accuracies=mean_accs,
        std_accuracies=std_accs
    )


def analyze_results(results):
    predicted = [r.spectral_page_theory for r in results]
    empirical = [r.min_depth_empirical for r in results]

    r_pearson, p_pearson = pearsonr(predicted, empirical)
    r_spearman, p_spearman = spearmanr(predicted, empirical)
    mae = np.mean([abs(p - e) for p, e in zip(predicted, empirical)])

    return {
        'pearson_r': r_pearson, 'pearson_p': p_pearson,
        'spearman_r': r_spearman, 'spearman_p': p_spearman,
        'mae': mae, 'predicted': predicted, 'empirical': empirical
    }


def plot_results(results, stats):
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Scatter plot
    ax1.scatter(stats['predicted'], stats['empirical'], s=100, alpha=0.7, color='steelblue')
    min_v, max_v = 0, max(max(stats['predicted']), max(stats['empirical']))
    ax1.plot([min_v, max_v], [min_v, max_v], 'r--', label='Perfect', alpha=0.5, linewidth=2)

    ax1.set_xlabel('Predicted Spectral Page', fontsize=12, fontweight='bold')
    ax1.set_ylabel('Empirical Min Depth', fontsize=12, fontweight='bold')
    ax1.set_title('Prediction 3: Spectral Page vs Network Depth\n(REAL NumPy)',
                  fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    for r in results:
        ax1.annotate(r.task_name, (r.spectral_page_theory, r.min_depth_empirical),
                    fontsize=8, alpha=0.7, xytext=(5, 5), textcoords='offset points')

    ax1.text(0.05, 0.95,
             f'Pearson r = {stats["pearson_r"]:.3f} (p = {stats["pearson_p"]:.4f})\n'
             f'Spearman ρ = {stats["spearman_r"]:.3f} (p = {stats["spearman_p"]:.4f})\n'
             f'MAE = {stats["mae"]:.3f}',
             transform=ax1.transAxes, fontsize=10, va='top',
             bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

    # Depth curves
    for r in results:
        ax2.errorbar(r.depths_tested, r.mean_accuracies, yerr=r.std_accuracies,
                    marker='o', label=f"{r.task_name} (r={r.spectral_page_theory})",
                    alpha=0.7, capsize=3)

    ax2.axhline(0.85, color='red', linestyle='--', label='Threshold', alpha=0.5, linewidth=2)
    ax2.set_xlabel('Network Depth', fontsize=12, fontweight='bold')
    ax2.set_ylabel('Test Accuracy', fontsize=12, fontweight='bold')
    ax2.set_title('Accuracy vs Depth', fontsize=14, fontweight='bold')
    ax2.legend(fontsize=8, loc='lower right')
    ax2.grid(True, alpha=0.3)
    ax2.set_ylim([0, 1.05])

    plt.tight_layout()
    plt.savefig('prediction_3_REAL_numpy_results.png', dpi=300, bbox_inches='tight')
    print(f"\n📊 Plot saved: prediction_3_REAL_numpy_results.png")
    plt.close()


def main():
    print("="*70)
    print("PREDICTION 3: Network Depth ~ Spectral Page (REAL)")
    print("="*70)

    results = []
    for task in TASKS:
        result = run_experiment(task, max_depth=4, n_trials=3, verbose=True)
        results.append(result)

    print("\n" + "="*70)
    print("STATISTICAL ANALYSIS")
    print("="*70)

    stats = analyze_results(results)
    print(f"\nPearson:  r = {stats['pearson_r']:.4f}, p = {stats['pearson_p']:.6f}")
    print(f"Spearman: ρ = {stats['spearman_r']:.4f}, p = {stats['spearman_p']:.6f}")
    print(f"MAE: {stats['mae']:.3f} layers")

    if stats['pearson_p'] < 0.05:
        print(f"\n✅ SIGNIFICANT (p < 0.05): Prediction SUPPORTED")
    else:
        print(f"\n❌ NOT SIGNIFICANT (p ≥ 0.05): Prediction NOT SUPPORTED")

    print("\n" + "="*70)
    print("RESULTS")
    print("="*70)
    print(f"{'Task':<15} {'Predicted':<10} {'Empirical':<10} {'Error':<8}")
    print("-"*45)
    for r in results:
        print(f"{r.task_name:<15} {r.spectral_page_theory:<10} "
              f"{r.min_depth_empirical:<10} {abs(r.spectral_page_theory - r.min_depth_empirical):<8}")

    plot_results(results, stats)

    print("\n" + "="*70)
    print("COMPLETE: Real experiment with trained networks")
    print("="*70)


if __name__ == '__main__':
    main()
