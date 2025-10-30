#!/usr/bin/env python3
"""
Prediction 3: Sensitivity Analysis

This script extends the original `prediction_3_REAL_numpy.py` to analyze
the sensitivity of the final correlation to the choice of accuracy threshold.
"""

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import List, Callable
from scipy.stats import pearsonr

# --- All the MLP and Task code from the original file is assumed to be here ---
# For brevity, we will copy it without displaying it.

def sigmoid(x):
    return 1 / (1 + np.exp(-np.clip(x, -500, 500)))

def relu(x):
    return np.maximum(0, x)

def softmax(x):
    exp_x = np.exp(x - np.max(x, axis=1, keepdims=True))
    return exp_x / np.sum(exp_x, axis=1, keepdims=True)


class MLPClassifier:
    def __init__(self, input_dim: int, output_dim: int, depth: int, width: int = 64):
        self.input_dim = input_dim
        self.output_dim = output_dim
        self.depth = depth
        self.width = width
        self.weights = []
        self.biases = []
        if depth == 0:
            self.weights.append(np.random.randn(input_dim, output_dim) * 0.1)
            self.biases.append(np.zeros(output_dim))
        else:
            self.weights.append(np.random.randn(input_dim, width) * np.sqrt(2/input_dim))
            self.biases.append(np.zeros(width))
            for _ in range(depth - 1):
                self.weights.append(np.random.randn(width, width) * np.sqrt(2/width))
                self.biases.append(np.zeros(width))
            self.weights.append(np.random.randn(width, output_dim) * np.sqrt(2/width))
            self.biases.append(np.zeros(output_dim))

    def forward(self, X, return_activations=False):
        activations = [X]
        h = X
        for i, (W, b) in enumerate(zip(self.weights, self.biases)):
            z = h @ W + b
            if i < len(self.weights) - 1:
                h = relu(z)
            else:
                h = z
            activations.append(h)
        if return_activations:
            return h, activations
        return h

    def train(self, X_train, y_train, X_test, y_test,
              epochs=200, lr=0.01, batch_size=32, patience=20, verbose=False):
        n_samples = X_train.shape[0]
        best_accuracy = 0
        patience_counter = 0
        for epoch in range(epochs):
            indices = np.random.permutation(n_samples)
            X_shuffled = X_train[indices]
            y_shuffled = y_train[indices]
            for i in range(0, n_samples, batch_size):
                X_batch = X_shuffled[i:i+batch_size]
                y_batch = y_shuffled[i:i+batch_size]
                logits, activations = self.forward(X_batch, return_activations=True)
                probs = softmax(logits)
                grad_logits = probs.copy()
                grad_logits[range(len(y_batch)), y_batch] -= 1
                grad_logits /= len(y_batch)
                gradients_W = []
                gradients_b = []
                for layer in range(len(self.weights) - 1, -1, -1):
                    grad_W = activations[layer].T @ grad_logits
                    grad_b = np.sum(grad_logits, axis=0)
                    gradients_W.insert(0, grad_W)
                    gradients_b.insert(0, grad_b)
                    if layer > 0:
                        grad_h = grad_logits @ self.weights[layer].T
                        grad_logits = grad_h * (activations[layer] > 0)
                for layer in range(len(self.weights)):
                    self.weights[layer] -= lr * gradients_W[layer]
                    self.biases[layer] -= lr * gradients_b[layer]
            test_acc = self.accuracy(X_test, y_test)
            if test_acc > best_accuracy:
                best_accuracy = test_acc
                patience_counter = 0
            else:
                patience_counter += 1
            if patience_counter >= patience:
                break
        return best_accuracy

    def predict(self, X):
        logits = self.forward(X)
        return np.argmax(logits, axis=1)

    def accuracy(self, X, y):
        predictions = self.predict(X)
        return np.mean(predictions == y)

@dataclass
class Task:
    name: str
    spectral_page: int
    input_dim: int
    output_dim: int
    generate_data: Callable
    description: str

def generate_xor(n_samples=1000):
    X = np.random.randint(0, 2, (n_samples, 2)).astype(float)
    y = (X[:, 0] != X[:, 1]).astype(int)
    return X, y

def generate_parity(n_samples=1000, n_bits=4):
    X = np.random.randint(0, 2, (n_samples, n_bits)).astype(float)
    y = (X.sum(axis=1) % 2).astype(int)
    return X, y

def generate_nested_xor(n_samples=1000):
    X = np.random.randint(0, 2, (n_samples, 4)).astype(float)
    xor1 = (X[:, 0] != X[:, 1]).astype(int)
    xor2 = (X[:, 2] != X[:, 3]).astype(int)
    y = (xor1 != xor2).astype(int)
    return X, y

def generate_simple(n_samples=1000):
    X = np.random.randn(n_samples, 4)
    y = (X[:, 0] + X[:, 1] > 0).astype(int)
    return X, y

def generate_three_xor(n_samples=1000):
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

@dataclass
class ExperimentResult:
    task_name: str
    spectral_page_theory: int
    depths_tested: List[int]
    mean_accuracies: List[float]

# =============================================================================
# MODIFIED ANALYSIS SCRIPT
# =============================================================================

def get_min_depth_for_threshold(result: ExperimentResult, threshold: float, max_depth: int):
    """Calculates minimum depth to achieve a given accuracy threshold."""
    for d, acc in zip(result.depths_tested, result.mean_accuracies):
        if acc >= threshold:
            return d
    return max_depth

def run_full_experiment(max_depth=4, n_trials=5, verbose=False):
    """Runs the experiment for all tasks and returns raw results."""
    results = []
    print("Running base experiment across all tasks...")
    for i, task in enumerate(TASKS):
        if verbose:
            print(f"  Task {i+1}/{len(TASKS)}: {task.name}...")
        
        depths = list(range(max_depth + 1))
        mean_accs = []

        for depth in depths:
            # Using a slightly higher number of trials for more stable averages
            accuracies = []
            for trial in range(n_trials):
                X_train, y_train = task.generate_data(1500)
                X_test, y_test = task.generate_data(500)
                model = MLPClassifier(task.input_dim, task.output_dim, depth, width=64)
                best_acc = model.train(X_train, y_train, X_test, y_test, verbose=False)
                accuracies.append(best_acc)
            mean_accs.append(np.mean(accuracies))

        results.append(ExperimentResult(
            task_name=task.name,
            spectral_page_theory=task.spectral_page,
            depths_tested=depths,
            mean_accuracies=mean_accs
        ))
    print("...experiment complete.")
    return results

def perform_sensitivity_analysis(raw_results, max_depth=4):
    """
    Analyzes the correlation between theory and empirical depth
    across a range of accuracy thresholds.
    """
    print("Performing sensitivity analysis on accuracy threshold...")
    thresholds = np.arange(0.75, 0.96, 0.01)
    p_values = []
    correlations = []
    
    predicted_pages = [r.spectral_page_theory for r in raw_results]

    for threshold in thresholds:
        empirical_depths = [get_min_depth_for_threshold(r, threshold, max_depth) for r in raw_results]
        r_pearson, p_pearson = pearsonr(predicted_pages, empirical_depths)
        p_values.append(p_pearson)
        correlations.append(r_pearson)

    return thresholds, correlations, p_values

def plot_sensitivity_analysis(thresholds, correlations, p_values):
    """Plots the results of the sensitivity analysis."""
    fig, ax1 = plt.subplots(figsize=(10, 6))

    # Plot correlation
    color = 'tab:blue'
    ax1.set_xlabel('Accuracy Threshold to Define "Solved"', fontsize=12, fontweight='bold')
    ax1.set_ylabel('Pearson Correlation (r)', color=color, fontsize=12, fontweight='bold')
    ax1.plot(thresholds, correlations, color=color, marker='o', label='Pearson Correlation')
    ax1.tick_params(axis='y', labelcolor=color)
    ax1.grid(True, alpha=0.3)

    # Plot p-value on a second y-axis
    ax2 = ax1.twinx()
    color = 'tab:red'
    ax2.set_ylabel('p-value', color=color, fontsize=12, fontweight='bold')
    ax2.plot(thresholds, p_values, color=color, marker='x', linestyle=':', label='p-value')
    ax2.axhline(0.05, color='gray', linestyle='--', label='p=0.05 Significance Level')
    ax2.tick_params(axis='y', labelcolor=color)
    ax2.set_ylim([-0.01, max(0.2, np.max(p_values) * 1.1)]) # Ensure 0.05 line is visible

    fig.suptitle('Sensitivity Analysis of Prediction 3', fontsize=16, fontweight='bold')
    ax1.set_title('Correlation Robustness to Accuracy Threshold (N=6 tasks)')
    fig.legend(loc="upper right", bbox_to_anchor=(0.9, 0.9))
    plt.tight_layout(rect=[0, 0, 1, 0.96])
    
    output_filename = 'prediction_3_sensitivity_analysis_results.png'
    plt.savefig(output_filename, dpi=300)
    print(f"\n📊 Sensitivity analysis plot saved to {output_filename}")
    plt.close()


def main():
    # First, run the base experiment to get the raw accuracy data for each depth
    # We increase n_trials to 5 for more stable results.
    raw_results = run_full_experiment(max_depth=4, n_trials=5, verbose=True)
    
    # Now, perform the sensitivity analysis on these results
    thresholds, correlations, p_values = perform_sensitivity_analysis(raw_results, max_depth=4)
    
    # Plot the outcome of the sensitivity analysis
    plot_sensitivity_analysis(thresholds, correlations, p_values)

    # Report the p-value at the original 85% threshold
    original_threshold_idx = np.where(np.isclose(thresholds, 0.85))[0][0]
    p_at_85 = p_values[original_threshold_idx]
    r_at_85 = correlations[original_threshold_idx]
    
    print("\n---")
    print(f"At original 85% threshold: r = {r_at_85:.4f}, p = {p_at_85:.6f}")
    if p_at_85 < 0.05:
        print("Result is statistically significant at the 85% threshold.")
    else:
        print("Result is NOT statistically significant at the 85% threshold.")
    print("---")


if __name__ == '__main__':
    main()
