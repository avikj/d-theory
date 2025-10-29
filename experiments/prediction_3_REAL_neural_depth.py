#!/usr/bin/env python3
"""
Prediction 3: Neural Network Depth vs Spectral Page (REAL IMPLEMENTATION)

Tests the hypothesis that minimum network depth correlates with spectral
sequence convergence page for the task's input space.

This is a REAL implementation using PyTorch, training actual networks.
"""

import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import Dataset, DataLoader
import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass
from typing import List, Tuple, Callable
from scipy.stats import pearsonr, spearmanr
import time


# =============================================================================
# TASK DEFINITIONS
# =============================================================================

@dataclass
class Task:
    """A learning task with theoretical spectral page prediction"""
    name: str
    spectral_page: int  # Theoretical prediction
    input_dim: int
    output_dim: int
    generate_data: Callable  # Function that generates (X, y) data
    description: str


def generate_xor(n_samples: int = 1000) -> Tuple[torch.Tensor, torch.Tensor]:
    """XOR: Classic non-linearly separable task"""
    X = torch.randint(0, 2, (n_samples, 2)).float()
    y = (X[:, 0] != X[:, 1]).long()  # XOR operation
    return X, y


def generate_parity(n_samples: int = 1000, n_bits: int = 8) -> Tuple[torch.Tensor, torch.Tensor]:
    """Parity: Count 1s modulo 2"""
    X = torch.randint(0, 2, (n_samples, n_bits)).float()
    y = (X.sum(dim=1) % 2).long()
    return X, y


def generate_nested_xor(n_samples: int = 1000) -> Tuple[torch.Tensor, torch.Tensor]:
    """Nested XOR: (x1 XOR x2) XOR (x3 XOR x4) - requires depth-2"""
    X = torch.randint(0, 2, (n_samples, 4)).float()
    xor1 = (X[:, 0] != X[:, 1]).long()
    xor2 = (X[:, 2] != X[:, 3]).long()
    y = (xor1 != xor2).long()
    return X, y


def generate_simple_classification(n_samples: int = 1000) -> Tuple[torch.Tensor, torch.Tensor]:
    """Simple linear classification - should need depth 1"""
    X = torch.randn(n_samples, 4)
    # Simple rule: if x1 + x2 > 0, class 1, else class 0
    y = (X[:, 0] + X[:, 1] > 0).long()
    return X, y


def generate_modular_arithmetic(n_samples: int = 1000) -> Tuple[torch.Tensor, torch.Tensor]:
    """Modular arithmetic: (a + b) mod 5 - requires structured computation"""
    # Represent numbers 0-4 as one-hot
    a = torch.randint(0, 5, (n_samples,))
    b = torch.randint(0, 5, (n_samples,))
    X = torch.zeros(n_samples, 10)
    X[range(n_samples), a] = 1
    X[range(n_samples), b + 5] = 1
    y = (a + b) % 5
    return X, y


# Task registry
TASKS = [
    Task(
        name="Simple Linear",
        spectral_page=1,
        input_dim=4,
        output_dim=2,
        generate_data=generate_simple_classification,
        description="Linear separable → depth 1"
    ),
    Task(
        name="XOR",
        spectral_page=1,
        input_dim=2,
        output_dim=2,
        generate_data=generate_xor,
        description="Single non-linearity → depth 1"
    ),
    Task(
        name="Nested XOR",
        spectral_page=2,
        input_dim=4,
        output_dim=2,
        generate_data=generate_nested_xor,
        description="Composition of XORs → depth 2"
    ),
    Task(
        name="Parity-4",
        spectral_page=2,
        input_dim=4,
        output_dim=2,
        generate_data=lambda n: generate_parity(n, n_bits=4),
        description="4-bit parity → depth 2"
    ),
    Task(
        name="Parity-8",
        spectral_page=2,
        input_dim=8,
        output_dim=2,
        generate_data=lambda n: generate_parity(n, n_bits=8),
        description="8-bit parity → depth 2"
    ),
    Task(
        name="Modular Add",
        spectral_page=2,
        input_dim=10,
        output_dim=5,
        generate_data=generate_modular_arithmetic,
        description="(a+b) mod 5 → depth 2 (group structure)"
    ),
]


# =============================================================================
# NEURAL NETWORK ARCHITECTURES
# =============================================================================

class MLPDepth(nn.Module):
    """Multi-layer perceptron with variable depth"""

    def __init__(self, input_dim: int, output_dim: int, depth: int, width: int = 128):
        """
        Args:
            input_dim: Input dimension
            output_dim: Output dimension (number of classes)
            depth: Number of hidden layers
            width: Width of each hidden layer
        """
        super().__init__()

        self.depth = depth
        layers = []

        if depth == 0:
            # Just linear layer (logistic regression)
            layers.append(nn.Linear(input_dim, output_dim))
        else:
            # Input layer
            layers.append(nn.Linear(input_dim, width))
            layers.append(nn.ReLU())

            # Hidden layers
            for _ in range(depth - 1):
                layers.append(nn.Linear(width, width))
                layers.append(nn.ReLU())

            # Output layer
            layers.append(nn.Linear(width, output_dim))

        self.network = nn.Sequential(*layers)

    def forward(self, x):
        return self.network(x)


# =============================================================================
# TRAINING PROCEDURE
# =============================================================================

def train_network(
    model: nn.Module,
    train_loader: DataLoader,
    test_loader: DataLoader,
    epochs: int = 100,
    lr: float = 0.01,
    patience: int = 10,
    verbose: bool = False
) -> Tuple[float, List[float]]:
    """
    Train network and return best test accuracy.

    Args:
        model: Neural network to train
        train_loader: Training data
        test_loader: Test data
        epochs: Maximum epochs
        lr: Learning rate
        patience: Early stopping patience
        verbose: Print progress

    Returns:
        best_accuracy: Best test accuracy achieved
        history: List of test accuracies per epoch
    """
    criterion = nn.CrossEntropyLoss()
    optimizer = optim.Adam(model.parameters(), lr=lr)

    best_accuracy = 0.0
    patience_counter = 0
    history = []

    for epoch in range(epochs):
        # Training
        model.train()
        train_loss = 0.0
        for X_batch, y_batch in train_loader:
            optimizer.zero_grad()
            outputs = model(X_batch)
            loss = criterion(outputs, y_batch)
            loss.backward()
            optimizer.step()
            train_loss += loss.item()

        # Evaluation
        model.eval()
        correct = 0
        total = 0
        with torch.no_grad():
            for X_batch, y_batch in test_loader:
                outputs = model(X_batch)
                _, predicted = torch.max(outputs, 1)
                total += y_batch.size(0)
                correct += (predicted == y_batch).sum().item()

        accuracy = correct / total
        history.append(accuracy)

        if accuracy > best_accuracy:
            best_accuracy = accuracy
            patience_counter = 0
        else:
            patience_counter += 1

        if verbose and epoch % 20 == 0:
            print(f"  Epoch {epoch:3d}: Train Loss = {train_loss/len(train_loader):.4f}, "
                  f"Test Acc = {accuracy:.4f}")

        # Early stopping
        if patience_counter >= patience:
            if verbose:
                print(f"  Early stopping at epoch {epoch}")
            break

    return best_accuracy, history


def evaluate_depth(
    task: Task,
    depth: int,
    n_trials: int = 3,
    n_train: int = 2000,
    n_test: int = 500,
    width: int = 128,
    verbose: bool = False
) -> Tuple[float, float]:
    """
    Evaluate network of given depth on task across multiple trials.

    Returns:
        mean_accuracy: Average test accuracy across trials
        std_accuracy: Standard deviation
    """
    accuracies = []

    for trial in range(n_trials):
        # Generate fresh data for each trial
        X_train, y_train = task.generate_data(n_train)
        X_test, y_test = task.generate_data(n_test)

        # Create dataloaders
        train_dataset = torch.utils.data.TensorDataset(X_train, y_train)
        test_dataset = torch.utils.data.TensorDataset(X_test, y_test)
        train_loader = DataLoader(train_dataset, batch_size=32, shuffle=True)
        test_loader = DataLoader(test_dataset, batch_size=32, shuffle=False)

        # Create and train model
        model = MLPDepth(task.input_dim, task.output_dim, depth, width)
        best_acc, _ = train_network(model, train_loader, test_loader, verbose=False)
        accuracies.append(best_acc)

    mean_acc = np.mean(accuracies)
    std_acc = np.std(accuracies)

    if verbose:
        print(f"  Depth {depth}: {mean_acc:.3f} ± {std_acc:.3f} "
              f"(trials: {[f'{a:.3f}' for a in accuracies]})")

    return mean_acc, std_acc


# =============================================================================
# EXPERIMENT RUNNER
# =============================================================================

@dataclass
class ExperimentResult:
    """Results for one task"""
    task_name: str
    spectral_page_theory: int
    min_depth_empirical: int
    depths_tested: List[int]
    mean_accuracies: List[float]
    std_accuracies: List[float]


def run_experiment(
    task: Task,
    max_depth: int = 5,
    accuracy_threshold: float = 0.90,
    n_trials: int = 3,
    verbose: bool = True
) -> ExperimentResult:
    """
    Run depth ablation study on a task.

    Tests depths 0, 1, 2, ..., max_depth and finds minimum depth
    achieving accuracy_threshold.
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"Task: {task.name} (predicted spectral page: {task.spectral_page})")
        print(f"Description: {task.description}")
        print(f"{'='*60}")

    depths = list(range(max_depth + 1))
    mean_accs = []
    std_accs = []

    for depth in depths:
        mean_acc, std_acc = evaluate_depth(task, depth, n_trials=n_trials, verbose=verbose)
        mean_accs.append(mean_acc)
        std_accs.append(std_acc)

    # Find minimum depth achieving threshold
    min_depth = max_depth  # Default if threshold never reached
    for d, acc in zip(depths, mean_accs):
        if acc >= accuracy_threshold:
            min_depth = d
            break

    if verbose:
        print(f"\n→ Minimum depth for {accuracy_threshold*100}% accuracy: {min_depth}")
        print(f"→ Theoretical prediction: {task.spectral_page}")
        print(f"→ Error: {abs(min_depth - task.spectral_page)}")

    return ExperimentResult(
        task_name=task.name,
        spectral_page_theory=task.spectral_page,
        min_depth_empirical=min_depth,
        depths_tested=depths,
        mean_accuracies=mean_accs,
        std_accuracies=std_accs
    )


# =============================================================================
# STATISTICAL ANALYSIS
# =============================================================================

def analyze_results(results: List[ExperimentResult]):
    """Compute correlation between predicted and empirical depths"""
    predicted = [r.spectral_page_theory for r in results]
    empirical = [r.min_depth_empirical for r in results]

    # Pearson correlation
    r_pearson, p_pearson = pearsonr(predicted, empirical)

    # Spearman correlation
    r_spearman, p_spearman = spearmanr(predicted, empirical)

    # Mean absolute error
    mae = np.mean([abs(p - e) for p, e in zip(predicted, empirical)])

    return {
        'pearson_r': r_pearson,
        'pearson_p': p_pearson,
        'spearman_r': r_spearman,
        'spearman_p': p_spearman,
        'mae': mae,
        'predicted': predicted,
        'empirical': empirical
    }


def plot_results(results: List[ExperimentResult], stats: dict, output_file: str):
    """Generate publication-quality plots"""
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))

    # Plot 1: Predicted vs Empirical
    ax1.scatter(stats['predicted'], stats['empirical'], s=100, alpha=0.7, color='steelblue')

    # Perfect correlation line
    min_val = min(min(stats['predicted']), min(stats['empirical']))
    max_val = max(max(stats['predicted']), max(stats['empirical']))
    ax1.plot([min_val, max_val], [min_val, max_val],
             'r--', label='Perfect correlation', alpha=0.5, linewidth=2)

    ax1.set_xlabel('Predicted Spectral Page', fontsize=12, fontweight='bold')
    ax1.set_ylabel('Empirical Minimum Depth', fontsize=12, fontweight='bold')
    ax1.set_title('Prediction 3: Spectral Page vs Neural Network Depth\n(REAL Implementation)',
                  fontsize=14, fontweight='bold')
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Add task labels
    for r in results:
        ax1.annotate(r.task_name,
                    (r.spectral_page_theory, r.min_depth_empirical),
                    fontsize=8, alpha=0.7, xytext=(5, 5),
                    textcoords='offset points')

    # Add stats
    ax1.text(0.05, 0.95,
             f'Pearson r = {stats["pearson_r"]:.3f} (p = {stats["pearson_p"]:.4f})\n'
             f'Spearman ρ = {stats["spearman_r"]:.3f} (p = {stats["spearman_p"]:.4f})\n'
             f'MAE = {stats["mae"]:.3f}',
             transform=ax1.transAxes, fontsize=10,
             verticalalignment='top', bbox=dict(boxstyle='round',
             facecolor='wheat', alpha=0.5))

    # Plot 2: Depth curves
    for result in results:
        ax2.errorbar(result.depths_tested, result.mean_accuracies,
                    yerr=result.std_accuracies, marker='o',
                    label=f"{result.task_name} (r={result.spectral_page_theory})",
                    alpha=0.7, capsize=3)

    ax2.axhline(0.90, color='red', linestyle='--',
               label='Threshold (90%)', alpha=0.5, linewidth=2)
    ax2.set_xlabel('Network Depth', fontsize=12, fontweight='bold')
    ax2.set_ylabel('Test Accuracy', fontsize=12, fontweight='bold')
    ax2.set_title('Accuracy vs Depth by Task', fontsize=14, fontweight='bold')
    ax2.legend(fontsize=8, loc='lower right')
    ax2.grid(True, alpha=0.3)
    ax2.set_ylim([0, 1.05])

    plt.tight_layout()
    plt.savefig(output_file, dpi=300, bbox_inches='tight')
    print(f"\n📊 Plot saved: {output_file}")
    plt.close()


# =============================================================================
# MAIN EXPERIMENT
# =============================================================================

def main():
    """Run complete experiment"""
    print("="*70)
    print("PREDICTION 3: Neural Network Depth ~ Spectral Convergence Page")
    print("REAL IMPLEMENTATION - Training actual PyTorch networks")
    print("="*70)

    print("\nHypothesis: Minimum network depth required for task T equals")
    print("spectral sequence convergence page r for input space structure.")
    print("\nNull Hypothesis: No correlation (r = 0, p > 0.05)")
    print("="*70)

    start_time = time.time()

    # Run experiments
    results = []
    for task in TASKS:
        result = run_experiment(task, max_depth=5, n_trials=3, verbose=True)
        results.append(result)

    # Analyze
    print("\n" + "="*70)
    print("STATISTICAL ANALYSIS")
    print("="*70)

    stats = analyze_results(results)

    print(f"\nPearson correlation:  r = {stats['pearson_r']:.4f}, "
          f"p = {stats['pearson_p']:.6f}")
    print(f"Spearman correlation: ρ = {stats['spearman_r']:.4f}, "
          f"p = {stats['spearman_p']:.6f}")
    print(f"Mean Absolute Error:  {stats['mae']:.3f} layers")

    # Interpret
    print("\n" + "="*70)
    print("INTERPRETATION")
    print("="*70)

    if stats['pearson_p'] < 0.05:
        print(f"\n✅ SIGNIFICANT CORRELATION (p = {stats['pearson_p']:.6f} < 0.05)")
        print(f"   Spectral page predicts network depth with r = {stats['pearson_r']:.3f}")
        print(f"   Prediction 3 is SUPPORTED by this experiment.")
    else:
        print(f"\n❌ NO SIGNIFICANT CORRELATION (p = {stats['pearson_p']:.6f} ≥ 0.05)")
        print(f"   Cannot reject null hypothesis.")
        print(f"   Prediction 3 is NOT SUPPORTED by this experiment.")

    if stats['mae'] < 1.0:
        print(f"\n   Average error: {stats['mae']:.2f} layers (< 1 layer)")
        print(f"   Spectral theory provides accurate depth prediction.")

    # Detailed results
    print("\n" + "="*70)
    print("DETAILED RESULTS")
    print("="*70)
    print(f"\n{'Task':<15} {'Predicted':<10} {'Empirical':<10} {'Error':<8}")
    print("-"*45)
    for r in results:
        error = abs(r.spectral_page_theory - r.min_depth_empirical)
        print(f"{r.task_name:<15} {r.spectral_page_theory:<10} "
              f"{r.min_depth_empirical:<10} {error:<8}")

    # Plot
    plot_results(results, stats, 'prediction_3_REAL_results.png')

    elapsed = time.time() - start_time
    print(f"\n⏱️  Total time: {elapsed:.1f}s")

    print("\n" + "="*70)
    print("STATUS: REAL EXPERIMENT COMPLETE")
    print("="*70)
    print("\nThis is ACTUAL DATA from trained PyTorch networks.")
    print("Results are reproducible (modulo random initialization).")


if __name__ == '__main__':
    main()
