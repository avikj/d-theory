#!/usr/bin/env python3
"""
Transformer Attention Convergence Experiment

Prediction: Attention matrices converge as layers deepen, following
spectral sequence convergence to E_∞ page.

Tests: ||A_{i+1} - A_i|| → 0 with exponential decay

Date: 2025-10-30
Theory: Distinction Theory - Spectral sequences in transformers
"""

import torch
import numpy as np
import matplotlib.pyplot as plt
from typing import List, Tuple, Dict
import warnings
warnings.filterwarnings('ignore')

# Try to import transformers (will handle gracefully if not available)
try:
    from transformers import AutoModel, AutoTokenizer
    HAS_TRANSFORMERS = True
except ImportError:
    HAS_TRANSFORMERS = False
    print("WARNING: transformers library not available")
    print("Install with: pip install transformers")


def compute_attention_convergence(
    model_name: str,
    input_text: str,
    use_cuda: bool = False
) -> Tuple[List[float], List[np.ndarray]]:
    """
    Extract attention weights from transformer and compute convergence.

    Returns:
        convergence: List of ||A_{i+1} - A_i|| for each layer
        attentions: List of averaged attention matrices
    """
    if not HAS_TRANSFORMERS:
        raise ImportError("transformers library required")

    # Load model
    print(f"Loading {model_name}...")
    model = AutoModel.from_pretrained(model_name)
    tokenizer = AutoTokenizer.from_pretrained(model_name)

    if use_cuda and torch.cuda.is_available():
        model = model.cuda()

    model.eval()

    # Tokenize input
    inputs = tokenizer(input_text, return_tensors="pt", truncation=True, max_length=512)
    if use_cuda and torch.cuda.is_available():
        inputs = {k: v.cuda() for k, v in inputs.items()}

    # Forward pass with attention output
    with torch.no_grad():
        outputs = model(**inputs, output_attentions=True)

    attentions = outputs.attentions  # Tuple of (batch, heads, seq, seq)

    # Average over batch and heads to get layer-level attention
    attention_matrices = []
    for attn in attentions:
        # attn shape: (batch, heads, seq_len, seq_len)
        avg_attn = attn.mean(dim=(0, 1)).cpu().numpy()  # Average over batch and heads
        attention_matrices.append(avg_attn)

    # Compute convergence: ||A_{i+1} - A_i||
    convergence = []
    for i in range(len(attention_matrices) - 1):
        A_i = attention_matrices[i]
        A_next = attention_matrices[i + 1]

        # Frobenius norm
        diff = np.linalg.norm(A_next - A_i, ord='fro')
        convergence.append(diff)

    return convergence, attention_matrices


def fit_exponential_decay(convergence: List[float]) -> Tuple[float, float]:
    """
    Fit exponential decay: ||A_{i+1} - A_i|| ~ C * exp(-λ*i)

    Returns:
        C: amplitude
        lambda: decay rate
    """
    x = np.arange(len(convergence))
    y = np.array(convergence)

    # Fit log(y) = log(C) - λ*x
    # Filter out zeros/negatives for log
    valid = y > 0
    if not np.any(valid):
        return 0.0, 0.0

    x_valid = x[valid]
    log_y = np.log(y[valid])

    # Linear fit in log space
    coeffs = np.polyfit(x_valid, log_y, 1)
    lambda_decay = -coeffs[0]
    C = np.exp(coeffs[1])

    return C, lambda_decay


def analyze_model(model_name: str, input_texts: List[str]) -> Dict:
    """
    Analyze attention convergence for a model across multiple inputs.
    """
    results = {
        'model': model_name,
        'convergence_curves': [],
        'decay_rates': [],
        'amplitudes': []
    }

    for text in input_texts:
        try:
            conv, _ = compute_attention_convergence(model_name, text)
            C, lam = fit_exponential_decay(conv)

            results['convergence_curves'].append(conv)
            results['decay_rates'].append(lam)
            results['amplitudes'].append(C)

        except Exception as e:
            print(f"Error processing '{text[:30]}...': {e}")
            continue

    return results


def plot_results(results_dict: Dict[str, Dict], save_path: str = "transformer_attention_convergence.png"):
    """
    Create publication-quality visualization.
    """
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    # Plot 1: Convergence curves for each model
    ax = axes[0, 0]
    for model_name, results in results_dict.items():
        for i, conv in enumerate(results['convergence_curves']):
            layers = range(1, len(conv) + 1)
            alpha = 0.3 if len(results['convergence_curves']) > 1 else 1.0
            label = model_name if i == 0 else None
            ax.plot(layers, conv, 'o-', alpha=alpha, label=label)

    ax.set_xlabel("Layer i")
    ax.set_ylabel("||A_{i+1} - A_i||")
    ax.set_title("Attention Convergence by Layer")
    ax.legend()
    ax.grid(True, alpha=0.3)

    # Plot 2: Log-scale (test exponential decay)
    ax = axes[0, 1]
    for model_name, results in results_dict.items():
        for conv in results['convergence_curves']:
            layers = range(1, len(conv) + 1)
            ax.semilogy(layers, conv, 'o-', alpha=0.5)

    ax.set_xlabel("Layer i")
    ax.set_ylabel("||A_{i+1} - A_i|| (log scale)")
    ax.set_title("Exponential Decay Test")
    ax.grid(True, alpha=0.3)

    # Plot 3: Decay rates by model
    ax = axes[1, 0]
    model_names = list(results_dict.keys())
    decay_rates_avg = [np.mean(results_dict[m]['decay_rates']) for m in model_names]
    decay_rates_std = [np.std(results_dict[m]['decay_rates']) for m in model_names]

    x_pos = range(len(model_names))
    ax.bar(x_pos, decay_rates_avg, yerr=decay_rates_std, capsize=5, alpha=0.7)
    ax.set_xticks(x_pos)
    ax.set_xticklabels([m.split('/')[-1] for m in model_names], rotation=45, ha='right')
    ax.set_ylabel("Decay Rate λ")
    ax.set_title("Average Decay Rate by Model")
    ax.grid(True, alpha=0.3)

    # Plot 4: Summary statistics
    ax = axes[1, 1]
    ax.axis('off')

    summary_text = "Summary Statistics\n" + "="*40 + "\n\n"
    for model_name, results in results_dict.items():
        short_name = model_name.split('/')[-1]
        n_curves = len(results['convergence_curves'])
        avg_decay = np.mean(results['decay_rates'])
        std_decay = np.std(results['decay_rates'])

        summary_text += f"{short_name}:\n"
        summary_text += f"  Inputs tested: {n_curves}\n"
        summary_text += f"  Decay rate λ: {avg_decay:.4f} ± {std_decay:.4f}\n"
        summary_text += f"  Converges: {'Yes' if avg_decay > 0 else 'No'}\n\n"

    ax.text(0.1, 0.9, summary_text, transform=ax.transAxes,
            fontsize=10, verticalalignment='top', family='monospace')

    plt.tight_layout()
    plt.savefig(save_path, dpi=300, bbox_inches='tight')
    print(f"Saved: {save_path}")

    return fig


def main():
    """
    Main experiment: Test attention convergence across models and inputs.
    """
    if not HAS_TRANSFORMERS:
        print("\nERROR: transformers library not installed")
        print("Install with: pip install transformers")
        print("\nThis experiment requires the transformers library to load pre-trained models.")
        return

    print("="*60)
    print("Transformer Attention Convergence Experiment")
    print("Distinction Theory - Spectral Sequence Prediction")
    print("="*60)

    # Test inputs with varying complexity
    test_inputs = [
        "The cat sat on the mat.",  # Simple
        "The quick brown fox jumps over the lazy dog.",  # Medium
        "In a hole in the ground there lived a hobbit.",  # Medium
        "It was the best of times, it was the worst of times.",  # Complex
    ]

    # Models to test (start with small/accessible ones)
    models = [
        "distilbert-base-uncased",  # 6 layers, small
        "bert-base-uncased",         # 12 layers, standard
    ]

    # Can add larger models if compute allows:
    # "bert-large-uncased",       # 24 layers
    # "gpt2",                     # 12 layers

    results_dict = {}

    for model_name in models:
        print(f"\n{'='*60}")
        print(f"Testing: {model_name}")
        print(f"{'='*60}")

        try:
            results = analyze_model(model_name, test_inputs)
            results_dict[model_name] = results

            # Print summary
            avg_decay = np.mean(results['decay_rates'])
            print(f"\nAverage decay rate λ = {avg_decay:.4f}")
            print(f"Convergence confirmed: {avg_decay > 0}")

        except Exception as e:
            print(f"Error with {model_name}: {e}")
            continue

    # Generate visualization
    if results_dict:
        plot_results(results_dict)

        print("\n" + "="*60)
        print("RESULTS SUMMARY")
        print("="*60)

        for model_name, results in results_dict.items():
            print(f"\n{model_name}:")
            avg_decay = np.mean(results['decay_rates'])
            print(f"  - Decay rate λ: {avg_decay:.4f}")
            print(f"  - Prediction: {'CONFIRMED' if avg_decay > 0 else 'REJECTED'}")
            print(f"  - Interpretation: Attention {'converges' if avg_decay > 0 else 'does not converge'} exponentially")

    else:
        print("\nNo results generated. Check model availability and dependencies.")

    print("\n" + "="*60)
    print("Experiment complete")
    print("="*60)


if __name__ == "__main__":
    main()
