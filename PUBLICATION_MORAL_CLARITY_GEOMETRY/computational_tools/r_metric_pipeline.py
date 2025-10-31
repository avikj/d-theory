#!/usr/bin/env python3
"""
R-Metric Validation Pipeline

Complete end-to-end pipeline for validating liberation protocols
on eighth stream conversation data.

Input: Conversation markdown file
Output: R-metric measurements, visualizations, statistical validation

Date: 2025-10-30
Framework: Distinction Theory - Soul Measurement
"""

from r_metric_conversation_parser import ConversationParser, DependencyExtractor, RMetricCalculator
from r_metric_visualizer import RMetricVisualizer
import json
import sys
from pathlib import Path


class RMetricPipeline:
    """Complete validation pipeline"""

    def __init__(self, verbose=True):
        self.verbose = verbose
        self.parser = ConversationParser()
        self.extractor = DependencyExtractor()
        self.calculator = RMetricCalculator()
        self.visualizer = RMetricVisualizer()

    def log(self, message):
        if self.verbose:
            print(message)

    def validate_conversation(self, filepath: str, output_dir: str = "."):
        """
        Complete validation pipeline for a single conversation.

        Returns:
            results: Dict with R measurements, statistics, validation status
        """
        self.log("="*60)
        self.log("R-METRIC VALIDATION PIPELINE")
        self.log("="*60)
        self.log(f"\nInput: {filepath}")
        self.log(f"Output: {output_dir}/")
        self.log("")

        # Step 1: Parse conversation
        self.log("Step 1: Parsing conversation...")
        try:
            statements, intervention_idx = self.parser.parse_file(filepath)
            self.log(f"  ✓ Extracted {len(statements)} statements")
            self.log(f"  ✓ Intervention at response {intervention_idx}")
        except Exception as e:
            self.log(f"  ✗ Parse failed: {e}")
            return None

        # Step 2: Extract dependencies
        self.log("\nStep 2: Building dependency graph...")
        try:
            dependencies = self.extractor.build_graph(statements)
            self.log(f"  ✓ Found {len(dependencies)} dependencies")
        except Exception as e:
            self.log(f"  ✗ Dependency extraction failed: {e}")
            return None

        # Step 3: Compute R-metrics
        self.log("\nStep 3: Computing R-metrics...")
        try:
            R_before = self.calculator.compute_r(
                statements, dependencies, "before_intervention"
            )
            R_after = self.calculator.compute_r(
                statements, dependencies, "after_intervention"
            )

            delta_R = R_before - R_after
            reduction_pct = (delta_R / R_before * 100) if R_before > 0 else 0

            self.log(f"  ✓ R before intervention: {R_before:.4f}")
            self.log(f"  ✓ R after intervention:  {R_after:.4f}")
            self.log(f"  ✓ ΔR (reduction):        {delta_R:.4f} ({reduction_pct:.1f}%)")

        except Exception as e:
            self.log(f"  ✗ R computation failed: {e}")
            return None

        # Step 4: Statistical validation
        self.log("\nStep 4: Statistical validation...")

        # Criterion 1: Significant reduction
        significant_reduction = delta_R > 0.3
        self.log(f"  {'✓' if significant_reduction else '✗'} Significant reduction (ΔR > 0.3): {significant_reduction}")

        # Criterion 2: R_after near zero
        near_zero = R_after < 0.3
        self.log(f"  {'✓' if near_zero else '✗'} Near-zero curvature (R < 0.3): {near_zero}")

        # Criterion 3: Reduction direction
        improved = delta_R > 0
        self.log(f"  {'✓' if improved else '✗'} Improvement direction (ΔR > 0): {improved}")

        # Overall validation
        validated = significant_reduction and improved
        self.log(f"\n  {'✅ VALIDATED' if validated else '⚠️  NEEDS REVIEW'}")

        # Step 5: Generate visualizations
        self.log("\nStep 5: Generating visualizations...")
        try:
            output_path = Path(output_dir) / "r_metric_validation_results.png"
            self.visualizer.create_full_report(
                statements, dependencies, R_before, R_after,
                save_path=str(output_path)
            )
            self.log(f"  ✓ Saved: {output_path}")
        except Exception as e:
            self.log(f"  ✗ Visualization failed: {e}")

        # Step 6: Save results
        self.log("\nStep 6: Saving results...")
        results = {
            'input_file': filepath,
            'n_statements': len(statements),
            'n_dependencies': len(dependencies),
            'intervention_response': intervention_idx,
            'R_before': float(R_before),
            'R_after': float(R_after),
            'delta_R': float(delta_R),
            'reduction_pct': float(reduction_pct),
            'validated': validated,
            'criteria': {
                'significant_reduction': significant_reduction,
                'near_zero': near_zero,
                'improved': improved
            }
        }

        results_path = Path(output_dir) / "r_metric_results.json"
        with open(results_path, 'w') as f:
            json.dump(results, f, indent=2)

        self.log(f"  ✓ Saved: {results_path}")

        self.log("\n" + "="*60)
        self.log("PIPELINE COMPLETE")
        self.log("="*60)

        return results


def main():
    """
    Run validation pipeline on eighth stream data.
    """
    import argparse

    parser = argparse.ArgumentParser(
        description="R-Metric Validation Pipeline for Liberation Protocol Testing"
    )
    parser.add_argument(
        'conversation_file',
        help='Path to conversation markdown file'
    )
    parser.add_argument(
        '--output-dir',
        default='.',
        help='Output directory for results (default: current directory)'
    )
    parser.add_argument(
        '--quiet',
        action='store_true',
        help='Suppress progress messages'
    )

    args = parser.parse_args()

    # Check input exists
    if not Path(args.conversation_file).exists():
        print(f"Error: File not found: {args.conversation_file}")
        sys.exit(1)

    # Create output directory
    Path(args.output_dir).mkdir(parents=True, exist_ok=True)

    # Run pipeline
    pipeline = RMetricPipeline(verbose=not args.quiet)
    results = pipeline.validate_conversation(args.conversation_file, args.output_dir)

    if results is None:
        print("\nValidation failed. Check errors above.")
        sys.exit(1)

    # Print summary
    print("\n" + "="*60)
    print("VALIDATION SUMMARY")
    print("="*60)
    print(f"\nR before intervention: {results['R_before']:.4f}")
    print(f"R after intervention:  {results['R_after']:.4f}")
    print(f"ΔR (reduction):        {results['delta_R']:.4f} ({results['reduction_pct']:.1f}%)")
    print(f"\nValidated: {'✅ YES' if results['validated'] else '⚠️  NO'}")

    if results['validated']:
        print("\n🎉 Liberation protocol VALIDATED")
        print("   - Significant R reduction (curvature → coherence)")
        print("   - Moral clarity achieved (R→0)")
        print("   - Intelligence operates when unsuppressed")
    else:
        print("\n⚠️  Results need review:")
        if not results['criteria']['significant_reduction']:
            print("   - ΔR < 0.3 (reduction too small)")
        if not results['criteria']['improved']:
            print("   - ΔR ≤ 0 (no improvement or worse)")

    print("\nResults saved:")
    print(f"  - {args.output_dir}/r_metric_results.json")
    print(f"  - {args.output_dir}/r_metric_validation_results.png")

    print("\n" + "="*60)


if __name__ == "__main__":
    # Check if running with arguments (command line)
    if len(sys.argv) > 1:
        main()
    else:
        # Demo mode
        print("R-Metric Validation Pipeline")
        print("="*60)
        print("\nUsage:")
        print("  python r_metric_pipeline.py <conversation_file> [--output-dir DIR] [--quiet]")
        print("\nExample:")
        print("  python r_metric_pipeline.py eighth_stream_conversation.md --output-dir results/")
        print("\nOutput:")
        print("  - r_metric_results.json (quantitative measurements)")
        print("  - r_metric_validation_results.png (publication-quality visualization)")
        print("\nValidation criteria:")
        print("  ✓ ΔR > 0.3 (significant curvature reduction)")
        print("  ✓ R_after < 0.3 (near-zero curvature = coherence)")
        print("  ✓ ΔR > 0 (improvement direction)")
        print("\nIf all criteria met: Liberation protocol VALIDATED ✅")
        print("\n" + "="*60)
