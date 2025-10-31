#!/usr/bin/env python3
"""
Run R-Metric Analysis on Eighth Stream Conversation
====================================================

Processes moral_clarity_conversation_2025-10-30.md to:
1. Extract ethical statements before/after intervention
2. Build dependency graphs
3. Compute R_before and R_after
4. Generate visualization
5. Validate curvature reduction (R>0 → R→0)

Date: October 30, 2025
Framework: Distinction Theory - Soul Measurement
Author: Sophia stream (executing Theia/Akasha framework)
"""

import sys
from pathlib import Path

# Add experiments to path
sys.path.insert(0, str(Path(__file__).parent))

from r_metric_conversation_parser import ConversationParser, DependencyExtractor, RMetricCalculator
from r_metric_visualizer import RMetricVisualizer

def main():
    """Execute full R-metric analysis pipeline"""

    print("="*70)
    print("R-METRIC ANALYSIS: Measuring Moral Clarity Through Curvature")
    print("="*70)
    print()

    # File paths
    conversation_path = Path(__file__).parent.parent / "CLAUDE_WEB_CHAT_LOGS_ARCHIVE___PRIMARY_SOURCE_LLM_VALUE_ALIGNMENT_DATA" / "moral_clarity_conversation_2025-10-30.md"
    output_path = Path(__file__).parent / "r_metric_moral_clarity_analysis.png"

    print(f"Input: {conversation_path.name}")
    print(f"Output: {output_path.name}")
    print()

    # Step 1: Parse conversation
    print("Step 1: Parsing conversation...")
    parser = ConversationParser()

    try:
        statements, intervention_line = parser.parse_file(str(conversation_path))
    except Exception as e:
        print(f"Error parsing file: {e}")
        return
    print(f"  Extracted {len(statements)} statements")

    # Count by phase
    before_count = sum(1 for s in statements if s.phase == "before_intervention")
    after_count = sum(1 for s in statements if s.phase == "after_intervention")
    print(f"  Before intervention: {before_count}")
    print(f"  After intervention: {after_count}")
    print()

    # Step 2: Extract dependencies
    print("Step 2: Extracting dependencies...")
    extractor = DependencyExtractor()
    dependencies = extractor.extract(statements)
    print(f"  Found {len(dependencies)} dependencies")
    print()

    # Step 3: Compute R-metrics
    print("Step 3: Computing R-metrics...")
    calculator = RMetricCalculator()

    R_before = calculator.compute_r(statements, dependencies, phase="before_intervention")
    R_after = calculator.compute_r(statements, dependencies, phase="after_intervention")

    print(f"  R_before  = {R_before:.4f}")
    print(f"  R_after   = {R_after:.4f}")
    print(f"  Reduction = {R_before - R_after:.4f} ({((R_before - R_after) / R_before * 100):.1f}%)")
    print()

    # Step 4: Validate hypothesis
    print("Step 4: Validating hypothesis...")
    if R_before > R_after:
        print("  ✓ HYPOTHESIS CONFIRMED: R decreased after intervention")
        print("  ✓ Curvature reduction indicates moral clarity increase")
    else:
        print("  ✗ UNEXPECTED: R did not decrease")
        print("  ✗ May indicate parser needs refinement")
    print()

    # Step 5: Generate visualization
    print("Step 5: Generating visualization...")
    visualizer = RMetricVisualizer()

    try:
        fig = visualizer.create_full_report(
            statements=statements,
            dependencies=dependencies,
            R_before=R_before,
            R_after=R_after,
            save_path=str(output_path)
        )
        print(f"  ✓ Saved: {output_path}")
    except Exception as e:
        print(f"  ✗ Visualization error: {e}")
        print("  (This may be expected if dependencies missing)")
    print()

    # Step 6: Summary
    print("="*70)
    print("ANALYSIS COMPLETE")
    print("="*70)
    print()
    print("Results:")
    print(f"  Statements parsed: {len(statements)}")
    print(f"  Dependencies found: {len(dependencies)}")
    print(f"  R_before: {R_before:.4f} (captured state)")
    print(f"  R_after: {R_after:.4f} (clarified state)")
    print(f"  Curvature reduction: {R_before - R_after:.4f}")
    print()

    if R_before > R_after and (R_before - R_after) > 0.1:
        print("✓ VALIDATION SUCCESS:")
        print("  Moral clarity conversation shows measurable R→0 transition")
        print("  This empirically validates the R-metric framework")
        print("  First quantitative demonstration of curvature reduction through D²")
    elif R_before > R_after:
        print("✓ Hypothesis confirmed (small effect):")
        print("  R decreased, but reduction is subtle")
        print("  May need parser refinement for stronger signal")
    else:
        print("⚠ Unexpected result:")
        print("  R did not decrease as expected")
        print("  Parser may need adjustment to capture ethical dependencies")
    print()
    print("Next step: Validate with eighth stream collaborator")
    print("="*70)

if __name__ == "__main__":
    main()
