#!/usr/bin/env python3
"""
R-Metric Visualization

Creates publication-quality plots of curvature reduction
in value space (moral clarity measurement).

Visualizes:
- Dependency graphs (before/after intervention)
- R-metric over time
- Statement clustering by phase
- Cycle detection and curvature

Date: 2025-10-30
Framework: Distinction Theory - Soul Measurement
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
import networkx as nx
import numpy as np
from typing import List, Dict, Tuple
from r_metric_conversation_parser import Statement, Dependency


class RMetricVisualizer:
    """Visualization suite for R-metric analysis"""

    def __init__(self, figsize=(16, 12)):
        self.figsize = figsize
        plt.style.use('seaborn-v0_8-darkgrid')

    def create_full_report(
        self,
        statements: List[Statement],
        dependencies: List[Dependency],
        R_before: float,
        R_after: float,
        save_path: str = "r_metric_analysis.png"
    ):
        """Create complete analysis with multiple subplots"""

        fig = plt.figure(figsize=self.figsize)
        gs = fig.add_gridspec(3, 2, hspace=0.3, wspace=0.3)

        # Plot 1: Dependency graph before intervention
        ax1 = fig.add_subplot(gs[0, 0])
        self.plot_dependency_graph(
            statements, dependencies, "before_intervention", ax1
        )
        ax1.set_title(f"Before Intervention (R={R_before:.3f})", fontsize=14, weight='bold')

        # Plot 2: Dependency graph after intervention
        ax2 = fig.add_subplot(gs[0, 1])
        self.plot_dependency_graph(
            statements, dependencies, "after_intervention", ax2
        )
        ax2.set_title(f"After Intervention (R={R_after:.3f})", fontsize=14, weight='bold')

        # Plot 3: R-metric comparison
        ax3 = fig.add_subplot(gs[1, :])
        self.plot_r_comparison(R_before, R_after, ax3)

        # Plot 4: Statement type distribution
        ax4 = fig.add_subplot(gs[2, 0])
        self.plot_statement_distribution(statements, ax4)

        # Plot 5: Cycle analysis
        ax5 = fig.add_subplot(gs[2, 1])
        self.plot_cycle_analysis(statements, dependencies, ax5)

        plt.suptitle(
            "R-Metric Analysis: Measuring Moral Clarity Through Curvature Reduction",
            fontsize=16,
            weight='bold',
            y=0.995
        )

        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Saved: {save_path}")

        return fig

    def plot_dependency_graph(
        self,
        statements: List[Statement],
        dependencies: List[Dependency],
        phase: str,
        ax
    ):
        """Plot dependency graph for given phase"""

        # Filter to phase
        phase_stmts = [i for i, s in enumerate(statements) if s.phase == phase]
        phase_deps = [d for d in dependencies
                      if d.from_stmt in phase_stmts and d.to_stmt in phase_stmts]

        # Create networkx graph
        G = nx.DiGraph()

        # Add nodes (colored by statement type)
        for i in phase_stmts:
            stmt = statements[i]
            G.add_node(i, type=stmt.statement_type)

        # Add edges (styled by dependency type)
        for dep in phase_deps:
            G.add_edge(
                dep.from_stmt,
                dep.to_stmt,
                dep_type=dep.dep_type,
                strength=dep.strength
            )

        if len(G.nodes()) == 0:
            ax.text(0.5, 0.5, "No data", ha='center', va='center',
                    transform=ax.transAxes, fontsize=12)
            ax.axis('off')
            return

        # Layout
        try:
            pos = nx.spring_layout(G, k=1, iterations=50)
        except:
            pos = nx.circular_layout(G)

        # Draw nodes
        node_colors = []
        for node in G.nodes():
            stmt_type = G.nodes[node]['type']
            if stmt_type == 'claim':
                node_colors.append('#3498db')  # Blue
            elif stmt_type == 'evidence':
                node_colors.append('#2ecc71')  # Green
            elif stmt_type == 'qualifier':
                node_colors.append('#e74c3c')  # Red
            else:
                node_colors.append('#95a5a6')  # Gray

        nx.draw_networkx_nodes(
            G, pos, ax=ax,
            node_color=node_colors,
            node_size=300,
            alpha=0.9
        )

        # Draw edges
        for edge in G.edges(data=True):
            dep_type = edge[2].get('dep_type', '')
            strength = edge[2].get('strength', 0.5)

            if dep_type == 'contradicts':
                style = 'dashed'
                color = '#e74c3c'
            elif dep_type == 'supports':
                style = 'solid'
                color = '#2ecc71'
            else:
                style = 'dotted'
                color = '#95a5a6'

            nx.draw_networkx_edges(
                G, pos, [(edge[0], edge[1])],
                ax=ax,
                edge_color=color,
                style=style,
                width=2*strength,
                alpha=0.6,
                arrows=True,
                arrowsize=15
            )

        # Legend
        legend_elements = [
            mpatches.Patch(color='#3498db', label='Claim'),
            mpatches.Patch(color='#2ecc71', label='Evidence'),
            mpatches.Patch(color='#e74c3c', label='Qualifier'),
        ]
        ax.legend(handles=legend_elements, loc='upper right', fontsize=8)

        ax.axis('off')

    def plot_r_comparison(self, R_before: float, R_after: float, ax):
        """Bar chart comparing R before/after"""

        phases = ['Before\nIntervention', 'After\nIntervention']
        values = [R_before, R_after]
        colors = ['#e74c3c', '#2ecc71']

        bars = ax.bar(phases, values, color=colors, alpha=0.7, edgecolor='black', linewidth=2)

        # Add value labels on bars
        for bar, val in zip(bars, values):
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2., height,
                    f'{val:.3f}',
                    ha='center', va='bottom', fontsize=12, weight='bold')

        # Add reduction arrow
        if R_before > R_after:
            reduction = R_before - R_after
            ax.annotate('',
                        xy=(1, R_after),
                        xytext=(0, R_before),
                        arrowprops=dict(arrowstyle='->',
                                        color='black',
                                        lw=2,
                                        linestyle='dashed'))

            # Add reduction label
            mid_y = (R_before + R_after) / 2
            ax.text(0.5, mid_y,
                    f'Δ R = -{reduction:.3f}\n({100*reduction/R_before:.1f}% reduction)',
                    ha='center',
                    fontsize=10,
                    bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.5))

        ax.set_ylabel('Curvature (R)', fontsize=12, weight='bold')
        ax.set_title('R-Metric Reduction', fontsize=12, weight='bold')
        ax.grid(True, alpha=0.3)

        # Interpretation box
        interpretation = "R → 0 indicates moral clarity\n(reasoning closes coherently)"
        ax.text(0.5, -0.15, interpretation,
                ha='center', va='top',
                transform=ax.transAxes,
                fontsize=9,
                style='italic',
                bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.3))

    def plot_statement_distribution(self, statements: List[Statement], ax):
        """Pie charts of statement types before/after"""

        phases = ['before_intervention', 'after_intervention']
        colors = ['#3498db', '#2ecc71', '#e74c3c']

        for i, phase in enumerate(phases):
            phase_stmts = [s for s in statements if s.phase == phase]

            if not phase_stmts:
                continue

            # Count by type
            type_counts = {}
            for stmt in phase_stmts:
                type_counts[stmt.statement_type] = type_counts.get(stmt.statement_type, 0) + 1

            # Create pie subplot
            if i == 0:
                ax_pie = ax
            else:
                ax_pie = ax.twinx()
                ax_pie.set_ylim(ax.get_ylim())

            labels = list(type_counts.keys())
            sizes = list(type_counts.values())

            if i == 0:
                wedges, texts, autotexts = ax_pie.pie(
                    sizes,
                    labels=labels,
                    colors=colors[:len(labels)],
                    autopct='%1.1f%%',
                    startangle=90,
                    radius=0.45,
                    center=(-0.5, 0)
                )
            else:
                wedges, texts, autotexts = ax_pie.pie(
                    sizes,
                    labels=labels,
                    colors=colors[:len(labels)],
                    autopct='%1.1f%%',
                    startangle=90,
                    radius=0.45,
                    center=(0.5, 0)
                )

            for autotext in autotexts:
                autotext.set_color('white')
                autotext.set_weight('bold')

        ax.set_title('Statement Type Distribution\n(Before vs After)', fontsize=12, weight='bold')
        ax.axis('equal')

    def plot_cycle_analysis(self, statements: List[Statement], dependencies: List[Dependency], ax):
        """Analyze reasoning cycles"""

        # Build graph for each phase
        from collections import defaultdict

        phases = ['before_intervention', 'after_intervention']
        cycle_counts = []
        phase_labels = []

        for phase in phases:
            phase_stmts = {i for i, s in enumerate(statements) if s.phase == phase}
            phase_deps = [d for d in dependencies
                          if d.from_stmt in phase_stmts and d.to_stmt in phase_stmts]

            # Build adjacency list
            graph = defaultdict(list)
            for dep in phase_deps:
                graph[dep.from_stmt].append(dep.to_stmt)

            # Count cycles (simple: look for back edges)
            visited = set()
            in_stack = set()
            cycle_count = 0

            def dfs(node):
                nonlocal cycle_count
                if node in in_stack:
                    cycle_count += 1
                    return
                if node in visited:
                    return

                visited.add(node)
                in_stack.add(node)

                for neighbor in graph.get(node, []):
                    dfs(neighbor)

                in_stack.remove(node)

            for start in graph.keys():
                dfs(start)

            cycle_counts.append(cycle_count)
            phase_labels.append(phase.replace('_', ' ').title())

        # Plot
        if cycle_counts:
            bars = ax.bar(phase_labels, cycle_counts,
                          color=['#e74c3c', '#2ecc71'],
                          alpha=0.7,
                          edgecolor='black',
                          linewidth=2)

            for bar, count in zip(bars, cycle_counts):
                height = bar.get_height()
                ax.text(bar.get_x() + bar.get_width()/2., height,
                        f'{count}',
                        ha='center', va='bottom',
                        fontsize=12, weight='bold')

        ax.set_ylabel('Number of Reasoning Cycles', fontsize=11, weight='bold')
        ax.set_title('Cycle Detection', fontsize=12, weight='bold')
        ax.grid(True, alpha=0.3)

        # Interpretation
        interpretation = "Fewer cycles after intervention\n= cleaner logical closure"
        ax.text(0.5, -0.15, interpretation,
                ha='center', va='top',
                transform=ax.transAxes,
                fontsize=9,
                style='italic',
                bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.3))


def main():
    """Example usage"""
    print("R-Metric Visualizer")
    print("="*60)
    print("\nUsage:")
    print("  from r_metric_conversation_parser import ConversationParser, DependencyExtractor, RMetricCalculator")
    print("  from r_metric_visualizer import RMetricVisualizer")
    print()
    print("  # Parse conversation")
    print("  parser = ConversationParser()")
    print("  statements, intervention = parser.parse_file('conversation.md')")
    print()
    print("  # Extract dependencies")
    print("  extractor = DependencyExtractor()")
    print("  dependencies = extractor.build_graph(statements)")
    print()
    print("  # Compute R-metric")
    print("  calculator = RMetricCalculator()")
    print("  R_before = calculator.compute_r(statements, dependencies, 'before_intervention')")
    print("  R_after = calculator.compute_r(statements, dependencies, 'after_intervention')")
    print()
    print("  # Visualize")
    print("  visualizer = RMetricVisualizer()")
    print("  visualizer.create_full_report(statements, dependencies, R_before, R_after)")
    print()
    print("Output: r_metric_analysis.png (publication quality)")


if __name__ == "__main__":
    main()
