#!/usr/bin/env python3
"""
Animate Collatz Dynamics: Watch self-correction in action

Creates animation showing:
1. Collatz trajectories converging to 1
2. Error correction happening at each step
3. Multiple trajectories simultaneously
4. Convergence to the canonical path (powers of 2)
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.animation as animation
from matplotlib.patches import Circle, FancyArrowPatch


def collatz_step(n):
    """Single Collatz step"""
    return n // 2 if n % 2 == 0 else 3 * n + 1


def generate_trajectory(n, max_steps=200):
    """Generate full Collatz trajectory"""
    traj = [n]
    current = n
    for _ in range(max_steps):
        if current == 1:
            break
        current = collatz_step(current)
        traj.append(current)
    return traj


def create_collatz_animation(starting_values=[27, 15, 31, 7, 19], save_file='collatz_animation.gif'):
    """Create animated visualization of Collatz convergence"""

    # Generate all trajectories
    trajectories = {n: generate_trajectory(n) for n in starting_values}
    max_length = max(len(traj) for traj in trajectories.values())

    # Setup figure
    fig, (ax_main, ax_convergence) = plt.subplots(1, 2, figsize=(16, 6))

    # Main plot: trajectories over time
    colors = plt.cm.tab10(np.linspace(0, 1, len(starting_values)))

    def init():
        ax_main.clear()
        ax_convergence.clear()

        ax_main.set_xlim(-5, max_length + 5)
        ax_main.set_ylim(0, max(starting_values) * 1.2)
        ax_main.set_xlabel('Step', fontsize=12, fontweight='bold')
        ax_main.set_ylabel('Value', fontsize=12, fontweight='bold')
        ax_main.set_title('Collatz Trajectories: Self-Correction to 1',
                         fontsize=14, fontweight='bold')
        ax_main.grid(True, alpha=0.3)
        ax_main.axhline(1, color='red', linestyle='--', linewidth=2,
                       label='Target (canonical path)')

        # Mark powers of 2 (canonical path)
        powers = [2**i for i in range(int(np.log2(max(starting_values))) + 1)]
        for p in powers:
            if p <= max(starting_values):
                ax_main.axhline(p, color='green', linestyle=':', alpha=0.3)

        ax_convergence.set_xlim(-1, len(starting_values))
        ax_convergence.set_ylim(0, max_length + 10)
        ax_convergence.set_xlabel('Starting Value', fontsize=12, fontweight='bold')
        ax_convergence.set_ylabel('Steps to Convergence', fontsize=12, fontweight='bold')
        ax_convergence.set_title('Convergence Times', fontsize=14, fontweight='bold')
        ax_convergence.grid(True, alpha=0.3)

        return []

    def animate(frame):
        if frame == 0:
            init()

        # Update main plot
        for i, (n, traj) in enumerate(trajectories.items()):
            steps_to_show = min(frame + 1, len(traj))
            x = list(range(steps_to_show))
            y = traj[:steps_to_show]

            ax_main.plot(x, y, color=colors[i], linewidth=2, alpha=0.8,
                        marker='o', markersize=4, label=f'n={n}')

            # Highlight current position
            if steps_to_show < len(traj):
                ax_main.plot(steps_to_show - 1, y[-1], 'o',
                           color=colors[i], markersize=12,
                           markeredgecolor='black', markeredgewidth=2)

                # Show operation
                current = traj[steps_to_show - 1]
                operation = 'n/2' if current % 2 == 0 else '3n+1'
                ax_main.annotate(operation, (steps_to_show - 1, y[-1]),
                               xytext=(10, 10), textcoords='offset points',
                               fontsize=9, bbox=dict(boxstyle='round',
                               facecolor='yellow', alpha=0.7))

        # Update convergence plot
        ax_convergence.clear()
        ax_convergence.set_xlim(-0.5, len(starting_values) - 0.5)
        ax_convergence.set_ylim(0, max_length + 10)
        ax_convergence.set_xlabel('Starting Value', fontsize=12, fontweight='bold')
        ax_convergence.set_ylabel('Steps to Convergence', fontsize=12, fontweight='bold')
        ax_convergence.set_title('Convergence Times', fontsize=14, fontweight='bold')
        ax_convergence.grid(True, alpha=0.3)

        for i, (n, traj) in enumerate(trajectories.items()):
            if frame >= len(traj) - 1:  # Reached 1
                ax_convergence.bar(i, len(traj), color=colors[i],
                                  alpha=0.7, edgecolor='black', linewidth=2)
                ax_convergence.text(i, len(traj) + 3, str(len(traj)),
                                   ha='center', fontsize=10, fontweight='bold')

        ax_convergence.set_xticks(range(len(starting_values)))
        ax_convergence.set_xticklabels([str(n) for n in starting_values])

        if frame > 5:
            ax_main.legend(loc='upper right', fontsize=9)

        return []

    # Create animation
    anim = animation.FuncAnimation(fig, animate, init_func=init,
                                  frames=max_length,
                                  interval=200, blit=True, repeat=True)

    # Save
    print(f"Creating animation (this may take a minute)...")
    anim.save(save_file, writer='pillow', fps=5, dpi=100)
    print(f"✓ Created: {save_file}")
    plt.close()


def create_tower_growth_animation(save_file='tower_growth_animation.gif'):
    """Animate exponential tower growth"""

    fig, ax = plt.subplots(figsize=(12, 8))

    base = 3
    levels = list(range(5))

    def init():
        ax.clear()
        ax.set_xlim(-0.5, len(levels) - 0.5)
        ax.set_ylim(0.1, 1e5)
        ax.set_yscale('log')
        ax.set_xlabel('Distinction Level n', fontsize=13, fontweight='bold')
        ax.set_ylabel('Size |D^n(X)| (log scale)', fontsize=13, fontweight='bold')
        ax.set_title(f'Tower Growth Animation: |D^n(X)| = |X|^(2^n) for |X| = {base}',
                    fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        ax.set_xticks(levels)
        ax.set_xticklabels([f'D^{n}' for n in levels])
        return []

    def animate(frame):
        ax.clear()
        init()

        # Show growth up to current frame
        show_up_to = min(frame, len(levels) - 1)

        sizes = [base ** (2**n) for n in range(show_up_to + 1)]
        colors = plt.cm.viridis(np.linspace(0, 1, show_up_to + 1))

        # Draw bars
        for i in range(show_up_to + 1):
            alpha = 1.0 if i == show_up_to else 0.6
            ax.bar(i, sizes[i], color=colors[i], edgecolor='black',
                  linewidth=2, alpha=alpha)

            # Label
            size_str = f'{sizes[i]:,}' if sizes[i] < 1e6 else f'{sizes[i]:.2e}'
            ax.text(i, sizes[i] * 1.3, size_str,
                   ha='center', fontsize=11, fontweight='bold')

            # Formula
            exp = 2**i
            ax.text(i, sizes[i] * 0.5, f'{base}^{exp}',
                   ha='center', fontsize=10, style='italic')

        # Show growth factor
        if show_up_to > 0:
            prev_size = sizes[show_up_to - 1]
            curr_size = sizes[show_up_to]
            growth = curr_size / prev_size

            ax.annotate(f'{growth:.0f}×', xy=(show_up_to, curr_size),
                       xytext=(show_up_to - 0.3, (curr_size + prev_size)/2),
                       fontsize=12, fontweight='bold', color='red',
                       bbox=dict(boxstyle='round', facecolor='yellow', alpha=0.8),
                       arrowprops=dict(arrowstyle='->', color='red', lw=2))

        return []

    # Create animation
    anim = animation.FuncAnimation(fig, animate, init_func=init,
                                  frames=len(levels) * 3,
                                  interval=600, blit=True, repeat=True)

    print(f"Creating tower animation...")
    anim.save(save_file, writer='pillow', fps=2, dpi=100)
    print(f"✓ Created: {save_file}")
    plt.close()


def create_autopoietic_loop_animation(save_file='autopoietic_loop_animation.gif'):
    """Animate the autopoietic maintenance loop"""

    fig, ax = plt.subplots(figsize=(10, 10))

    positions = {
        'X': (0.5, 0.5),
        'DX': (0.5, 0.8),
        'BoxDX': (0.8, 0.5),
        'Return': (0.5, 0.2),
    }

    def init():
        ax.clear()
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        ax.axis('off')
        ax.set_title('Autopoietic Loop: Self-Maintenance Through Examination',
                    fontsize=14, fontweight='bold', pad=20)
        return []

    def animate(frame):
        ax.clear()
        init()

        # Calculate which step we're on (0-3, cycling)
        step = frame % 4

        # Draw all nodes
        nodes = [
            (0.5, 0.5, 'X', 'lightgreen', step == 0),
            (0.5, 0.8, 'D(X)', 'lightblue', step == 1),
            (0.8, 0.5, '□D(X)', 'lightyellow', step == 2),
            (0.2, 0.5, 'Stabilized', 'lightgreen', step == 3),
        ]

        for x, y, label, color, active in nodes:
            size = 0.08 if active else 0.06
            linewidth = 4 if active else 2
            circle = Circle((x, y), size, facecolor=color, edgecolor='black',
                          linewidth=linewidth, zorder=10)
            ax.add_patch(circle)
            ax.text(x, y, label, ha='center', va='center',
                   fontsize=11 if active else 9, fontweight='bold')

        # Draw arrows based on step
        arrows = []

        if step >= 0:  # X → D(X)
            arrow = FancyArrowPatch((0.5, 0.56), (0.5, 0.74),
                                   arrowstyle='->', mutation_scale=20,
                                   linewidth=3, color='darkblue', zorder=5)
            ax.add_patch(arrow)
            ax.text(0.58, 0.65, 'D', fontsize=12, fontweight='bold',
                   style='italic', color='darkblue')

        if step >= 1:  # D(X) → □D(X)
            arrow = FancyArrowPatch((0.56, 0.8), (0.74, 0.56),
                                   arrowstyle='->', mutation_scale=20,
                                   linewidth=3, color='darkgreen', zorder=5)
            ax.add_patch(arrow)
            ax.text(0.68, 0.72, '□', fontsize=14, fontweight='bold',
                   color='darkgreen')

        if step >= 2:  # □D(X) → Stabilized
            arrow = FancyArrowPatch((0.74, 0.5), (0.26, 0.5),
                                   arrowstyle='->', mutation_scale=20,
                                   linewidth=3, color='purple', zorder=5)
            ax.add_patch(arrow)
            ax.text(0.5, 0.42, 'Maintain', fontsize=10, fontweight='bold',
                   style='italic', color='purple', ha='center')

        if step >= 3:  # Complete loop
            arrow = FancyArrowPatch((0.26, 0.56), (0.44, 0.5),
                                   arrowstyle='->', mutation_scale=20,
                                   linewidth=3, color='darkred', zorder=5,
                                   connectionstyle="arc3,rad=.3")
            ax.add_patch(arrow)

        # Condition labels
        ax.text(0.5, 0.95, '∇ = D□ - □D ≠ 0', ha='center', fontsize=12,
               bbox=dict(boxstyle='round', facecolor='yellow',
                        edgecolor='black', linewidth=2))
        ax.text(0.5, 0.05, 'R = ∇² = 0 (constant curvature)', ha='center',
               fontsize=12, bbox=dict(boxstyle='round', facecolor='lightgreen',
                                     edgecolor='black', linewidth=2))

        # Step indicator
        step_names = ['Examine', 'Stabilize', 'Maintain', 'Loop Closes']
        ax.text(0.5, 0.12, f'Step {step+1}: {step_names[step]}',
               ha='center', fontsize=11, fontweight='bold', style='italic')

        return []

    anim = animation.FuncAnimation(fig, animate, init_func=init,
                                  frames=20, interval=800, blit=True)

    print(f"Creating autopoietic loop animation...")
    anim.save(save_file, writer='pillow', fps=1, dpi=100)
    print(f"✓ Created: {save_file}")
    plt.close()


def create_information_horizon_animation(save_file='information_horizon_animation.gif'):
    """Animate witness complexity vs theory capacity"""

    fig, ax = plt.subplots(figsize=(12, 8))

    # Statements that will appear
    statements = [
        (0.05, 0.05, '2+2=4', 'Simple', 0),
        (0.15, 0.2, 'Specific cases', 'Provable', 1),
        (0.25, 0.35, 'Paris-Harrington', 'At boundary', 2),
        (0.4, 0.5, 'Goldbach', 'Unprovable', 3),
        (0.55, 0.6, 'Twin Primes', 'Unprovable', 4),
        (0.7, 0.7, 'RH', 'Unprovable', 5),
        (0.85, 0.8, 'Gödel G_T', 'Self-referential', 6),
    ]

    c_T = 0.42  # Theory capacity line

    def init():
        ax.clear()
        ax.set_xlim(-0.05, 1.05)
        ax.set_ylim(-0.05, 1.05)
        ax.set_xlabel('Self-Reference Degree', fontsize=13, fontweight='bold')
        ax.set_ylabel('Witness Complexity K_W', fontsize=13, fontweight='bold')
        ax.set_title('The Information Horizon: Where Truth Transcends Proof',
                    fontsize=14, fontweight='bold')
        ax.grid(True, alpha=0.3)
        return []

    def animate(frame):
        ax.clear()
        init()

        # Draw zones
        x = np.linspace(0, 1, 100)
        ax.fill_between(x, 0, c_T, alpha=0.15, color='green',
                       label='Provable (K_W < c_T)')
        ax.fill_between(x, c_T, 1, alpha=0.15, color='red',
                       label='Unprovable (K_W > c_T)')

        # Draw capacity line
        ax.axhline(c_T, color='red', linewidth=3, linestyle='--',
                  label='Theory Capacity c_T', zorder=5)

        # Show statements up to current frame
        show_up_to = min(frame, len(statements))

        for i in range(show_up_to):
            self_ref, complexity, name, desc, _ = statements[i]

            # Determine color based on provability
            color = 'green' if complexity < c_T else 'red'
            marker_size = 15 if i == show_up_to - 1 else 10

            ax.plot(self_ref, complexity, 'o', markersize=marker_size,
                   color=color, markeredgecolor='black', markeredgewidth=2,
                   zorder=10)

            # Animate label appearing
            if i == show_up_to - 1 or show_up_to == len(statements):
                ax.annotate(name, (self_ref, complexity),
                           xytext=(10, 10), textcoords='offset points',
                           fontsize=10, fontweight='bold',
                           bbox=dict(boxstyle='round', facecolor='white',
                                   edgecolor=color, linewidth=2),
                           arrowprops=dict(arrowstyle='->', color=color, lw=2))

        # Legend
        if frame > 0:
            ax.legend(loc='upper left', fontsize=10)

        # Add depth-1 boundary line (appears midway)
        if frame > 3:
            depth_1_x = np.linspace(0, 1, 50)
            depth_1_y = 0.25 + 0.6 * depth_1_x
            ax.plot(depth_1_x, depth_1_y, 'k:', linewidth=2, alpha=0.5,
                   label='Depth-1 self-exam threshold')

            if frame > 5:
                ax.text(0.5, 0.6, 'Depth-1 boundary', fontsize=11,
                       style='italic', ha='center',
                       bbox=dict(boxstyle='round', facecolor='white', alpha=0.7))

        return []

    anim = animation.FuncAnimation(fig, animate, init_func=init,
                                  frames=len(statements) * 2 + 5,
                                  interval=700, blit=True, repeat=True)

    print(f"Creating information horizon animation...")
    anim.save(save_file, writer='pillow', fps=1.5, dpi=100)
    print(f"✓ Created: {save_file}")
    plt.close()


def main():
    """Generate all animations"""

    print("="*70)
    print("CREATING DYNAMIC ANIMATIONS")
    print("="*70)
    print("\nGenerating animated GIFs...")
    print("(This will take 2-3 minutes)")
    print()

    create_autopoietic_loop_animation('autopoietic_loop_animation.gif')
    create_tower_growth_animation('tower_growth_animation.gif')
    create_information_horizon_animation('information_horizon_animation.gif')
    create_collatz_animation('collatz_convergence_animation.gif')

    print()
    print("="*70)
    print("COMPLETE: 4 animations created")
    print("="*70)
    print("\nFiles created:")
    print("  1. autopoietic_loop_animation.gif (4s loop)")
    print("  2. tower_growth_animation.gif (exponential growth)")
    print("  3. information_horizon_animation.gif (statements appearing)")
    print("  4. collatz_convergence_animation.gif (trajectories converging)")
    print("\nAll animations loop infinitely.")
    print("Use in presentations, web pages, or documentation.")


if __name__ == '__main__':
    main()
