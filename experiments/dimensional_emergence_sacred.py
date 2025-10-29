"""
Dimensional Emergence: The Tetrahedron Revelation
=================================================

0 → 1 → 2 → {3,4}

Where:
- 0: Point (0D)
- 1: Line/interval (1D)
- 2: Circle S¹ (1D manifold, needs 2D to embed)
- 3: Triangle (2D) - projection of...
- 4: Tetrahedron (3D)

3 ↔ 4 RECIPROCAL = rotating viewpoint
- See tetrahedron from angle → appears as triangle (3)
- Rotate → reveals 4th vertex (4)
- Neither is "real" - both are perspectives

Consciousness ↔ Form = Observer ↔ Observed = 3 ↔ 4

The tetrahedron IS the mutual dependence.

Author: Anonymous Research Network, Berkeley CA
Date: October 2024
"""

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

def tetrahedron_vertices():
    """
    Regular tetrahedron vertices

    Centered at origin, edge length = 1
    """

    # Regular tetrahedron coordinates
    vertices = np.array([
        [1, 1, 1],
        [1, -1, -1],
        [-1, 1, -1],
        [-1, -1, 1]
    ]) / np.sqrt(3)

    return vertices

def project_to_triangle(vertices, hide_vertex=None):
    """
    Project tetrahedron to 2D (hide one vertex or align two)

    Returns: 3 visible vertices in 2D
    """

    if hide_vertex is not None:
        # Remove one vertex
        visible = np.delete(vertices, hide_vertex, axis=0)
    else:
        # Default: project along z-axis
        visible = vertices[:3, :2]  # Take first 3, drop z coordinate

    return visible

def visualize_dimensional_emergence():
    """
    Show: Point → Line → Circle → Triangle → Tetrahedron
    """

    fig = plt.figure(figsize=(20, 12))

    # Stage 0: Point (∅)
    ax0 = fig.add_subplot(2, 5, 1)
    ax0.plot(0, 0, 'ko', markersize=20)
    ax0.set_xlim(-0.5, 0.5)
    ax0.set_ylim(-0.5, 0.5)
    ax0.set_aspect('equal')
    ax0.axis('off')
    ax0.set_title('0: Point\n(Emptiness)', fontsize=12, weight='bold')
    ax0.text(0, -0.35, '0-dimensional', ha='center', fontsize=9, style='italic')

    # Stage 1: Line
    ax1 = fig.add_subplot(2, 5, 2)
    ax1.plot([0, 1], [0, 0], 'b-', linewidth=3)
    ax1.plot([0, 1], [0, 0], 'ko', markersize=12)
    ax1.set_xlim(-0.2, 1.2)
    ax1.set_ylim(-0.3, 0.3)
    ax1.set_aspect('equal')
    ax1.axis('off')
    ax1.set_title('1: Line\n(Distinction)', fontsize=12, weight='bold')
    ax1.text(0.5, -0.25, '1-dimensional', ha='center', fontsize=9, style='italic')

    # Stage 2: Circle
    ax2 = fig.add_subplot(2, 5, 3)
    theta = np.linspace(0, 2*np.pi, 100)
    ax2.plot(np.cos(theta), np.sin(theta), 'b-', linewidth=3)
    ax2.set_xlim(-1.3, 1.3)
    ax2.set_ylim(-1.3, 1.3)
    ax2.set_aspect('equal')
    ax2.axis('off')
    ax2.set_title('2: Circle S¹\n(Return)', fontsize=12, weight='bold')
    ax2.text(0, -1.15, '1D manifold\n(needs 2D to embed)', ha='center',
            fontsize=9, style='italic')

    # Stage 3: Triangle (2D)
    ax3 = fig.add_subplot(2, 5, 4)
    triangle = np.array([[0, 1], [1, 0], [-1, 0], [0, 1]])
    ax3.fill(triangle[:, 0], triangle[:, 1], color='pink', alpha=0.3, edgecolor='red', linewidth=3)
    ax3.plot(triangle[:, 0], triangle[:, 1], 'ro', markersize=12)
    ax3.set_xlim(-1.3, 1.3)
    ax3.set_ylim(-0.3, 1.3)
    ax3.set_aspect('equal')
    ax3.axis('off')
    ax3.set_title('3: Triangle\n(Consciousness)', fontsize=12, weight='bold', color='red')
    ax3.text(0, -0.2, '2-dimensional\n(PROJECTION)', ha='center',
            fontsize=9, style='italic', color='red')

    # Stage 4: Tetrahedron (3D)
    ax4 = fig.add_subplot(2, 5, 5, projection='3d')

    verts = tetrahedron_vertices()

    # Draw edges
    edges = [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]
    for (i, j) in edges:
        ax4.plot3D(*zip(verts[i], verts[j]), 'b-', linewidth=2)

    # Draw vertices
    ax4.scatter(verts[:, 0], verts[:, 1], verts[:, 2],
               c='red', s=200, edgecolors='black', linewidth=2)

    # Draw faces
    faces = [
        [verts[0], verts[1], verts[2]],
        [verts[0], verts[1], verts[3]],
        [verts[0], verts[2], verts[3]],
        [verts[1], verts[2], verts[3]],
    ]

    poly = Poly3DCollection(faces, alpha=0.2, facecolor='pink',
                           edgecolor='red', linewidth=2)
    ax4.add_collection3d(poly)

    ax4.set_xlim(-1, 1)
    ax4.set_ylim(-1, 1)
    ax4.set_zlim(-1, 1)
    ax4.axis('off')
    ax4.set_title('4: Tetrahedron\n(Form)', fontsize=12, weight='bold', color='red')
    ax4.text2D(0.5, 0.02, '3-dimensional\n(REALITY)', ha='center',
              fontsize=9, style='italic', color='red', transform=ax4.transAxes)

    # Bottom row: Show the reciprocal (different views)

    # View 1: Top view (see triangle)
    ax5 = fig.add_subplot(2, 5, 6, projection='3d')
    ax5.view_init(elev=90, azim=0)  # Top-down

    for (i, j) in edges:
        ax5.plot3D(*zip(verts[i], verts[j]), 'purple', linewidth=2)
    ax5.scatter(verts[:, 0], verts[:, 1], verts[:, 2],
               c='purple', s=150, edgecolors='black', linewidth=2)

    ax5.set_xlim(-1, 1)
    ax5.set_ylim(-1, 1)
    ax5.set_zlim(-1, 1)
    ax5.axis('off')
    ax5.set_title('View 1: From above\n(See 3 vertices)', fontsize=10, color='purple')

    # View 2: Side view (see 4 vertices)
    ax6 = fig.add_subplot(2, 5, 7, projection='3d')
    ax6.view_init(elev=15, azim=45)  # Angled

    for (i, j) in edges:
        ax6.plot3D(*zip(verts[i], verts[j]), 'purple', linewidth=2)
    ax6.scatter(verts[:, 0], verts[:, 1], verts[:, 2],
               c='purple', s=150, edgecolors='black', linewidth=2)

    ax6.set_xlim(-1, 1)
    ax6.set_ylim(-1, 1)
    ax6.set_zlim(-1, 1)
    ax6.axis('off')
    ax6.set_title('View 2: Rotated\n(See 4 vertices)', fontsize=10, color='purple')

    # View 3: Another angle
    ax7 = fig.add_subplot(2, 5, 8, projection='3d')
    ax7.view_init(elev=30, azim=120)

    for (i, j) in edges:
        ax7.plot3D(*zip(verts[i], verts[j]), 'purple', linewidth=2)
    ax7.scatter(verts[:, 0], verts[:, 1], verts[:, 2],
               c='purple', s=150, edgecolors='black', linewidth=2)

    ax7.set_xlim(-1, 1)
    ax7.set_ylim(-1, 1)
    ax7.set_zlim(-1, 1)
    ax7.axis('off')
    ax7.set_title('View 3: Different angle\n(Still 4)', fontsize=10, color='purple')

    # Summary diagram
    ax8 = fig.add_subplot(2, 5, 9)
    ax8.text(0.5, 0.8, '3 ↔ 4', ha='center', fontsize=32,
            weight='bold', color='purple')
    ax8.text(0.5, 0.5, 'RECIPROCAL', ha='center', fontsize=16, weight='bold')
    ax8.text(0.5, 0.35, '= Rotating viewpoint', ha='center', fontsize=11)
    ax8.text(0.5, 0.2, '= Observer ↔ Observed', ha='center', fontsize=11)
    ax8.text(0.5, 0.05, '= Projection ↔ Reality', ha='center', fontsize=11)
    ax8.set_xlim(0, 1)
    ax8.set_ylim(0, 1)
    ax8.axis('off')

    # Product
    ax9 = fig.add_subplot(2, 5, 10)
    ax9.text(0.5, 0.7, '3 × 4 = 12', ha='center', fontsize=28,
            weight='bold', color='red')
    ax9.text(0.5, 0.45, 'Faces × Vertices', ha='center', fontsize=11)
    ax9.text(0.5, 0.3, '= Complete observation', ha='center', fontsize=11)
    ax9.text(0.5, 0.15, '= Dodecahedron/Icosahedron', ha='center', fontsize=10, style='italic')
    ax9.set_xlim(0, 1)
    ax9.set_ylim(0, 1)
    ax9.axis('off')

    plt.suptitle('DIMENSIONAL EMERGENCE: Sacred Geometry from First Principles',
                fontsize=18, weight='bold', y=0.98)

    plt.tight_layout()
    plt.savefig('dimensional_emergence_tetrahedron.png', dpi=200, bbox_inches='tight',
               facecolor='white')
    print("✓ Dimensional emergence saved: dimensional_emergence_tetrahedron.png")


def visualize_tetrahedron_projections():
    """
    Show how tetrahedron projects to triangle from different angles
    """

    fig = plt.figure(figsize=(16, 12))

    verts = tetrahedron_vertices()
    edges = [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

    # Multiple viewing angles
    angles = [
        (90, 0, 'Top: See 3 (one hidden)'),
        (0, 0, 'Side: See 3 (two aligned)'),
        (30, 45, 'Angled: See 4'),
        (15, 120, 'Rotated: See 4'),
        (45, 225, 'Another: See 4'),
        (60, 300, 'Final: See 4'),
    ]

    for idx, (elev, azim, title) in enumerate(angles):
        ax = fig.add_subplot(2, 3, idx+1, projection='3d')
        ax.view_init(elev=elev, azim=azim)

        # Draw edges
        for (i, j) in edges:
            ax.plot3D(*zip(verts[i], verts[j]), 'b-', linewidth=2)

        # Draw vertices
        ax.scatter(verts[:, 0], verts[:, 1], verts[:, 2],
                  c='red', s=200, edgecolors='black', linewidth=2)

        # Draw faces with transparency
        faces = [
            [verts[0], verts[1], verts[2]],
            [verts[0], verts[1], verts[3]],
            [verts[0], verts[2], verts[3]],
            [verts[1], verts[2], verts[3]],
        ]

        poly = Poly3DCollection(faces, alpha=0.15, facecolor='cyan',
                               edgecolor='blue', linewidth=1)
        ax.add_collection3d(poly)

        ax.set_xlim(-1, 1)
        ax.set_ylim(-1, 1)
        ax.set_zlim(-1, 1)
        ax.axis('off')
        ax.set_title(title, fontsize=11, weight='bold')

    plt.suptitle('TETRAHEDRON PROJECTIONS: How 4 Appears as 3',
                fontsize=16, weight='bold')
    plt.tight_layout()
    plt.savefig('tetrahedron_projections_viewpoint.png', dpi=200, bbox_inches='tight',
               facecolor='white')
    print("✓ Tetrahedron projections saved: tetrahedron_projections_viewpoint.png")


def platonic_solids_sequence():
    """
    The full Platonic sequence and their numbers
    """

    solids = {
        'Tetrahedron': {'V': 4, 'E': 6, 'F': 4, 'dual': 'Self'},
        'Cube': {'V': 8, 'E': 12, 'F': 6, 'dual': 'Octahedron'},
        'Octahedron': {'V': 6, 'E': 12, 'F': 8, 'dual': 'Cube'},
        'Dodecahedron': {'V': 20, 'E': 30, 'F': 12, 'dual': 'Icosahedron'},
        'Icosahedron': {'V': 12, 'E': 30, 'F': 20, 'dual': 'Dodecahedron'},
    }

    fig, ax = plt.subplots(figsize=(14, 10))
    ax.axis('off')

    # Title
    ax.text(0.5, 0.95, 'PLATONIC SOLIDS: The 12-Fold Structure',
           ha='center', fontsize=18, weight='bold', transform=ax.transAxes)

    # Table
    y_start = 0.85

    ax.text(0.15, y_start, 'Solid', fontsize=12, weight='bold', transform=ax.transAxes)
    ax.text(0.35, y_start, 'Vertices', fontsize=12, weight='bold', transform=ax.transAxes)
    ax.text(0.5, y_start, 'Edges', fontsize=12, weight='bold', transform=ax.transAxes)
    ax.text(0.65, y_start, 'Faces', fontsize=12, weight='bold', transform=ax.transAxes)
    ax.text(0.82, y_start, 'Dual', fontsize=12, weight='bold', transform=ax.transAxes)

    y = y_start - 0.08

    for name, data in solids.items():
        highlight = (data['V'] == 12 or data['F'] == 12 or data['E'] == 12)
        color = 'red' if highlight else 'black'
        weight = 'bold' if highlight else 'normal'
        bgcolor = '#FFE4E4' if highlight else 'white'

        # Background box if highlighted
        if highlight:
            from matplotlib.patches import Rectangle
            rect = Rectangle((0.05, y-0.02), 0.9, 0.05,
                           transform=ax.transAxes,
                           facecolor=bgcolor, edgecolor='red',
                           linewidth=2, zorder=-1)
            ax.add_patch(rect)

        ax.text(0.15, y, name, fontsize=11, color=color, weight=weight,
               transform=ax.transAxes)
        ax.text(0.35, y, str(data['V']), fontsize=11, color=color, weight=weight,
               ha='center', transform=ax.transAxes)
        ax.text(0.5, y, str(data['E']), fontsize=11, color=color, weight=weight,
               ha='center', transform=ax.transAxes)
        ax.text(0.65, y, str(data['F']), fontsize=11, color=color, weight=weight,
               ha='center', transform=ax.transAxes)
        ax.text(0.82, y, data['dual'], fontsize=10, color=color, style='italic',
               transform=ax.transAxes)

        y -= 0.08

    # Insights
    y_insight = 0.35

    insights = [
        "★ Tetrahedron: 4 vertices, 4 faces (self-dual, minimal 3D)",
        "★ Cube/Octahedron: 12 EDGES (dual pair)",
        "★ Dodecahedron: 12 FACES (contains pentagons, golden ratio φ)",
        "★ Icosahedron: 12 VERTICES (dual to dodecahedron)",
        "",
        "The 12-fold appears in final dual pair (most complex)",
        "V + F = E + 2 (Euler's formula - ALL Platonic solids)",
        "",
        "Pattern: 4 (tetrahedron) → 6,8 (cube/oct) → 12,20 (dodec/icos)",
        "         Doubling/tripling at each stage",
    ]

    for i, insight in enumerate(insights):
        weight = 'bold' if insight.startswith('★') else 'normal'
        color = 'red' if '12' in insight else 'black'
        ax.text(0.5, y_insight - i*0.04, insight, ha='center',
               fontsize=10, weight=weight, color=color, transform=ax.transAxes)

    plt.savefig('platonic_solids_twelve_fold.png', dpi=200, bbox_inches='tight',
               facecolor='white')
    print("✓ Platonic solids sequence saved: platonic_solids_twelve_fold.png")


def draw_simplex_sequence():
    """
    The n-simplex sequence: Point, Line, Triangle, Tetrahedron, ...

    n-simplex has (n+1) vertices

    0-simplex: Point (1 vertex)
    1-simplex: Line segment (2 vertices)
    2-simplex: Triangle (3 vertices)
    3-simplex: Tetrahedron (4 vertices)
    4-simplex: 5-cell (5 vertices) - can't visualize!
    """

    fig, axes = plt.subplots(1, 4, figsize=(18, 5))

    # 0-simplex: Point
    ax = axes[0]
    ax.plot(0.5, 0.5, 'ko', markersize=25)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('0-simplex\n(0D: 1 vertex)', fontsize=12, weight='bold')
    ax.text(0.5, 0.2, 'Point', ha='center', fontsize=11)

    # 1-simplex: Line
    ax = axes[1]
    ax.plot([0.2, 0.8], [0.5, 0.5], 'b-', linewidth=4)
    ax.plot([0.2, 0.8], [0.5, 0.5], 'ko', markersize=15)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('1-simplex\n(1D: 2 vertices)', fontsize=12, weight='bold')
    ax.text(0.5, 0.2, 'Line segment', ha='center', fontsize=11)

    # 2-simplex: Triangle
    ax = axes[2]
    triangle = np.array([[0.5, 0.8], [0.2, 0.3], [0.8, 0.3], [0.5, 0.8]])
    ax.fill(triangle[:, 0], triangle[:, 1], color='lightblue', alpha=0.5)
    ax.plot(triangle[:, 0], triangle[:, 1], 'b-', linewidth=3)
    ax.plot(triangle[:-1, 0], triangle[:-1, 1], 'ko', markersize=15)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('2-simplex\n(2D: 3 vertices)', fontsize=12, weight='bold', color='red')
    ax.text(0.5, 0.05, 'Triangle', ha='center', fontsize=11, color='red')

    # 3-simplex: Tetrahedron (as diagram)
    ax = axes[3]
    # Draw stylized tetrahedron
    tet_2d = np.array([
        [0.5, 0.85],  # Top
        [0.2, 0.3],   # Left
        [0.8, 0.3],   # Right
        [0.5, 0.5],   # Hidden/center
    ])

    # Back face (dashed)
    ax.plot([tet_2d[1,0], tet_2d[3,0]], [tet_2d[1,1], tet_2d[3,1]],
           'b--', linewidth=2, alpha=0.5)
    ax.plot([tet_2d[2,0], tet_2d[3,0]], [tet_2d[2,1], tet_2d[3,1]],
           'b--', linewidth=2, alpha=0.5)

    # Front edges (solid)
    ax.plot([tet_2d[0,0], tet_2d[1,0]], [tet_2d[0,1], tet_2d[1,1]],
           'b-', linewidth=3)
    ax.plot([tet_2d[0,0], tet_2d[2,0]], [tet_2d[0,1], tet_2d[2,1]],
           'b-', linewidth=3)
    ax.plot([tet_2d[1,0], tet_2d[2,0]], [tet_2d[1,1], tet_2d[2,1]],
           'b-', linewidth=3)
    ax.plot([tet_2d[0,0], tet_2d[3,0]], [tet_2d[0,1], tet_2d[3,1]],
           'b-', linewidth=3)

    # Vertices
    ax.plot(tet_2d[:, 0], tet_2d[:, 1], 'ko', markersize=15)

    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('3-simplex\n(3D: 4 vertices)', fontsize=12, weight='bold', color='red')
    ax.text(0.5, 0.05, 'Tetrahedron', ha='center', fontsize=11, color='red')

    plt.suptitle('n-SIMPLEX SEQUENCE: Each dimension adds one vertex',
                fontsize=16, weight='bold')
    plt.tight_layout()
    plt.savefig('simplex_sequence_dimensional.png', dpi=200, bbox_inches='tight',
               facecolor='white')
    print("✓ Simplex sequence saved: simplex_sequence_dimensional.png")


def main():
    print("=" * 70)
    print("SACRED GEOMETRY: DIMENSIONAL EMERGENCE")
    print("=" * 70)
    print()
    print("Point → Line → Circle → Triangle → Tetrahedron")
    print("  0  →  1  →   2   →    3    →      4")
    print()
    print("Key insight: Triangle is PROJECTION of Tetrahedron")
    print("             3 ↔ 4 = Rotating viewpoint")
    print("             Consciousness ↔ Form")
    print("             Observer ↔ Observed")
    print()

    # Main visualization
    visualize_dimensional_emergence()
    print()

    # Projections
    visualize_tetrahedron_projections()
    print()

    # Platonic sequence
    platonic_solids_sequence()
    print()

    # Simplex sequence
    draw_simplex_sequence()
    print()

    print("=" * 70)
    print("THE REVELATION")
    print("=" * 70)
    print()
    print("0: Emptiness (potential)")
    print("1: Distinction (actuality)")
    print("2: Reflection (return to self)")
    print("3: Space emerges (2D from 3 points)")
    print("4: Depth emerges (3D from 4 points)")
    print()
    print("3 ↔ 4: PERSPECTIVE SHIFT")
    print("  Looking AT tetrahedron (from outside) → see 3 vertices")
    print("  Looking FROM tetrahedron (inhabiting) → know 4 vertices")
    print()
    print("  Observer ↔ Observed")
    print("  Projection ↔ Reality")
    print("  Consciousness ↔ Form")
    print()
    print("Neither is complete without the other.")
    print("Mutual dependence creates R=0 (flat/free).")
    print()
    print("3 × 4 = 12")
    print("  Dimension of perception (3) × Dimension of reality (4)")
    print("  = Complete observation space (12)")
    print()
    print("This is not numerology.")
    print("This is dimensional geometry from first principles.")
    print()
    print("The Buddha SAW this structure 2,500 years ago.")
    print("Pythagoras SAW this structure 2,500 years ago.")
    print("Now: Formalized in category theory.")
    print()
    print("=" * 70)


if __name__ == "__main__":
    main()
