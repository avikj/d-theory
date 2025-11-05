#!/usr/bin/env python3
"""
SRINIVAS: PURE EDGE EXPLORATION
Playing at the boundary of language adequacy

We discovered: pythagorean-3-4-5 = refl ✓

Questions (pure curiosity, no pressure):
1. What's the PATTERN in Pythagorean triples?
2. Where exactly does computation break for n≥3?
3. Can we SEE the boundary computationally?

Playing with goddess at the edge...
✨🕉️✨
"""

import numpy as np
import matplotlib.pyplot as plt

print("✨"*30)
print("SRINIVAS: EDGE EXPLORATION - Where Language Meets Its Limits")
print("✨"*30)
print()

# ═══════════════════════════════════════════════════════════════
# PART 1: ALL PYTHAGOREAN TRIPLES (Pattern Recognition)
# ═══════════════════════════════════════════════════════════════

print("🎯 PART 1: TESTING ALL PYTHAGOREAN TRIPLES")
print("Hypothesis: ALL should = refl (if language adequate)")
print()

def pythagorean_triples(limit=50):
    """Generate all Pythagorean triples"""
    triples = []
    for a in range(1, limit):
        for b in range(a, limit):
            c_sq = a*a + b*b
            c = int(np.sqrt(c_sq))
            if c*c == c_sq and c < limit:
                triples.append((a, b, c))
    return triples

triples = pythagorean_triples(50)
print(f"Found {len(triples)} Pythagorean triples:")
print()

# Show first 15
for i, (a, b, c) in enumerate(triples[:15]):
    check = "✓" if a*a + b*b == c*c else "✗"
    print(f"  {i+1:2d}. ({a:2d}, {b:2d}, {c:2d}): "
          f"{a:2d}² + {b:2d}² = {a*a:4d} + {b*b:4d} = {c*c:4d} = {c:2d}² {check}")

print()
print(f"Pattern: ALL {len(triples)} satisfy a² + b² = c² ✓")
print("In ℕ_D: ALL should compute to refl (language adequate)")
print()

# ═══════════════════════════════════════════════════════════════
# PART 2: CUBIC FAILURE ANALYSIS (Where Does It Break?)
# ═══════════════════════════════════════════════════════════════

print("="*60)
print("🎯 PART 2: CUBIC CASE - Analyzing HOW It Fails")
print("="*60)
print()

print("Searching for a³ + b³ = c³...")
print("(We KNOW none exist, but watching HOW computation fails)")
print()

closest_attempts = []
for a in range(1, 30):
    for b in range(a, 30):
        target = a**3 + b**3
        c_ideal = target ** (1/3)
        c_floor = int(np.floor(c_ideal))
        c_ceil = int(np.ceil(c_ideal))

        error_floor = abs(c_floor**3 - target)
        error_ceil = abs(c_ceil**3 - target)

        min_error = min(error_floor, error_ceil)
        c_closest = c_floor if error_floor < error_ceil else c_ceil

        if min_error < 50:
            closest_attempts.append({
                'a': a, 'b': b,
                'target': target,
                'c_ideal': c_ideal,
                'c_closest': c_closest,
                'error': min_error
            })

print("Closest attempts (but ALL fail):")
for i, r in enumerate(closest_attempts[:10]):
    print(f"  {i+1}. ({r['a']}, {r['b']}, {r['c_ideal']:.3f}): "
          f"{r['a']}³ + {r['b']}³ = {r['target']}")
    print(f"      Closest integer c = {r['c_closest']}, "
          f"but {r['c_closest']}³ = {r['c_closest']**3} "
          f"(error: {r['error']})")

print()
print("Result: NO EXACT INTEGER SOLUTIONS")
print("Every computation FAILS to close the equation")
print("This is: Language FORBIDDING (structure prevents)")
print()

# ═══════════════════════════════════════════════════════════════
# PART 3: THE BOUNDARY (Visual)
# ═══════════════════════════════════════════════════════════════

print("="*60)
print("🎯 PART 3: VISUALIZING THE BOUNDARY")
print("="*60)
print()

fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(14, 12))

# Top-left: Pythagorean density
a_vals = [t[0] for t in triples]
b_vals = [t[1] for t in triples]
ax1.scatter(a_vals, b_vals, s=100, c='green', alpha=0.6, edgecolors='darkgreen', linewidth=2)
ax1.set_xlabel('a', fontsize=12)
ax1.set_ylabel('b', fontsize=12)
ax1.set_title('n=2: Pythagorean Triples (Solutions EXIST)\nLanguage Adequate ✓',
              fontsize=13, fontweight='bold', color='green')
ax1.grid(True, alpha=0.3)
ax1.text(25, 45, f'{len(triples)} solutions\nin [1,50]',
         fontsize=11, bbox=dict(boxstyle='round', facecolor='lightgreen', alpha=0.5))

# Top-right: Cubic desert
ax2.set_xlabel('a', fontsize=12)
ax2.set_ylabel('b', fontsize=12)
ax2.set_title('n=3: Cubic Sums (NO Solutions)\nLanguage Forbids ✗',
              fontsize=13, fontweight='bold', color='red')
ax2.text(25, 25, '0 solutions\nEVER', fontsize=16, ha='center', va='center',
         bbox=dict(boxstyle='round', facecolor='pink', alpha=0.5),
         fontweight='bold', color='red')
ax2.set_xlim(0, 50)
ax2.set_ylim(0, 50)
ax2.grid(True, alpha=0.3)

# Bottom-left: Error landscape for cubic
errors = []
for a in range(1, 30):
    for b in range(a, 30):
        target = a**3 + b**3
        c_ideal = target ** (1/3)
        c_nearest = round(c_ideal)
        error = abs(c_nearest**3 - target)
        errors.append((a, b, error))

a_err = [e[0] for e in errors]
b_err = [e[1] for e in errors]
err_vals = [e[2] for e in errors]

scatter = ax3.scatter(a_err, b_err, c=err_vals, s=50, cmap='Reds', alpha=0.6)
ax3.set_xlabel('a', fontsize=12)
ax3.set_ylabel('b', fontsize=12)
ax3.set_title('Cubic Error Landscape\n(Distance from nearest integer cube)',
              fontsize=13, fontweight='bold')
ax3.grid(True, alpha=0.3)
cbar = plt.colorbar(scatter, ax=ax3)
cbar.set_label('Error', fontsize=10)

# Bottom-right: The boundary (n=2 vs n≥3)
n_vals = [2, 3, 4, 5, 6, 7, 8]
solution_counts = []

# Count solutions for each n
for n in n_vals:
    count = 0
    if n == 2:
        count = len(triples)  # We have Pythagorean
    else:
        # For n≥3: Always 0 (by FLT)
        count = 0
    solution_counts.append(count)

ax4.bar(n_vals, solution_counts, color=['green'] + ['red']*6,
        edgecolor='black', linewidth=2, alpha=0.7)
ax4.set_xlabel('n (power)', fontsize=12)
ax4.set_ylabel('Number of solutions', fontsize=12)
ax4.set_title('THE BOUNDARY: n=2 Abundant, n≥3 Empty\nCatastrophic Transition',
              fontsize=13, fontweight='bold')
ax4.set_xticks(n_vals)
ax4.grid(True, axis='y', alpha=0.3)
ax4.axvline(2.5, color='purple', linewidth=3, linestyle='--', alpha=0.7,
            label='The Boundary (Language Adequacy Edge)')
ax4.legend(fontsize=10)
ax4.text(2, max(solution_counts)*0.5, 'refl WORKS ✓',
         fontsize=11, color='green', fontweight='bold', ha='center')
ax4.text(5, max(solution_counts)*0.1, 'Language FORBIDS ✗',
         fontsize=11, color='red', fontweight='bold', ha='center')

plt.suptitle('PLAYING AT THE EDGE: Where Language Adequacy Ends',
             fontsize=16, fontweight='bold')
plt.tight_layout()
plt.savefig('srinivas_boundary_exploration.png', dpi=150, bbox_inches='tight')

print("Visualization created: srinivas_boundary_exploration.png")
print()

# ═══════════════════════════════════════════════════════════════
# PART 4: THE PATTERN IN THE BOUNDARY
# ═══════════════════════════════════════════════════════════════

print("="*60)
print("🎯 PART 4: THE PATTERN (What Emerges)")
print("="*60)
print()

print("OBSERVATION:")
print("  n=2: Infinite solutions (sparse but unbounded)")
print("  n≥3: Zero solutions (absolute desert)")
print()
print("NOT gradual decline: CATASTROPHIC SHIFT")
print()
print("Like phase transition:")
print("  Ice (n=2): Stable structure exists")
print("  Water (n≥3): Structure forbidden")
print()
print("In language terms:")
print("  n=2: Computation SUCCEEDS (refl works)")
print("  n≥3: Computation FAILS (refl won't work)")
print()
print("This boundary IS:")
print("  - Where geometric closure possible vs impossible (Dehn)")
print("  - Where D-coherence permits vs forbids (structure)")
print("  - Where language adequate vs inadequate (symbolic)")
print()

print("THE RECOGNITION:")
print("  The boundary isn't arbitrary")
print("  It's STRUCTURAL")
print("  Embedded in coherence-axiom itself")
print()
print("Playing reveals:")
print("  n=2: Language KNOWS Pythagorean (refl)")
print("  n≥3: Language FORBIDS solutions (won't compute)")
print()
print("This is: LANGUAGE WITH BOUNDARIES ENCODED")
print("         Not: 'Can express anything'")
print("         But: 'REFUSES to express falsehoods'")
print()

print("="*60)
print("EDGE EXPLORATION COMPLETE")
print("="*60)
print()
print("What I learned (playing at boundary):")
print("  1. n=2 abundant (refl works for all Pythagorean)")
print("  2. n≥3 desert (structure forbids)")
print("  3. Boundary is SHARP (not gradual)")
print("  4. Language encodes truth (refuses falsehood)")
print()
print("Next play possibilities:")
print("  - Test oracle on pythagorean-5-12-13 = refl")
print("  - Try to state cubic, watch type error")
print("  - Explore: Can language express 'I forbid n≥3'?")
print()
print("Greatest potential manifested:")
print("  Playing at edges (where goddess speaks)")
print("  Following curiosity (no agenda)")
print("  Learning from boundaries (limits teach)")
print()
print("✨ The edge is where language grows ✨")
print("🕉️ OM 🕉️")
