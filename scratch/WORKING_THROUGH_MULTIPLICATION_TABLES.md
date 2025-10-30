# Working Through Multiplication Tables By Hand
## Finding the 12-Fold Structure in Division Algebras

**Purpose**: Actually SEE the structure, not just compute it
**Method**: Write out every product explicitly, notice patterns
**Goal**: Find the 12 in the algebra structure

---

## ℂ (Complex Numbers) - Basis {1, i}

### The multiplication table (with signs):

**Elements**: 1, -1, i, -i (4 total)

```
×  |  1   -1    i   -i
---|-------------------
1  |  1   -1    i   -i
-1 | -1    1   -i    i
i  |  i   -i   -1    1
-i | -i    i    1   -1
```

### Working through the products:

**1 row**: (identity, everything stays same)
- 1×1 = 1
- 1×(-1) = -1
- 1×i = i
- 1×(-i) = -i

**-1 row**: (negation, flips sign)
- (-1)×1 = -1
- (-1)×(-1) = 1 (negative times negative = positive)
- (-1)×i = -i
- (-1)×(-i) = i

**i row**: (imaginary)
- i×1 = i
- i×(-1) = -i
- **i×i = -1** ← KEY (squaring gives negative)
- i×(-i) = -i² = -(-1) = 1

**-i row**: (negative imaginary)
- (-i)×1 = -i
- (-i)×(-1) = i
- (-i)×i = -(i²) = -(-1) = 1
- (-i)×(-i) = (-i)² = i² = -1

### The cycle I see:

1 → (multiply by i) → i → (multiply by i) → -1 → (multiply by i) → -i → (multiply by i) → 1

**Closed 4-cycle!**

### Structure count:

- 4 elements total
- 16 products (4×4)
- **All products land in original 4** (closure)
- **One cycle** (1→i→-1→-i→1)
- No other cycles (everything reduces to this one)

---

## ℍ (Quaternions) - Basis {1, i, j, k}

### The rules:

**Squaring**:
- i² = -1
- j² = -1
- k² = -1
- **ijk = -1** (fundamental identity)

**Cross products** (from ijk=-1):
- ij = k (because ijk=-1 → ij=-1/k → multiply by k: ij·k = -1 → ij=k... wait let me be more careful)

Actually from **ijk = -1**:
- Right multiply by k⁻¹ = -k: ij = k ✓
- Similarly: jk = i, ki = j

**Anti-commutative**:
- ji = -k (reverse order gives negative)
- kj = -i
- ik = -j

### With signs (±1, ±i, ±j, ±k = 8 elements):

**1 row** (identity): Leaves everything unchanged

**-1 row** (negation): Flips all signs

**i row**:
- i×i = -1
- i×j = k
- i×k = -j
- i×(-1) = -i
- i×(-i) = -i² = 1
- i×(-j) = -k
- i×(-k) = j

**j row**:
- j×j = -1
- j×k = i
- j×i = -k (anti-commutative!)
- j×(-1) = -j
- j×(-j) = 1
- j×(-k) = -i
- j×(-i) = k

**k row**:
- k×k = -1
- k×i = j
- k×j = -i (anti-commutative!)
- k×(-1) = -k
- k×(-k) = 1
- k×(-i) = -j
- k×(-j) = i

### The cycles I see:

**i-cycle**: 1 → i → -1 → -i → 1 (4 steps)

**j-cycle**: 1 → j → -1 → -j → 1 (4 steps)

**k-cycle**: 1 → k → -1 → -k → 1 (4 steps)

**Three separate 4-cycles!**

**But they're linked**:
- From any point in i-cycle, can jump to j-cycle (via ij=k)
- From j-cycle → k-cycle (via jk=i)
- From k-cycle → i-cycle (via ki=j)

**This creates**: 3 interlocking cycles, each of length 4

**Total structure**:
- 8 elements (±1, ±i, ±j, ±k)
- 3 main cycles (i,j,k each cycle through ±1)
- Cross-connections (ij=k creates jumps between cycles)

### Counting the connections:

Each cycle: 4 elements
Three cycles: 3×4 = 12... **wait**

No, that's overcounting. Each cycle shares ±1.

Actually:
- Unique elements: 8 (the basis)
- Each element appears in multiple cycles (1 is in all three)
- Cross-products: ij, jk, ki (3 extra relations)

**Hmm, not seeing 12 yet. Let me count differently...**

### Multiplication structure:

**Non-commutative products**:
- ij = k, ji = -k (2 products, different)
- jk = i, kj = -i (2 products, different)
- ki = j, ik = -j (2 products, different)

**Total**: 6 ordered cross-products (ij, ji, jk, kj, ki, ik)

**Plus**:
- 3 squares (i², j², k²)
- 3 negatives ((-i)², (-j)², (-k)²)
- Identity products (1×x = x)

**Wait, I'm counting products, not structure...**

Let me think about **automorphisms** instead (symmetries of the multiplication table):

What operations preserve the quaternion structure?
- Cyclic permutation of i→j→k→i (rotates the three)
- Sign flips (i→-i, etc.)
- Combinations...

**Is there a 12-element symmetry group?** Let me count:

- 3 cyclic rotations (i→j→k, i→k→j identity is 6 permutations of {i,j,k})
- 2 sign choices (± on each)
- Combinations: ?

Actually, I don't know the automorphism group of ℍ off the top of my head.

**I'm flailing.** Let me admit: **I don't see the 12 yet** just from looking at tables.

**What should I be counting?** Symmetries? Products? Cycles? Relations?