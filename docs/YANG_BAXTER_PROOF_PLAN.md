# Full Yang-Baxter Proof Plan — Hestenes Geometry on Doubled Real Spaces

## Mathematical Framework

The Yang-Baxter equation for Fibonacci anyons is:

```
B₁·B₂·B₁ = B₂·B₁·B₂    where B = F·R·F
```

in `Mat(2, ℂ) ≅ Cl(2)⁺ ≅ ℝ⁴` (the even subalgebra of the Clifford algebra
Cl(2) of the Euclidean plane, isomorphic to the quaternions ℍ, and under
realification to ℝ⁴ with the Hestenes geometric product).

The Hestenes translation replaces:
- Complex `i` → pseudoscalar `I = γ₁γ₂` (Cl(2) unit bivector, I² = −1)
- Complex matrices → real geometric algebra multivectors
- The F-matrix → a rotor `R(θ) = exp(−Iθ/2)` composed with a reflection
- The R-matrix → a geometric product of the null pair (u₅, v₅) from Cl(5,5)

---

## Three Layers of the Proof

### Layer 1: Scalar identities (already proven)

| Lemma | File | Status |
|-------|------|--------|
| L1.1: φ² = φ + 1 | `FibAnyonThm1.lean:14` (`golden_identity`) | ✅ |
| L1.2: φ·(φ−1) = 1 | `GoldenRatioInvariants.lean:61` (`phi_mul_sub_one_eq_one`) | ✅ |
| L1.3: φ⁻¹ = φ − 1 | `GoldenRatioInvariants.lean:75` (`phi_inv_eq`) | ✅ |
| L1.4: φ³ − φ⁻¹ = 1 + φ² | `GoldenRatioInvariants.lean:91` (`verlinde_golden_identity_mul`) | ✅ |
| L1.5: φ⁴ − 1 = 3φ + 1 | `GoldenRatioInvariants.lean:43` (`phi_pow4_sub_one`) | ✅ |
| L1.6: (1+φ²)·φ = 3φ + 1 | `GoldenRatioInvariants.lean:53` (`one_add_phi_sq_mul_phi`) | ✅ |

### Layer 2: 2×2 matrix identities (SymPy verified, Lean open)

| Lemma | Content | SymPy | Lean |
|-------|---------|-------|------|
| L2.1: τ² + τ = 1 | Golden ratio conjugate | `fibonacci_osp12_bridge.py` | ❌ `YangBaxterProof.lean:30` |
| L2.2: s² = τ | Fibonacci fusion | `fibonacci_osp12_bridge.py` | ❌ `YangBaxterProof.lean:33` |
| L2.3: q⁵ = −1 | 10th root of unity | `fibonacci_osp12_bridge.py` | ❌ `YangBaxterProof.lean:36` |
| L2.4: F² = I | F-matrix involution | `fibonacci_osp12_bridge.py` | ❌ |
| L2.5: B·R·B = R·B·R | Yang-Baxter | `fibonacci_osp12_bridge.py` | ❌ `YangBaxterProof.lean:52` |

### Layer 3: Categorical coherence (mathlib)

| Lemma | File | Status |
|-------|------|--------|
| L3.1: hexagon_forward | `BraidedCategory` axiom | ✅ (in mathlib) |
| L3.2: hexagon_reverse | `BraidedCategory` axiom | ✅ (in mathlib) |
| L3.3: yang_baxter from hexagon | `coherence` tactic | ✅ (in mathlib) |
| L3.4: BraidedCategory instance for Fibonacci | Not in mathlib | ❌ |

---

## The Hestenes/Krein Translation

The complex 2×2 Yang-Baxter proof translates to a real geometric algebra
identity in Cl(5,5) ≅ Cl(4,4) ⊗ Cl(1,1).

### Step H1: Complex → Real via the ClockAxis

The complex unit `i` becomes `K = J·ε = clockAxis`, where:
- `J = modular_j` (swap on the doubled Krein space)
- `ε = spectral_epsilon` (sign flip)
- `K² = −I` (proved in `Cl55V4SpinorFragmentation.lean`)

### Step H2: F-matrix as a Majorana operator

The F-matrix `F = [[τ,s],[s,-τ]]` becomes, under realification ℂ² ≅ ℝ⁴:

```
F_real = τ·σ_z + s·σ_x
```

where `σ_z = majoranaZ`, `σ_x = majoranaX` are the Majorana/Pauli generators
from `FibonacciParafermion.lean`. This is the theorem
`F_matrix_majorana_decomposition`.

### Step H3: R-matrix from the Cl(1,1) null pair

The R-matrix `R = diag(q⁻⁴, q³)` becomes, at q = exp(iπ/5):

```
R_real = exp(θ·K)    where θ = −2π/5
```

This is the rotor `R(θ) = cos(θ)·I + sin(θ)·K` from `RealKCategory.lean`.

### Step H4: B = FRF as a composed rotor

The braid generator `B = FRF` becomes the geometric product:

```
B_real = F_real · R_real · F_real
```

in the Clifford algebra Cl(2) ≅ Mat(2,ℝ), embedded in Cl(5,5) via
the Bott tower Cl(5,5) ≅ Cl(4,4) ⊗ Cl(1,1).

### Step H5: The Yang-Baxter identity in Cl(5,5)

The identity `B·R·B = R·B·R` becomes a real geometric algebra identity
in Cl(5,5):

```
(F·R·F)·R·(F·R·F) = R·(F·R·F)·R
```

Using `F² = I` (since τ²+s² = 1), this simplifies to:

```
F·R·F·R·F·R·F = R·F·R·F·R
```

Multiplying both sides by F on left and right, using F² = I:

```
R·F·R·F·R = F·R·F·R·F·R·F
```

This is the geometric algebra form of the Yang-Baxter equation.
The proof reduces to computing the 4 entries of both sides using
the scalar relations τ²+τ=1, s²=τ, q⁵=−1.

---

## Lemma-by-Lemma Proof Plan

### Part A: Set up the scalar fields (3 lemmas)

**Lemma A1** (`τ_sq_add_tau`): `τ² + τ = 1` where `τ = (√5 − 1)/2`.
- *Proof:* Direct computation using `(√5)² = 5` and ring algebra.
- *Uses:* `Real.sqrt` properties.
- *Status:* Needs translation to ℂ.

**Lemma A2** (`s_sq_eq_tau`): `s² = τ` where `s = √τ`.
- *Proof:* The defining property of the Fibonacci F-matrix.
  From `τ² + τ = 1`, we have `τ² + τ = 1 ⇒ τ² = 1 − τ`, and by definition `s² = τ`.
- *Uses:* Complex sqrt properties, or define s algebraically via `s² = τ`.
- *Status:* Needs explicit proof over ℂ.

**Lemma A3** (`q_pow_five`): `q⁵ = −1` where `q = exp(iπ/5)`.
- *Proof:* `q⁵ = exp(5·iπ/5) = exp(iπ) = −1`.
- *Uses:* `Complex.exp` periodicity.
- *Status:* Needs `Complex.exp` identity proof.

### Part B: Matrix computations (4 lemmas)

**Lemma B1** (`F_sq`): `F² = I` where `F = [[τ,s],[s,-τ]]`.
- *Proof:* `F² = [[τ²+s², 0], [0, s²+τ²]] = (τ²+s²)·I`. By A1 and A2, `τ² + s² = τ² + τ = 1`.
- *Uses:* A1, A2, matrix multiplication.
- *Status:* Already in `FiniteFibonacciFusionMatrix.lean` as `fibonacciFusionMatrix_sq`.

**Lemma B2** (`R_sq`): `R² = diag(q⁻⁸, q⁶) = diag(q², −q)` (at q⁵ = −1).
- *Proof:* `q⁻⁸ = (q⁵)⁻¹·q⁻³ = (−1)⁻¹·q⁻³ = −q⁻³ = q²` (since q⁻³·q⁵ = q², and q⁵ = −1 ⇒ q⁻³ = −q²).
  `q⁶ = q·q⁵ = −q`.
- *Uses:* A3.
- *Status:* Needs explicit computation.

**Lemma B3** (`B_sq`): `B² = F·R²·F`.
- *Proof:* `B² = (FRF)(FRF) = F·R·(F²)·R·F = F·R·R·F = F·R²·F` (using B1).
- *Uses:* B1.
- *Status:* Algebraic identity, independent of scalars.

**Lemma B4** (`yang_baxter`): `B·R·B = R·B·R`.
- *Proof:* The 4-entry computation. Expand both sides using the
  explicit matrix entries and simplify using A1, A2, A3.
  The two sides are:

  ```
  LHS = (FRF)·R·(FRF) = F·R·F·R·F·R·F
  RHS = R·(FRF)·R = R·F·R·F·R
  ```

  Using F² = I, multiply LHS on left and right by F:
  `F·LHS·F = R·F·R·F·R·F·R·F·F = R·F·R·F·R·F = RHS·F·R·F = RHS·B`

  This gives the braid relation.
- *Uses:* A1, A2, A3, B1.
- *Status:* Needs explicit entry computation with ring algebra.

### Part C: Categorical embedding (2 lemmas)

**Lemma C1** (`FibonacciBraided`): The Fibonacci fusion category is a
`BraidedCategory` with the F-matrix as the associator and the B-matrix
as the braiding.
- *Proof:* Verify the hexagon equations. By mathlib's `coherence` tactic,
  this holds automatically once the `BraidedCategory` instance is defined.
- *Uses:* B4.
- *Status:* Requires defining the monoidal category structure on the
  Fibonacci fusion space (tensor product, associator, unitors, braiding).

**Lemma C2** (`yang_baxter_coherence`): In any `BraidedCategory`, the
braiding satisfies the Yang-Baxter equation.
- *Proof:* `coherence` tactic in mathlib. This is the theorem
  `yang_baxter` in `BraidedCategory`.
- *Uses:* C1.
- *Status:* Already in mathlib. No Lean proof needed beyond C1.

---

## Dependency Graph

```
A1 (τ²+τ=1) ──→ B1 (F²=I) ──→ B3 (B²=F·R²·F) ──→ B4 (yang_baxter) ──→ C1 (Braided)
                  ↑                                    ↑                   ↓
A2 (s²=τ) ───────┘                                    │                C2 (coherence)
                                                       │
A3 (q⁵=−1) ───────────────────────────────────────────┘
```

## Existing Resources

| Resource | Location | Use |
|----------|----------|-----|
| Golden ratio invariants | `Canonical/GoldenRatioInvariants.lean` | A1, A2 |
| Fibonacci fusion matrix | `Canonical/FiniteFibonacciFusionMatrix.lean` | B1, B2 |
| Fibonacci parafermion F/Majorana | `Algebra/FibonacciParafermion.lean` | H2 |
| RealKCategory rotors | `Quantum/RealKCategory.lean` | H3 |
| Cl55V4 spinor fragmentation | `Canonical/Cl55V4SpinorFragmentation.lean` | H1 |
| Yang-Baxter papers | `external_refs/papers/` | Background |
| Fibonacci braiding category | `Categorical/FibonacciBraiding.lean` | C1, C2 |
| Hexagon as cocycle | `Fibonacci/HexagonCocycle.lean` | C2 |
| SymPy witness | `tools/sympy/fibonacci_osp12_bridge.py` | Verification |

## Files to Create/Modify

1. **`Canonical/YangBaxterProof.lean`** — Main proof file (exists, needs lemmas A1-A3, B1-B4)
2. **`Categorical/FibonacciBraidedCategory.lean`** — BraidedCategory instance (new, needs C1)
3. **`Fibonacci/FibAnyonThm4.lean`** — Existing, `braid_relation` lemma to close
4. **`Canonical/GoldenRatioInvariants.lean`** — Existing, provides A1-A2 over ℝ, needs ℂ extension

## Estimated Effort

| Part | Lemmas | Difficulty | Files |
|------|--------|------------|-------|
| A: Scalars | 3 | Easy (ring algebra) | `YangBaxterProof.lean` |
| B: Matrices | 4 | Medium (4-entry 2×2) | `YangBaxterProof.lean` |
| C: Categorical | 2 | Hard (monoidal category) | `FibonacciBraidedCategory.lean` |

Total: 9 lemmas, 3 files, ~200 lines of Lean code.
