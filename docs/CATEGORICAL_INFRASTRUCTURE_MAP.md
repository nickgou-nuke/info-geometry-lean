# Categorical Infrastructure Map

> This document exists because LLM coding agents repeatedly lose context about
> what is already formalized and write redundant matrix-level code when the
> categorical infrastructure already exists. Read this before adding any new
> representation-theoretic or categorical content.

---

## 1. The Golden Rule

**The categorical/Grothendieck layer exists and is the owner layer.**
Matrix-level files are *instances* of categorical theorems, never replacements
for them. Before writing any new `def` or `theorem` at the matrix level, check
whether the categorical equivalent exists in the files below.

---

## 2. Grothendieck Group (Universal)

**File:** `Algebra/Grothendieck.lean`

The full universal Grothendieck group construction for additive commutative
monoids:

```lean
def GrothendieckRel (x y : M × M) : Prop := ∃ k : M, x.1 + y.2 + k = x.2 + y.1 + k
def grothendieckSetoid (M) [AddCommMonoid M] : Setoid (M × M)
def Grothendieck (M) [AddCommMonoid M] : Type _ := Quotient (grothendieckSetoid M)
```

**Closed owner theorems (Bucket 1):**
- `grothendieck_add_assoc`, `grothendieck_add_comm`, `grothendieck_zero_add`,
  `grothendieck_add_zero`, `grothendieck_add_left_neg`
- `grothendieckMap`, `grothendieckMap_add` (functoriality)
- `grothendieckProdEquiv : Grothendieck (A × B) ≃+ Grothendieck A × Grothendieck B`
- `grothendieckEquivInt : Grothendieck ℕ ≃+ ℤ` — **this is K₀(Spec F) ≅ ℤ**

**Gap:** The Fibonacci fusion algebra `τ ⊗ τ = 1 ⊕ τ` is not yet expressed as a
Grothendieck semiring structure. The file `FibonacciGrothendieckLimit.lean`
starts this but uses `AddCommGroup.DirectLimit`, not `Algebra.Grothendieck`.

---

## 3. Category-Theoretic Colimit Infrastructure

### 3a. Tensor Tower Colimit

**File:** `Canonical/TensorTowerColimit.lean`

The inductive colimit of a chain of modules `A_n` with bonding maps
`iota n : A n → A (n+1)` and a cone `psi n : A n → A_inf`:

```lean
variable (iota : ∀ n, A n →ₗ[R] A (n + 1))
variable (psi : ∀ n, A n →ₗ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)
```

**Closed theorems:**
- `psi_comp_iota_seq` — colimit commutativity by induction
- `protected_states_survive_colimit` — topological protection

**Connection:** This is the owner for the Fibonacci braid colimit.
`StableFibonacciAnyonBraidLimit.lean` should use `TensorTowerColimit`,
not write its own limit infrastructure.

### 3b. Erlangen Colimit Resolution

**File:** `Canonical/ErlangenColimitResolution.lean`

Resolves colimit inheritance of invariants via a global ambient algebra:

```lean
def resolveColimitInheritsInvariants_of_ambient
    (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
    (Invariants : ∀ n, SupergradedClosureAt (Chain n))
    (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invariants (n+1)))
    (A_infty : Type*) [Ring A_infty]
    (GlobalInvariants : SupergradedClosureAt A_infty)
    (global_embed : ∀ n, BondingIntertwiner (Invariants n) GlobalInvariants) :
    ColimitInheritsInvariants Chain Invariants Bonding
```

**Connection:** When the finite Fibonacci braid matrices embed into an infinite
braid group C*-algebra, this is the theorem that transports grade/invariant
structure to the colimit.

### 3c. Category Theory Cone Uniqueness

**File:** `Canonical/CategoryTheoryConeUniqueness.lean`

Uses `Mathlib.CategoryTheory.Limits.IsLimit` directly. This is the mathlib
category-theoretic colimit, not a custom one.

---

## 4. Categorical Fibonacci Surface

**File:** `Categorical/FibonacciBraiding.lean`

Theorem-level categorical surface (no packaging, no witnesses):

```lean
theorem F_sq (τ s : ℂ) (s_sq : s ^ 2 = τ) (tau_sq_add_tau : τ ^ 2 + τ = 1) :
    fibonacciFusionMatrix τ s * fibonacciFusionMatrix τ s = 1

theorem det_F (τ s : ℂ) (s_sq : s ^ 2 = τ) (tau_sq_add_tau : τ ^ 2 + τ = 1) :
    (fibonacciFusionMatrix τ s).det = -1

theorem B_eq_FRF (q : Units ℂ) (τ s : ℂ) :
    fibonacciBMatrix q τ s = fibonacciFusionMatrix τ s * fibonacciRMatrix q * fibonacciFusionMatrix τ s

theorem artin_relation (q : Units ℂ) (τ s : ℂ)
    (h_artin : fibonacciBMatrix q τ s * fibonacciBMatrix q τ s *
      fibonacciBMatrix q τ s * fibonacciBMatrix q τ s *
      fibonacciBMatrix q τ s = ...) : ...
```

**This is the owner file** for all categorical Fibonacci theorems.
Matrix-level files like `FibonacciParafermion.lean` and `FiniteFibonacci*.lean`
are the concrete realizations; `FibonacciBraiding.lean` is the surface.

**Not formalized:** The pentagon equation, the hexagon equation as categorical
coherence, the braided monoidal category structure.

---

## 5. Categorical Krein / Clifford / Quantum

### 5a. Real K-Category

**File:** `Quantum/RealKCategory.lean`

```lean
structure RealKVect where
  V : Type u
  [isAddCommGroup : AddCommGroup V]
  [isModule : Module ℝ V]
  K : V →ₗ[ℝ] V
  K_sq_neg_one : K ∘ₗ K = -LinearMap.id
```

**Theorems:**
- Complex action derived from `K` on each object
- Functor `ModuleCat ℂ ⥤ RealKVect` (complex vector spaces as `ℝ`-spaces with `K := I·`)

**Connection:** This is the categorical home for the `Spinor := ℝ × ℝ` with
`h = diag(1,-1)` and `f = [[0,0],[1,0]]`. The OSp(1|2) spinor module is a
`RealKVect` object with `K = h` (since `h² = I`, not `-I` — so it's a real
structure, not a complex one). The Krein symmetry `J = [[0,I],[I,0]]` is
another `RealKVect` structure on the doubled space.

### 5b. Real Majorana Category

**File:** `Quantum/RealMajoranaCategory.lean`

The categorical setting for Majorana fermions and Clifford algebras.

### 5c. Krein Category

**File:** `Krein/Category.lean`

Krein space categorical structure.

---

## 6. Hadjiivanov–Todorov Log CFT Monodromy

**Owner file:** `Clifford/LogCftMonodromy.lean`

```lean
def virasoroL0Cell (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := upperJordan h 1
def hadjiivanovMonodromy (h : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := ...
```

**Supporting files:**
- `Canonical/LogCftMonodromyBridge.lean` — `lowerHadjiivanovMonodromy`
- `OperatorAlgebra/LogExchangeMonodromy.lean` — lower/upper monodromy powers,
  exchange algebra completeness
- `Clifford/ExchangeSMatrixBridge.lean` — S-matrix bridge
- `Clifford/DiscreteMoebiusGroup.lean` — `moebius_hadjiivanov_unscaled_action`
- `Clifford/ModularCftBridge.lean` — modular `T`, `S` generators
- `Clifford/MonodromyFlowAdapter.lean` — monodromy → flow

**Not formalized:** The full Todorov–Hadjiivanov analytic exchange algebra
(documented as incomplete in `ExchangeSMatrixBridge.lean`).

---

## 7. GHT Connection: SL(2,ℝ)/U(1) Coset Parafermions

The Georgiev–Hadjiivanov–Todorov work describes:
- SL(2,ℝ)/U(1) coset CFT
- Parafermion currents with fractional conformal dimensions
- Braid group representations from the coset
- Logarithmic monodromy matrices (rank-2 Jordan cells)

**What exists in the repo:**

| GHT Concept | Repo Formalization | File |
|------------|-------------------|------|
| SL(2,ℝ) generators | `sl2E`, `sl2F`, `sl2H` with commutation | `Algebra/FibonacciParafermion.lean` |
| Real 2-dim spinor carrier | `Spinor := Fin 2 → ℝ` | `Algebra/OSp12.lean` |
| Weyl projectors | `WeylPlusProjector`, `WeylMinusProjector` | `Algebra/FibonacciParafermion.lean` |
| F-matrix as 𝔰𝔩₂ operator | `F_matrix_sl2_decomposition` | `Algebra/FibonacciParafermion.lean` |
| Parafermion fusion matrix | `F_matrix a b` with `IsFibonacciRelation` | `Canonical/FibonacciParafermionAtoms.lean` |
| Complex fusion matrix | `fibonacciFusionMatrix τ s` | `Canonical/FiniteFibonacciFusionMatrix.lean` |
| ℝ→ℂ coefficient bridge | `ofReal_F_matrix`, `ofReal_F_matrix_sq` | `Canonical/FibonacciParafermionFusionBridge.lean` |
| Log CFT monodromy | `hadjiivanovMonodromy h` | `Clifford/LogCftMonodromy.lean` |
| Modular SL(2,ℤ) | `modularT`, `modularS` | `Clifford/ModularCftBridge.lean` |
| Braid colimit | `psi_comp_iota_seq` | `Canonical/TensorTowerColimit.lean` |
| Grothendieck K₀ | `Grothendieck ℕ ≃+ ℤ` | `Algebra/Grothendieck.lean` |
| Categorical surface | `F_sq`, `det_F`, `artin_relation` | `Categorical/FibonacciBraiding.lean` |
| Continuous weights | `Weight := ℝ` | `Algebra/OSp12.lean` |
| f shifts weight by -2 | `spinor_f_matrix_sl2_weight_module_connection` | `Algebra/OSp12.lean` |

**What is missing (the real open debt):**

1. **Categorical pentagon/hexagon** — the Fibonacci fusion category as a
   braided monoidal category, with the F-matrix satisfying the pentagon
   equation and the braiding satisfying the hexagon equation.

2. **Colimit identification** — the theorem that the colimit of finite
   Fibonacci braid matrices (via `TensorTowerColimit`) acts as the
   Hadjiivanov monodromy on the parafermion Hilbert space.

3. **Analytic exchange algebra** — the full Todorov–Hadjiivanov exchange
   algebra (explicitly marked as incomplete in `ExchangeSMatrixBridge.lean`).

4. **Categorical Grothendieck semiring** — the Fibonacci fusion algebra
   expressed as a Grothendieck semiring structure on `Algebra/Grothendieck.lean`
   (currently `FibonacciGrothendieckLimit.lean` uses `AddCommGroup.DirectLimit`
   instead of the universal `Grothendieck` construction).

---

## 7b. Factored finite algebra layers

The repository has finite, theorem-safe entry points for reusable algebraic
blocks.  These files are bridge surfaces, not replacements for the categorical
owners above:

1. **Finite spin algebra** (`Algebra/FiniteSpinAlgebra.lean`) — concrete
   `2 × 2` complex spin-half ladder matrices `J_plus`, `J_minus`, `J_zero`,
   their commutator, a `SpinHalfBasis` interface, and the checked relations
   `[J_zero,J_plus]=J_plus`, `[J_zero,J_minus]=-J_minus`,
   `[J_plus,J_minus]=2 • J_zero`.
2. **Finite SUSY blocks** (`Algebra/FiniteSUSYBlocks.lean`) — a finite
   matrix interface `FiniteSUSYSystem` with `H_minus = A_dag * A`,
   `H_plus = A * A_dag`, the associativity-only intertwining identity
   `A * H_minus = H_plus * A`, and the two-state finite Witten trace readout.
3. **Arithmetic product gates** (`Arithmetic/ZetaProductGate.lean`) — two
   small scalar gate interfaces: `ProductZeroGate` for product annihilation and
   `ProductUnitGate` for product-one/lossless readouts.  This layer does not
   assert a zeta zero-location theorem or analytic continuation.

These layers are suitable inputs for later Cuntz/UHF, Aubert--Plymen, and
Super-TKK adapters only after those adapters supply explicit maps and checked
compatibility laws.

### Layer-4 guardrail: anyon braid quotient witnesses

The finite GAP smoke test
`tools/gap/verify_anyon_weyl_braids.g` checks only the abstract D-type
Artin/Coxeter quotient presentations:

* the D4 quotient has order `192` and maps bijectively to `W(D4)`;
* the D5 quotient has order `1920` and maps bijectively to `W(D5)`;
* `W(D4)` has a two-dimensional irreducible character.

This is group-theoretic evidence for finite quotient bookkeeping, not a proof
that a Fibonacci anyon braid image is `W(D4)` or `W(D5)`.  Before adding a Lean
owner for anyon braid quotients, fix the finite data being checked:

* exact braid generators, e.g. the existing Fibonacci `R` and `B = F R F`
  matrices or an explicitly named finite quotient representation;
* exact target group presentation, such as a specified Coxeter/Weyl group;
* a machine-readable certificate connecting the computed GAP group data to the
  Lean statement.

Do not identify Fibonacci braid images with `G₂(2)`, `W(D₄)`, `W(D₅)`,
split-octonion automorphisms, or geometric transport until the concrete finite
homomorphism and its image certificate are supplied.

---

## 8. The Correct Order of Operations

When adding new content:

1. **Check `Algebra/Grothendieck.lean` first** — if it's a Grothendieck group
   construction, use the universal one, don't rebuild it.

2. **Check `Categorical/` next** — if it's a categorical theorem about
   Fibonacci braiding, it belongs in `Categorical/FibonacciBraiding.lean`
   or a new file in `Categorical/`.

3. **Check `Canonical/TensorTowerColimit.lean`** — if it's a colimit of
   a chain of modules, use this infrastructure.

4. **Only then write matrix-level code** — in `Canonical/FiniteFibonacci*.lean`
   or `Algebra/FibonacciParafermion.lean`, as a concrete instance of the
   categorical theorem.

5. **Never write a bridge file** — use `import` directly. If two files need
   to connect, one imports the other. No `*Bridge.lean` files.

---

## 9. Build Status

| Layer | Status |
|-------|--------|
| `Algebra.Grothendieck` | ✅ Builds (clean) |
| `Algebra.OSp12` | ✅ Builds (clean) |
| `Algebra.FibonacciParafermion` | ✅ Builds (clean) |
| `Algebra.All` | ✅ Builds (8108 jobs) |
| `Categorical.FibonacciBraiding` | ✅ Builds |
| `Canonical.TensorTowerColimit` | ✅ Builds |
| `Canonical.ErlangenColimitResolution` | ✅ Builds |
| `Clifford.LogCftMonodromy` | ✅ Builds |
| `Quantum.RealKCategory` | ✅ Builds |
| `InfoGeometry.All` | ❌ Fails (pre-existing in `Arithmetic/`, `Canonical/`) |

---

## 10. Key Debts Marked Bucket 3

- `spinor_f_matrix_sl2_weight_module_connection` — documented in `OSp12.lean`
- `fibonacciFusion_on_module` — Fibonacci F-matrix on the spinor module,
  documented in `OSp12.lean`
- Colimit identification with Hadjiivanov monodromy — undocumented but implicit
- Analytic Todorov–Hadjiivanov exchange algebra — documented in
  `ExchangeSMatrixBridge.lean`
- Pentagon/hexagon equations for Fibonacci — not documented anywhere

---

*Last updated: 2026-06-02*

## 11. Finite metriplectic and central-root witness layer

This layer is a finite algebraic readout, not a smooth superKähler geometry
construction and not a physical thermodynamics theorem.

* `lean/InfoGeometry/Topology/Metriplectic.lean` — defines an algebraic
  `MetriplecticStructure` over a commutative ring with two supplied brackets,
  Hamiltonian/entropy observables, and explicit annihilation laws.  Closed
  theorems include `energy_conservation`, `entropy_evolution`, and
  `metriplectic_packet`.
* `tools/sympy/parafermion_clifford_roots.py` — exact finite diagnostic for a
  real central root with `J^2 = -I`; optional `clifford`/`galgebra`
  availability is diagnostic only.
* `tools/gap/metriplectic_superkahler.g` — finite center/grading smoke test;
  it does not prove super-Kähler geometry or metriplectic thermodynamics.
* `docs/MetriplecticSuperkahlerDigest.tex` — digest explicitly recording the
  finite algebraic scope and the missing smooth/superKähler hypotheses.

Guardrail: do not promote this packet to a global superKähler theorem, a
Hestenes--Krein metric theorem, a first/second law of thermodynamics theorem,
or a categorical braided-Clifford theorem without explicit owner definitions
and kernel-checked coherence/compatibility proofs.

---

## 12. Albert-Freudenthal Spectral Reduction & Exceptional Tripotency

**Files:**
- `lean/InfoGeometry/OperatorAlgebra/AlbertCubicTripotent.lean`
- `tools/sympy/freudenthal_cubic_reduction.py`

**Mathematical role:**
- Formalizes the cubic characteristic polynomial of the 27-dimensional Albert algebra.
- Defines the Freudenthal cubic invariants (`trace1`, `trace2`, `norm`).
- Provides the exact constructive proof `tripotency_is_cubic_rank2_special`, proving that setting the Freudenthal invariants to the trace-zero, quadric-negative vacuum threshold natively maps the Albert element into a strict Jordan tripotent ($P^3 = P$) via pure commutative ring arithmetic.
- Validates the coordinate-free reduction matching the topological boundaries of the Octonionic Cayley Projective Plane ($\mathbb{OP}^2$) directly in Lean without relying on complex continuous meshes.

**Boundary restrictions:**
- Does *not* automatically embed differential manifold calculations or continuous exceptional Lie group extensions. It evaluates purely the polynomial algebra limits bridging the non-associative exceptional geometry via characteristic trace boundaries.
