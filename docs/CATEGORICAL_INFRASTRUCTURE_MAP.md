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

## 7b. Factored Architecture Layers

The repository has been hygienically refactored to decouple specific algebraic behaviors from concrete coordinates, separating abstract definitions across three core layers:

1. **Layer 1: Core Spin Algebra** (`Algebra/FiniteSpinAlgebra.lean`) — Isolates the uncomplexified SU(2) angular momentum generators ($J_+, J_-, J_0$) and standard ladder commutation relations.
2. **Layer 2: Finite SUSY / Parity Supergraded Blocks** (`Algebra/FiniteSUSYBlocks.lean`) — Structures the $\mathbb{Z}_2$ supergraded Lie algebra using decoupled supercharges ($A, A^\dagger$) and verifies the trace-free Witten index property on finite block-diagonal sectors.
3. **Layer 3: Arithmetic Zeta Product-Zero Gate** (`Arithmetic/ZetaProductGate.lean`) — Implements the abstract product-zero gate over partition functions to ensure anomaly-free scaling.

These three layers form the canonical entry points for downstream structural linkages like the CuntzUHFBridge.

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
