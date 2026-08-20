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

**Closed owner theorems for Fibonacci Fusion Ring:**
- `FibonacciGrothendieckRing.lean`: Expresses the additive Grothendieck completion `FibonacciK0 := Grothendieck FibFusionMonoid` using `Algebra/Grothendieck.lean` and connects to the concrete `ℤ²` fusion-ring model `τ² = 1 + τ`.
- `K0FibonacciRing.lean`: Ring isomorphism between `FibonacciK0` and the golden quadratic integer ring $\mathbb{Z}[\tau]/(\tau^2 - \tau - 1)$.

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

**Formalized:** The pentagon equation (via Rohozhkin matrix chart) and the hexagon equation (via Artin relation) as finite categorical coherence.
**Not formalized:** The full mathlib `BraidedCategory` instance.

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
| Split composition algebra typeclass (`q ∈ {2,4,8}`) | `SplitCompositionAlgebra K A` | `Algebra/SplitJordanSpinor.lean` |
|  Hermitian `2×2` Jordan matrix J₂(𝔸_s) | `JordanMatrix2 K A` | `Algebra/SplitJordanSpinor.lean` |
|  J₂ determinant boundary formula | `determinant := αβ - N(Z)`; signature/isomorphism remains a proof obligation | Fioresi et al. Eq. (3.4)-(3.5) |
|  Spinor carrier 𝔸_s² | `Spinor2 A` | `Algebra/SplitJordanSpinor.lean` |
|  Raw 2×2 matrix action on 𝔸_s² | `SplitMatrix2.spinorAction` | Fioresi et al. Eq. (4.11), (4.15), (4.19) |
|  Klein-spinor orbit representative predicates | `KleinSpinorOrbitStratification` | Fioresi et al. §5.1 |
|  Concrete split-complex spinor representatives `(1,0)`, `(E,0)`, `(E,E)` | `genericRep`, `nullRep`, `diagonalNullRep` | `Algebra/KleinSpinorOrbit.lean` |
|  Raw `2×2 C_s` determinant-one coordinate matrices | `CsMatrix2.DetOne`, `CsSL2` | theorem-safe local stand-in for `SL(2,C_s)` |
|  Eq. 5.22–5.24 local stabilizer equations/families | `CsSL2.eq_5_22_generic_unipotent_stabilizes`, `CsSL2.eq_5_22_generic_stabilizer_shape`, `CsSL2.eq_5_23_null_scalar_conditions`, `CsSL2.eq_5_23_null_first_column_Ebar_shape`, `CsSL2.eq_5_23_null_Ebar_family_stabilizes`, `CsSL2.eq_5_24_diagonal_null_row_sum_iff` | stabilizer equations only; no full orbit-classification or dimension theorem |
|  Planar inversion and `J₂(C_s)` Jordan--Cayley coordinate identities | `planar_inversion_line_to_circle_numerator`, `CsJordan.det_cayleyInversion`, `CsJordan.cayleyInversion_involutive` | `Algebra/JordanCayleyInversion.lean`; finite coordinate identities only, no CCC/Spin(5,5)/octonionic inverse theorem |
|  Concrete split-complex/split-quaternion trace-reversal determinant packets | `JordanCayleyInversionCs.Herm2x2Cs.fundamental_identity`, `JordanCayleyInversionCs.Herm2x2Cs.klein_quadric_equation`, `JordanCayleyInversionHs.Herm2x2Hs.fundamental_identity`, `JordanCayleyInversionHs.Herm2x2Hs.klein_quadric_equation` | diagonal coordinate packet identities only; not a full matrix inverse theorem or structure-group isomorphism |
|  Split-octonionic `q=8` Jordan--Cayley proof boundary | `JordanCayleyBoundary`, `SplitOctonionicBoundary.ambient_dimension_eq_ten`, `SplitOctonionicBoundary.on_klein_quadric` | `Algebra/SplitOctonionicJordanCayleyBoundary.lean`; packages proof obligations for a concrete `J₂(O_s)` model, no `Spin(5,5)` theorem |
|  Concrete Zorn split-octonion norm/conjugation ingredient | `JordanCayleyInversionOs.detZ_mulZ_composition`, `JordanCayleyInversionOs.Herm2x2Os.mul_conj_eq_det`, `JordanCayleyInversionOs.Herm2x2Os.fundamental_identity` | `Algebra/JordanCayleyInversionOs.lean`; determinant packet and conjugation/norm identity only, not a full octonionic matrix inverse or conformal group theorem |
|  Split-octonionic coordinate stratum predicates | `Herm2x2OsQ.Stratum`, `Herm2x2OsQ.stratum_exhaustive`, `Herm2x2OsQ.mulTraceReversal_vanishes_of_isNull` | `Algebra/JordanCayleyOrbitStratification.lean`; zero/null/generic predicate case split only, not an `SL(2,O_s)`, `Pin(5,5)`, `O(5,5)`, or quotient orbit classification |
|  Coordinate determinant strata bridge | `cs_null_orbit`, `hs_null_orbit`, `os_null_orbit`, `uniform_null_orbit`, `uniform_fundamental_identity`, `OrbitClassificationBridge.osq_stratum_exhaustive` | `Algebra/OrbitClassification.lean`, `Algebra/OrbitClassificationBridge.lean`; determinant-null/generic coordinate packets only, not full group orbit classification, CCC, analytic conformality, or global conformal inversion |
|  Five-graded split-weight socket | `SplitIdempotents`, `Weight5`, `FiveGradedDecomposition`, `NullWeightSector`, `right_mul_E_of_split`, `right_mul_Ebar_of_split`, `split_idempotent_projection_packet` | `Algebra/FiveGradedTKK.lean`; finite `E/Ebar` idempotent projection/extraction socket for refining null sectors by weight, not uniqueness of decomposition, not a full `J₂(O_s)` construction, and not a `Spin(5,5)`/`Pin(5,5)` orbit classification |
|  Lightcone compensation projectors | `LightConePair`, `LightConePair.pPlus`, `LightConePair.pMinus`, `LightConePair.pPlus_idem`, `LightConePair.pMinus_idem`, `LightConePair.pPlus_mul_pMinus`, `LightConePair.pMinus_mul_pPlus`, `LightConePair.pPlus_add_pMinus_eq_one`, `LightConePair.lightcone_compensation_packet` | `Algebra/LightConePair.lean`; exact associative-ring consequences of `e₊²=e₋²=0` and `e₊e₋+e₋e₊=1`, not a Clifford module, Pin action, or physical Witten-index theorem |
|  Five-graded Möbius/Witten globality capstone | `WittenMobiusIndex`, `witten_mobius_index_zero_of_local_compensation`, `witten_four_layer_parity_sum_zero`, `five_graded_mobius_witten_globality_packet`, `GradeTwoInformationLedger.stateAt`, `GradeTwoInformationLedger.recursive_visibleLoss_eq_gradeTwoGain` | `Canonical/FiveGradedMobiusWittenGlobality.lean`, `OperatorAlgebra/FiveGradedDefectAbsorption.lean`; closed conditional bridge packaging five-grade inversion owner laws, Möbius/chiral trace zero, four-layer Witten parity sum zero, and recursive grade-two compensation; no CCC, RH, black-hole unitarity, physical Witten index, conformal-group equivalence, or orbit classification |
|  Mathlib Clifford split `(5,5)` Pin/Spin names and finite relations | `q55`, `pinGroup55`, `spinGroup55`, `r₀_sq`, `r₅_sq`, `anticomm`, `v4_relation`, `ProjectiveSignEq`, `r₅_projective_involutive` | `Physics/Pin55Formal.lean`; uses mathlib `CliffordAlgebra`/`pinGroup`/`spinGroup` names and exact generator identities, but does not prove a topological quotient, literal four-element V4 subgroup, CCC, conformal inversion, or orbit classification |
|  Central sign conjugation invariance | `unitConjugation`, `scalarSignUnits`, `unitConjugation_one`, `unitConjugation_neg_one`, `unitConjugation_scalarSign_trivial`, `unitConjugation_neg_eq` | `Physics/CentralizerInvariance.lean`; exact ring/unit identity that conjugation by `-1` is trivial, not a constructed `Pin(5,5) → O(5,5)` double-cover, not a quotient by `{±1}`, and not a full orbit-classification theorem |
|  Finite `O(5,5)`/V4/Klein-bottle shadows | `splitPair55`, `negAll_preserves_splitPair`, `reflPair0_preserves_splitPair`, `reflPair1_preserves_splitPair`, `reflPair0_comm_reflPair1`, `kleinBottle_affine_relation`, `finite_o55_v4_klein_packet` | `Topology/O55V4KleinBottleFinite.lean`; exact coordinate identities over `ℚ` only, not the Lie group `O(5,5)`, `Pin(5,5)`, CCC, topological quotient construction, or orbit classification |
|  Generic quadratic zero/null/generic strata | `OrbitStratum`, `orbit_classify_trichotomy`, `classifyOrbit`, `PreservesOrbitStrata`, `map_stratum_of_preserves`, `q55_orbit_classify_trichotomy`, `classifyQ55Orbit`, `q55_epsilon0_isGeneric`, `q55_epsilon5_isGeneric`, `q55NegAll_preserves_orbit_strata`, `q55NegAll_maps_stratum` | `Topology/SpinorOrbitStratum.lean`; predicate/case-split and explicit quadratic-value-preserving map layer for quadratic forms and the concrete `q55`, not spin-action invariance or full orbit classification |
|  Finite Pauli `B₃` braid shadow | `sigma1_sq`, `sigma2_sq`, `sigma3_sq`, `sigma1_sigma2_anticomm`, `sigma1_mul_sigma2`, `pauli_braid_relation`, `pauli_braid_triple_product`, `pauli_b3_braid_shadow_packet` | `Canonical/PauliBraidB3.lean`; exact `2 × 2` complex matrix identity for `1+iσ₁` and `1+iσ₂`, not a full `Bₙ` representation, not a biquaternion/Clifford isomorphism theorem, not Hecke/BMW/quantum-supergroup centralizer theory, and not an `osp(1|8)` formalization |
|  Witten--Möbius chiral parity compensated shadow | `chiralParityIndex`, `wittenMoebiusChiralParityIndex_ePlus_eMinus_zero`, `anomalyFree_zero`, `compensatedRecursion_eq_splitOne`, `compensatedRecursion_chiralParityIndex_zero`, `FiveGradedCompensatedParityShadow.parity_index_zero`, `FiveGradedCompensatedParityShadow.grade_zero_setwise_stable`, `witten_moebius_chiral_parity_packet` | `Canonical/WittenMoebiusChiralParityIndex.lean`; finite `e₊/e₋` compensation and zero parity-index recursion tied to the existing five-graded closure owner, not a global Möbius theorem, full Witten index theorem, or full 5-graded super-TKK closure |
|  Reduced-structure/spin isomorphism boundary | `ReducedStructureSpinBoundary` | Fioresi et al. Eq. (3.6) |
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

1. **Full Braided Category Instance** — the Fibonacci fusion category as a
   `BraidedCategory` typeclass instance (the finite matrix pentagon and hexagon
   coherences are formalized, but not the abstract functorial mathlib instance).

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
- Full `BraidedCategory` instance — (pentagon/hexagon coherences are verified in `Categorical/`)

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
- **Integration:** The `P^3 = P` collapse is physically wired into the $\mathfrak{g}_0$ structure algebra of the 5-graded Super-TKK framework via `superTKK_of_Freudenthal` in `SuperTKK.lean`.

---

## 13. Delaunay Pentagon Pure-Braid Invariant

Source: Rohozhkin, “Pentagon equations, Delaunay triangulations and pure braid group invariant”.

Files:
- `lean/InfoGeometry/Topology/DelaunayFlipMatrix.lean`
- `lean/InfoGeometry/Topology/RohozhkinPentagonMatrix.lean`
- `lean/InfoGeometry/Topology/DelaunayPureBraidInvariant.lean`
- `lean/InfoGeometry/Topology/PureBraidGroup.lean`
- `lean/InfoGeometry/Topology/DelaunayFlipMatrixEmbeddings.lean`
- `lean/InfoGeometry/Topology/DelaunayPureBraidRepresentation.lean`
- `tools/sympy/rohozhkin_pentagon_matrices.py`

Closed finite target:
- rational local flip matrices over `ℚ`;
- `flip_inverse_identity`, the local inverse flip identity;
- `flip_far_commute_embedded_blocks`, far-commutativity for independent
  disjoint `2 × 2` blocks embedded in a `4 × 4` transport matrix;
- `pentagon_appendix_identity`, the explicit Appendix A five-flip `3 × 3`
  rational pentagon product;
- `rohozhkinMatrix`, a presentation-level product of witnessed flip matrices;
- `rohozhkin_invariant_under_inverse_move`,
  `rohozhkin_invariant_under_far_commute_move`, and
  `rohozhkin_invariant_under_pentagon_move`, the three explicitly witnessed
  flip-word replacement invariance theorems;
- `DelaunayEquiv` and `rohozhkinQuotientMatrix`, a quotient-level matrix
  readout for words modulo the generated move relation;
- `PureBraid.PureBraidGenerator`, `PureBraid.pureBraidRelations`, and
  `PureBraid.PB`, an explicit mathlib `PresentedGroup` boundary for pure
  braids with noninterleaving far-commutativity, three-index, and four-index
  relator families;
- `trivialPureBraidGeneratorAssignment` and `trivial_pure_braid_representation`,
  a deliberately trivial descent socket for testing `PresentedGroup.lift`, not
  the Rohozhkin monodromy representation.

Open target:
- deriving the Appendix A matrices from a general `2n+1` triangle-basis
  insertion map;
- constructing the nontrivial Rohozhkin generator assignment into
  `Units (Matrix (Fin (2n+1)) (Fin (2n+1)) ℚ)`;
- proving that this nontrivial assignment kills every explicit
  `PureBraid.pureBraidRelations` relator;
- the nontrivial pure-braid homomorphism `PB_n → GL_{2n+1}(ℚ)` with
  invertibility in the target group;
- knot invariants from braid closure and Markov moves.

Boundary:
- this is a rational Delaunay/pentagon invariant;
- it is not a unitary anyon braid representation;
- it is not a Fibonacci `F/R` category construction;
- it does not yet give a knot invariant until Markov-move invariance is separately proved.

### Jordan Algebra Linearization (New)
Files:
- `lean/InfoGeometry/Algebra/JordanLinearization.lean`

Mathematical role:
- Defines the general commutative, non-associative `JordanAlgebra` typeclass over a commutative ring `K`.
- Establishes the theorem boundary for the `linearized_jordan_identity` under translation `x → x + z`.
- Provides the axiomatic base required for graded Lie transformations in TKK algebras.

Boundary:
- Strictly algebraic; does not specialize to specific split algebras or spatial dimensions.
- The linearized identity proof is deferred (verified numerically).

### Pin(5,5), Spin(5,5), O(5,5) quotients (Existing)
Files:
- `lean/InfoGeometry/Physics/Pin55Formal.lean` — `pinGroup55`, `spinGroup55`, V4 relation.

Status:
- `pinGroup55`, `spinGroup55`, `q55` (split (5,5) form) defined.
- `r0_sq`, `r5_sq`, anticomm, `v4_relation` proved.
- O(5,5) and {I,-I} quotients not yet formalized.
- Full orbit classification (zero/null/generic) open boundary.

### GAP / Sage / SymPy tool layer
Directories:
- `tools/gap/` (33 files) — finite field shadows for all split-algebra and group identities.
- `tools/sage/` (19 files) — exact rational/GF witnesses.
- `tools/sympy/` (14 files) — Pin(5,5), Klein spinor orbit, strata.

These tools provide cross-verification but are not part of the Lean build.

---

## Packet-Scoped Audit Classification

### Packet A: Finite Clifford/Jordan/Spinor Identities — **CLOSED**

Files:
- `Physics/Pin55Formal.lean` — pinGroup55, spinGroup55, q55, V4 relation
- `Algebra/GeometricBridge.lean` — Cs/Hs/Os fundamental identity re-exports
- `Algebra/KleinSpinorOrbit.lean` — stabilizer equations (5.22)–(5.24)
- `Algebra/KleinSpinorOrbitSocketClosure.lean` — socket closure theorems
- `Algebra/JordanCayleyInversionCs.lean` — X·X̃ = −det·I for (2,2)
- `Algebra/JordanCayleyInversionHs.lean` — same for (3,3)
- `Algebra/JordanCayleyInversionOs.lean` — same for (5,5)
- `Algebra/OrbitClassification.lean` — null/generic determinant strata
- `Algebra/Cl11Fermions.lean` — {b, b†} = 1 from Cl(1,1)
- `Algebra/CubicJordanSTU.lean` — (X♯)♯ = N·X for diagonal STU
- `Algebra/OrbitStratification.lean` — orbit_classification (zero/non-zero)
- `Algebra/SplitJordanSpinor.lean` — typeclass + boundary sockets

**Zero `sorry` / `axiom` across all files.** Every header honestly documents what it does **not** prove.

### Packet B: Rohozhkin/Delaunay Pure-Braid Layer — **SCOPED MATRIX BOUNDARY**

Files:
- `Topology/PureBraidGroup.lean` — presented group boundary (explicit relators, 0 sorry)
- `Topology/DelaunayPureBraidInvariant.lean` — local Delaunay move-invariance theorems
- `Topology/DelaunayPureBraidRepresentation.lean` — quotient readout / GL target boundary
- `Topology/RohozhkinMatrix.lean` — concrete generator-matrix data

Mathematical status:
- Rohozhkin/Delaunay data support a finite pure-braid matrix boundary.
- This layer is not a physical five-graded globality theorem and does not feed Packet C automatically.
- A closed nontrivial `PB → GL` homomorphism still requires the generator assignment and all relator checks to be kernel-proved.

### Packet C: Five-Graded Global Compensation & Witten/Möbius Closure — **CLOSED CONDITIONAL BRIDGE**

Files:
- `Canonical/FiveGradedMobiusWittenGlobality.lean` — capstone packaging theorem (zero `sorry`, closed conditional bridge) containing:
  - `ConformalFiveGradeSystem` structure (source/sink/incoming/outgoing/center closure as structural witness fields)
  - `GradeTwoInformationLedger` structure (visibleLoss_eq_gradeTwoGain as structural witness field)
  - `stateAt` definition (recursive state evolution)
  - `recursive_visibleLoss_eq_gradeTwoGain` induction proof
  - `five_graded_mobius_witten_globality_packet` capstone theorem

Context files:
- `Algebra/FiveGradedTKK.lean` — E/Ē idempotent split, 5-weight index, right-mul extraction
- `OperatorAlgebra/FiveGradedDefectAbsorption.lean` — grade-routing and grade-two compensation ledger
- `Canonical/ConformalFiveGradeInversion.lean` — source/sink, incoming/outgoing, and center duality from the five-grade inversion laws
- `Canonical/MobiusChiralClosure.lean` — χ_global_4 and Möbius-twisted trace = 0
- `Arithmetic/WittenParityIndex.lean` — +1, −1, +1, −1 parity sequence

Mathematical status:
- **Closed conditional bridge**: zero `sorry` / local `axiom`.
- `ConformalFiveGradeSystem.source_sink_closure`, `incoming_outgoing_closure`, `center_stability` are **structural witness fields** — the theorem does not prove them; it packages them from instantiation sites.
- `GradeTwoInformationLedger.visibleLoss_eq_gradeTwoGain` is a structural witness field.
- `recursive_visibleLoss_eq_gradeTwoGain` is kernel-proved by induction on the witness field.
- Möbius trace cancellation and Witten four-layer parity cancellation are imported finite witnesses, not analytic physics derived from the Jordan layer alone.
- The capstone `five_graded_mobius_witten_globality_packet` is a **closed conditional bridge** that packages the five-grade closure fields, Möbius trace zero, Witten parity sum zero, and recursive grade-two compensation into a single conjunction theorem.

Boundary:
- Does not prove the concrete existence of a conformal five-grading — that is the instantiation site's burden.
- Does not prove CCC.
- Does not prove black-hole unitarity / Page curve.
- Does not prove analytic superconformal index theory, analytic continuation, zeta, or RH claims.
- Does not prove complete orbit classification.
- Does not prove full physical Witten-index theorem.
- Does not prove global conformal-group equivalence.
- Does not prove a Delaunay pure-braid → GL₂ₙ₊₁(ℚ) homomorphism.

### Supergraded Five-Graded Bridge (New)
File:
- `Canonical/SupergradedFiveGradedBridge.lean`

Status: **CLOSED** (0 sorry, 0 axiom).
- Proves `witten_mobius_bridge`: packages Möbius chiral trace zero (both χ and twisted)
  and Witten 4-layer parity sum zero into a single bridge theorem.
- Connects the `SupergradedBracket`, `OSp12.OperatorSurface`, and five-graded closure layers
  through the supertrace cancellation mechanism.
