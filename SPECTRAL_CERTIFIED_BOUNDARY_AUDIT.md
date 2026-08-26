# Spectral/Algebra Certified Boundary Audit

**Date**: 2026-08-26
**Auditor**: AI Agent (per user request: option 3 → 2)

---

## Executive Summary

The `Spectral/Algebra` directory contains a **kernel-clean algebraic spectral sequence** up to and including **bounded page stabilization**. The convergence theorem (`Convergence.lean`) has **dependent-type API mismatches** and should remain a documented frontier. The correct path forward is **Route B**: build three separate bridges from the certified stabilization owner to the existing categorical colimit infrastructure (`TensorTowerColimit`, `ErlangenColimitResolution`).

---

## File-by-File Status

| File | Kernel Status | Key Exports | Notes |
|------|---------------|-------------|-------|
| `ExactCouple.lean` | ✅ **Clean** | `ExactCouple` structure, `differential`, `differential_comp_differential` | Core exact couple with bidegree shifts; `d = j ∘ k`, `d² = 0` proved |
| `DerivedCouple.lean` | ✅ **Clean** | `DerivedD`, `DerivedE`, `derivedI`, `derivedJ`, `derivedK`, three exactness theorems | Full derived couple construction with all exactness proofs |
| `PageStabilization.lean` | ✅ **Clean** | `differential_eq_zero_of_domain_eq_zero`, `differential_eq_zero_of_codomain_eq_zero`, `targetCycles_eq_top_of_differential_eq_zero`, `targetBoundariesInCycles_eq_bot_of_differential_eq_zero`, `derivedEEquivOfAdjacentDifferentialsZero`, `directDerivedEEquivOfAdjacentDifferentialsZero` | **One-step stabilization**: zero adjacent differentials ⇒ homology ≃ module |
| `IteratedDerivedCouple.lean` | ✅ **Clean** | `Stage` (Σ-type), `deriveStage`, `iteratedStage`, `page`, `pageDifferential`, `iteratedStage_succ_E` | Iteration via sigma-bundled `ModuleCat`; next page = homology of current |
| `IteratedPageStabilization.lean` | ✅ **Clean** | `iteratedPageSuccEquivOfAdjacentDifferentialsZero`, `iteratedPageEquivOfEventuallyAdjacentDifferentialsZero`, `iteratedPageEquivOfEventuallyAdjacentTermsZero` | Multi-step stabilization from PageStabilization lemmas |
| `ConvergenceCore.lean` | ✅ **Clean** | `EventualPageStabilization`, `BoundedPageStabilization`, `EventualPageStabilization.equiv`, `BoundedPageStabilization.equiv` | Contract-based stabilization (independent of numerical bounds) |
| `ExactCoupleFiltration.lean` | ✅ **Clean** | `incomingIIterate`, `imageFiltration`, `associatedGraded`, `filtrationJ`, `associatedGradedZeroEquivEOfKZero` | **Filtration reconstruction**: image filtration of `i`-iterates, associated graded, bridge to `E` terms when `k = 0` |
| `Convergence.lean` | ⚠️ **Frontier** | `IsBounded`, `iteratedPageEquivOfBounded`, `iteratedPageEquivOfBounded_from`, `iteratedPageEquivOfBounded_any` | **API mismatches**: `IsBounded` expects `incomingIIterate` on iterated stages but degree maps shift; `ModuleCat` coercions; `Elb_iterate` type transport issues. Keep as documented frontier. |

---

## Certified Carriers and Morphisms (The "Stable API")

### 1. Page/Stage Index Type
```lean
I : Type v  -- arbitrary indexing type (e.g., ℤ × ℤ for bidegree)
n : ℕ       -- page number (iteration count)
```

### 2. Stabilized/Equal Pages
**Theorem**: `IteratedPageStabilization.iteratedPageEquivOfEventuallyAdjacentTermsZero`
```lean
noncomputable def iteratedPageEquivOfEventuallyAdjacentTermsZero
  (S : Stage R I) (p : I) (N m : ℕ) (hNm : N ≤ m)
  (hIncomingTerm : ∀ n, N ≤ n → ∀ x : page S n (differentialDegree⁻¹ p), x = 0)
  (hOutgoingTerm : ∀ n, N ≤ n → ∀ x : page S n (differentialDegree (differentialDegree p)), x = 0) :
  (page S m p : Type u) ≃ₗ[R] (page S N p : Type u)
```
**Carriers**: `page S m p`, `page S N p` (both `ModuleCat.{u} R`, i.e., `Type u` with `AddCommGroup` and `Module R`)
**Morphism**: Linear equivalence `≃ₗ[R]`

**Contract version** (`ConvergenceCore.lean`):
```lean
structure EventualPageStabilization (S : Stage R I) (p : I) (N : ℕ) where
  incoming_zero : ∀ n, N ≤ n → ∀ x : page S n (differentialDegree⁻¹ p), x = 0
  outgoing_zero : ∀ n, N ≤ n → ∀ x : page S n (differentialDegree (differentialDegree p)), x = 0

noncomputable def EventualPageStabilization.equiv {S} {p} {N m} (h : EventualPageStabilization S p N) (hNm : N ≤ m) :
  (page S m p : Type u) ≃ₗ[R] (page S N p : Type u)
```

### 3. Map Between Successive Pages
**From `IteratedDerivedCouple.lean`**:
```lean
noncomputable def pageDifferential
  (S : Stage R I) (n : ℕ) (p : I) :
  (page S n p : Type u) →ₗ[R] (page S n (pageDifferentialDegree S n p) : Type u) :=
  (iteratedStage S n).couple.differential p
```
**From `IteratedPageStabilization.lean`** (successor page equivalence when differentials vanish):
```lean
noncomputable def iteratedPageSuccEquivOfAdjacentDifferentialsZero
  (S : Stage R I) (n : ℕ) (p : I)
  (hIncoming : (iteratedStage S n).couple.differential (differentialDegree⁻¹ p) = 0)
  (hOutgoing : (iteratedStage S n).couple.differential (differentialDegree (differentialDegree p)) = 0) :
  (page S (n + 1) p : Type u) ≃ₗ[R] (page S n p : Type u)
```

### 4. Filtration Carrier
**From `ExactCoupleFiltration.lean`**:
```lean
noncomputable def incomingIIterate (C : GradedExactCouple ...) : ∀ n p, D (backwardIIndex iDeg n p) →ₗ[R] D p
noncomputable abbrev imageFiltration (C : GradedExactCouple ...) (n : ℕ) (p : I) : Submodule R (D p) := LinearMap.range (C.incomingIIterate n p)
noncomputable abbrev associatedGraded (C : GradedExactCouple ...) (n : ℕ) (p : I) := (C.imageFiltration n p) ⧸ C.imageFiltrationStep n p
noncomputable def toAssociatedGraded (C : ...) (n : ℕ) (p : I) : C.imageFiltration n p →ₗ[R] C.associatedGraded n p
```
**Bridge to `E` terms** (when `k = 0`):
```lean
noncomputable def associatedGradedZeroEquivEOfKZero
  (C : GradedExactCouple ...) (p : I) (hk : C.k (jDeg (iDeg p)) = 0) :
  C.associatedGraded 0 (iDeg p) ≃ₗ[R] E (jDeg (iDeg p))
```

### 5. Existing Colimit Infrastructure Targets

#### `TensorTowerColimit.lean` (Canonical)
```lean
variable (A : ℕ → Type*) [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
variable (iota : ∀ n, A n →ₗ[R] A (n + 1))
variable (A_inf : Type*) [AddCommGroup A_inf] [Module R A_inf]
variable (psi : ∀ n, A n →ₗ[R] A_inf)
variable (psi_comm : ∀ n, (psi (n + 1)).comp (iota n) = psi n)

def iota_seq (n : ℕ) : ∀ m, A n →ₗ[R] A (n + m)

theorem psi_comp_iota_seq (n m : ℕ) : (psi (n + m)).comp (iota_seq A iota n m) = psi n

variable (colimit_kernel : ∀ (n : ℕ) (x : A n), psi n x = 0 → ∃ m, iota_seq A iota n m x = 0)

def IsTopologicallyProtected (n : ℕ) (x : A n) : Prop := ∀ m, iota_seq A iota n m x ≠ 0
theorem protected_states_survive_colimit (n : ℕ) (x : A n) (h_prot : IsTopologicallyProtected A iota n x) : psi n x ≠ 0
```

#### `ErlangenColimitResolution.lean` (Canonical)
```lean
def resolveColimitInheritsInvariants_of_ambient
  (Chain : ℕ → Type*) [∀ n, Ring (Chain n)]
  (Invariants : ∀ n, SupergradedClosureAt (Chain n))
  (Bonding : ∀ n, BondingIntertwiner (Invariants n) (Invarints (n+1)))
  (A_infty : Type*) [Ring A_infty]
  (GlobalInvariants : SupergradedClosureAt A_infty)
  (global_embed : ∀ n, BondingIntertwiner (Invariants n) GlobalInvariants) :
  ColimitInheritsInvariants Chain Invariants Bonding
```

---

## Identified Gaps (The Three Bridges Needed)

Following the user's decomposition, the convergence claim `E_∞ ≃ gr H ≃ colim E_r` requires:

### Bridge 1: `SpectralStablePage` (Already certified)
**Input**: `EventualPageStabilization S p N` or `BoundedPageStabilization S`
**Output**: `(page S m p) ≃ₗ[R] (page S N p)` for all `m ≥ N`
**Status**: ✅ **DONE** in `ConvergenceCore.lean` and `IteratedPageStabilization.lean`

### Bridge 2: `SpectralAssociatedGradedReconstruction` (Missing)
**Input**: 
- Stabilized page data at index `p`
- Filtration from `ExactCoupleFiltration` on the *limiting* exact couple (which is the stage at page `N`)
- Hypothesis: `k = 0` at the relevant degree (vanishing of the outgoing `k` map)
**Output**: `StablePage S N p ≃ₗ[R] AssociatedGraded C N (iDeg p)` where `C` is the exact couple at stage `N`
**File to create**: `SpectralAssociatedGradedReconstruction.lean`
**Dependencies**: `ExactCoupleFiltration.associatedGradedZeroEquivEOfKZero`, `IteratedPageStabilization.iteratedPageEquivOfEventuallyAdjacentTermsZero`

### Bridge 3: `SpectralColimitComparison` (Missing)
**Input**: 
- A directed system `A : ℕ → Type*` built from the stabilized pages (or their associated graded pieces)
- Linear maps `iota : ∀ n, A n →ₗ[R] A (n + 1)` coming from the page equivalences
- Compatibility with `TensorTowerColimit` or `ErlangenColimitResolution` interface
**Output**: `AssociatedGraded ... ≃ₗ[R] TensorTowerColimit ...` (or canonical map + injectivity/surjectivity)
**File to create**: `SpectralColimitComparison.lean`
**Dependencies**: `TensorTowerColimit.psi_comp_iota_seq`, `ErlangenColimitResolution.resolveColimitInheritsInvariants_of_ambient`

---

## Immediate Next Step

**Create `SpectralAssociatedGradedReconstruction.lean`** as the first new owner file. It should:

1. Take a `Stage R I` and a page index `p`
2. Assume `EventualPageStabilization S p N` (from Bridge 1)
3. Assume the limiting exact couple at stage `N` has `k = 0` at the relevant degree
4. Use `ExactCoupleFiltration.associatedGradedZeroEquivEOfKZero` to connect the stabilized page to the associated graded
5. Produce: `StablePage S N p ≃ₗ[R] AssociatedGraded (iteratedStage S N).couple N (iDeg p)`

This isolates the filtration/exact-couple hypotheses from the colimit comparison, exactly as the user specified.

---

## Appendix: Convergence.lean Specific Issues (For Reference)

The `Convergence.lean` file attempts to combine all three bridges into one monolithic `IsBounded` structure. The API mismatches are:

1. **`incomingIIterate` on iterated stages**: The `IsBounded.Dlb` field expects `C.incomingIIterate (n := s + 1) p` where `C : GradedExactCouple`. But on iterated stages, the `iDeg` map changes at each derivation (`derivedIDegree`), so the composite `i`-iterates don't align with the original filtration.

2. **`ModuleCat` coercion boundaries**: `Stage` uses `ModuleCat.{u} R`; `page` coerces to `Type u`. The `IsBounded.Elb_iterate` expects `E ((iDeg.symm^[s]) p)` but `iDeg` on derived stages is `derivedIDegree`, not the original `iDeg`.

3. **`pageIncoming`/`pageOutgoing` fields**: These reference `(iteratedStage S n).couple.differentialDegree` but the `IsBounded` structure is on the *initial* exact couple, not the iterated ones.

4. **Zero-module instances**: The `Dub`/`Elb` fields use `∀ x : D ..., x = 0` which requires `Subsingleton (D ...)` instances that aren't automatically synthesized for dependent families.

**Recommendation**: Do not repair. Decompose into the three bridges above.