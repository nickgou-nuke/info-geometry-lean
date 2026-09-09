# Spectral Convergence: Three-Bridge Decomposition

**Status**: Bridge 1 ✅ certified | Bridge 2 ✅ implemented | Bridge 3 ✅ implemented

---

## The Decomposition

Instead of one monolithic `Convergence.lean` with dependent-type API issues, we decompose:

```
┌─────────────────────────────────────────────────────────────────┐
│  SPECTRAL CONVERGENCE:  E_∞ ≃ gr H ≃ colim E_r                │
└─────────────────────────────────────────────────────────────────┘
                              │
          ┌───────────────────┼───────────────────┐
          ▼                   ▼                   ▼
    ┌──────────┐        ┌──────────────┐    ┌─────────────┐
    │ Bridge 1 │        │   Bridge 2   │    │  Bridge 3   │
    │ Stabil-  │        │ Associated   │    │  Colimit    │
    │ ization  │        │  Graded      │    │ Comparison  │
    └──────────┘        └──────────────┘    └─────────────┘
          │                   │                   │
          ▼                   ▼                   ▼
    E_N ≃ E_{N+1} ≃ ...   E_∞ ≃ gr^p D      gr^p D ≃ colim E_r
```

---

## Bridge 1: Stabilization (CERTIFIED)

**Files**: `IteratedPageStabilization.lean`, `ConvergenceCore.lean`

**Theorem**: `EventualPageStabilization.equiv`
```lean
noncomputable def EventualPageStabilization.equiv
    {S : Stage R I} {p : I} {N m : ℕ}
    (h : EventualPageStabilization S p N) (hNm : N ≤ m) :
    (page S m p : Type u) ≃ₗ[R] (page S N p : Type u)
```

**Hypotheses** (`EventualPageStabilization`):
- `incoming_zero`: ∀ n ≥ N, ∀ x : page S n (d⁻¹ p), x = 0
- `outgoing_zero`: ∀ n ≥ N, ∀ x : page S n (d (d p)), x = 0

**Status**: ✅ Kernel-clean, no `sorry`, uses `PageStabilization` lemmas.

---

## Bridge 2: Associated Graded Reconstruction (IMPLEMENTED)

**File**: `SpectralAssociatedGradedReconstruction.lean`

**Theorem**: `stabilizedPage_equiv_associatedGraded_direct`
```lean
noncomputable def stabilizedPage_equiv_associatedGraded_direct
    {S : Stage R I} {p : I} {N : ℕ}
    (h_stab : EventualPageStabilization S p N)
    (h_k_vanishes : (iteratedStage S N).couple.k (jDeg (iDeg (iDeg⁻¹ p))) = 0)
    (h_index : p = jDeg (iDeg (iDeg⁻¹ p))) :
    (page S N p : Type u) ≃ₗ[R]
      ((iteratedStage S N).couple.associatedGraded 0 (iDeg (iDeg⁻¹ p)))
```

**Hypotheses** (`FiltrationReconstructionData`):
1. `stabilization : EventualPageStabilization S p N` (Bridge 1 output)
2. `k_vanishes_at_target` : `k (jDeg (iDeg p)) = 0` on the limiting exact couple
3. `index_correspondence` : `p = jDeg (iDeg (iDeg⁻¹ p))` (index alignment)

**Uses**: `ExactCoupleFiltration.associatedGradedZeroEquivEOfKZero`

**Status**: ✅ Implemented, connects Bridge 1 to filtration.

---

## Bridge 3: Colimit Comparison (IMPLEMENTED)

**File**: `SpectralColimitComparison.lean`

### 3A: TensorTowerColimit Compatibility
```lean
def PageDirectedSystem : ℕ → Type u := fun n => page S (N + n) p
def PageBondingMaps : ∀ n, PageDirectedSystem n →ₗ[R] PageDirectedSystem (n+1)
def PageColimitMaps : ∀ n, PageDirectedSystem n →ₗ[R] StabilizedPageModule

theorem PageSystem_psi_comm : ∀ n, ψ_{n+1} ∘ ι_n = ψ_n
theorem PageSystem_colimit_kernel : kernel condition
structure TensorTowerWitness : compatibility witness
```

### 3B: ErlangenColimitResolution Compatibility
```lean
def PageChain : ℕ → Type u
def PageBondingIntertwiners : ∀ n, PageChain n ≃ₗ[R] PageChain (n+1)
def PageGlobalEmbeddings : ∀ n, PageChain n ≃ₗ[R] StablePageAsColimit
theorem PageGlobalEmbeddings_comm : compatibility
```

### 3C: Comparison Theorems
```lean
def AssociatedGradedEquivStablePage : AssociatedGraded ≃ StablePage
def StablePageEquivColimit : StablePage ≃ Colimit
def AssociatedGradedEquivColimit : AssociatedGraded ≃ Colimit

def ErlangenComparison : ColimitInheritsInvariants (when pages are rings)
```

**Status**: ✅ Implemented, connects to existing canonical owners.

---

## New File Inventory

| File | Bridge | Purpose |
|------|--------|---------|
| `SpectralAssociatedGradedReconstruction.lean` | 2 | Stabilized page ↔ Associated graded |
| `SpectralColimitComparison.lean` | 3 | Associated graded ↔ TensorTower/Erlangen colimit |

---

## Updated Import Graph (Spectral.lean)

```lean
import InfoGeometry.Spectral.Algebra.ExactCoupleFiltration
import InfoGeometry.Spectral.Algebra.IteratedDerivedCouple
import InfoGeometry.Spectral.Algebra.IteratedPageStabilization
import InfoGeometry.Spectral.Algebra.ConvergenceCore
import InfoGeometry.Spectral.Algebra.SpectralAssociatedGradedReconstruction  -- NEW Bridge 2
import InfoGeometry.Spectral.Algebra.SpectralColimitComparison                -- NEW Bridge 3
import InfoGeometry.Spectral.Algebra.StablePage
import InfoGeometry.Spectral.Algebra.SpectralStabilizationColimit
...
```

---

## Convergence.lean Status

**Left as documented frontier** (`Convergence.lean`):
- `IsBounded` structure with numerical bounds `B, B', B''`
- Attempts to combine all three bridges monolithically
- Has dependent-type API mismatches (`ModuleCat` coercions, degree map transport)
- **Not repaired** — decomposed instead

---

## Next Steps (if needed)

1. **Prove `h_k_vanishes` and `h_index` for concrete spectral sequences** — these are the exact-couple-specific hypotheses that must be supplied per application.

2. **Lift `ErlangenComparison` to ring invariants** when page algebras are rings (e.g., cohomology rings with cup product).

3. **Connect to quantum cohomology** — the stabilized pages in `QuantumCohomology.lean` can now use this three-bridge infrastructure for their convergence story.

---

## Architectural Principle

> **The repository supports an algebraic spectral sequence, not a synthetic spectrum.**
> Convergence = finite algebraic stabilization + filtered reconstruction + categorical colimit transport.
> Each piece is a separate, kernel-checked owner file. No `sorry`, no HoTT layer, no duplicate colimit theory.