# Spectral → Lean 4 Port Plan

**Source**: `external_refs/Spectral` (Lean 2 HoTT, 73 `.hlean` files)  
**Target**: `lean/InfoGeometry/Spectral/` (Lean 4.28.0, mathlib4-native)  
**Policy**: Clean reimplementation using mathlib4 primitives; no mechanical translation.

---

## Dependency DAG (from Spectral imports)

```
logic.hlean, property.hlean, choice.hlean, heq.hlean
         ↓
move_to_lib.hlean, types/pointed2.hlean, types/sigma.lean, types/sum.lean, types/list.lean, types/trunc.lean
         ↓
homotopy/*.hlean (susp, pushout, wedge, smash, join, EM, EMRing, degree, ...)
         ↓
colimit/*.hlean (seq_colim, pushout, omega_compact, ...)
         ↓
spectrum/basic.hlean (prespectrum, spectrum, maps, spectrification)
         ↓
algebra/*.hlean (group_theory, subgroup, quotient_group, product_group, direct_sum,
                 free_abelian_group, free_group, ring, graded, module_chain_complex,
                 exact_couple, spectral_sequence, splice, short_five, ses, ...)
         ↓
cohomology/basic.hlean, serre.hlean, gysin.hlean, projective_space.hlean
homology/basic.hlean, sphere.hlean, torus.hlean
```

---

## Port Waves

### Wave 0: Infrastructure (this repo)
- [x] Lean 4.28.0 toolchain pinned
- [x] mathlib4 at v4.28.0 via `lakefile.lean`
- [x] `InfoGeometryCore` local dependency
- [ ] Add `Spectral` Lean 4 target directory: `lean/InfoGeometry/Spectral/`

### Wave 1: Algebraic Core — Exact Couples & Spectral Sequences
**Source**: `algebra/exact_couple.hlean` + `algebra/spectral_sequence.hlean` (~380 lines combined)  
**Target**: `lean/InfoGeometry/Spectral/Algebra/ExactCouple.lean`, `SpectralSequence.lean`  
**mathlib4 dependencies**: `Mathlib.CategoryTheory`, `Mathlib.HomologicalAlgebra`, `Mathlib.Algebra.Module.Graded`  
**Why first**: Pure algebra, no homotopy/spectrum infrastructure needed. Mathematical heart of the project.

**Key structures to port**:
- `ExactCouple` (objects `D, E : ℤ × ℤ → Module R`, maps `i, j, k`)
- `DerivedCouple` construction
- `ConvergentExactCouple` (boundedness, `B3` condition)
- `SpectralSequence` from exact couple (`E r`, differentials `d r`, `α r` isos)
- `ConvergentSpectralSequence` (`E∞`, `s₀`, `f`, `lb`, `HDinf`)
- Normal spectral sequences (first quadrant, `deg d r = (r+2, -(r+1))`)
- Convergence theorems (`E_isomorphism`, `Einf_isomorphism`, `convergence_0`, `stable_range`)

**Deliverable**: Compiling Lean 4 module + Sage/Singular/SymPy scripts that compute the same `E r` pages for a concrete exact couple (e.g. the `ℤ`-graded couple from a filtered complex).

### Wave 2: Spectrum & Prespectrum Foundations
**Source**: `spectrum/basic.hlean`, `spectrum/smash.hlean`, `spectrum/spectrification.hlean`, `spectrum/trunc.hlean`  
**Target**: `lean/InfoGeometry/Spectral/Spectrum/Basic.lean`, `Smash.lean`, `Spectrification.lean`  
**mathlib4 dependencies**: `Mathlib.Topology.Homotopy`, `Mathlib.AlgebraicTopology.SimplicialObject`, `Mathlib.CategoryTheory.Triangulated.SpectralObject`  
**Key structures**: `GenPrespectrum`, `IsSpectrum`, `SMap`, `spectrification` as sequential colimit, `ℤ`-indexed reduction from `ℕ`-indexed.

### Wave 3: Homotopy Operations Used by Spectral Sequences
**Source**: `homotopy/susp.hlean`, `homotopy/smash.hlean`, `homotopy/wedge.hlean`, `homotopy/fwedge.hlean`, `homotopy/join_theorem.hlean`, `homotopy/EM.hlean`, `homotopy/EMRing.hlean`, `homotopy/pushout.hlean`  
**Target**: `lean/InfoGeometry/Spectral/Homotopy/`  
**mathlib4 dependencies**: `Mathlib.Topology.Homotopy.HomotopyGroup`, `Mathlib.AlgebraicTopology.SimplicialSet`, `Mathlib.CategoryTheory.Limits.Pushout`  
**Note**: Use mathlib4's native `Suspension`, `SmashProduct`, `Wedge`, `EilenbergMacLaneSpace` where available; only fill gaps.

### Wave 4: Colimit Infrastructure
**Source**: `colimit/seq_colim.hlean`, `colimit/pushout.hlean`, `colimit/omega_compact.hlean`, `colimit/pointed.hlean`  
**Target**: `lean/InfoGeometry/Spectral/Colimit/`  
**mathlib4**: `Mathlib.CategoryTheory.Limits.Colimit`, `Mathlib.CategoryTheory.Limits.SequentialColimit`

### Wave 5: Homology / Cohomology / Serre Spectral Sequence
**Source**: `homology/basic.hlean`, `cohomology/basic.hlean`, `cohomology/cofiber_sequence.hlean`, `cohomology/serre.hlean`, `cohomology/gysin.hlean`, `cohomology/projective_space.hlean`  
**Target**: `lean/InfoGeometry/Spectral/Homology/`, `Cohomology/`  
**mathlib4**: `Mathlib.AlgebraicTopology.SingularHomology`, `Mathlib.AlgebraicTopology.SimplicialSet`, `Mathlib.Topology.Homotopy.HomotopyGroup`

### Wave 6: Higher Groups & Real Projective Spaces
**Source**: `higher_groups.hlean`, `homotopy/realprojective.hlean`, `cohomology/projective_space.hlean`  
**Target**: `lean/InfoGeometry/Spectral/HigherGroups.lean`, `RealProjective.lean`

---

## First Slice (Wave 1) — Concrete Deliverables

| File | Lines | Description |
|------|-------|-------------|
| `lean/InfoGeometry/Spectral/Algebra/ExactCouple.lean` | ~200 | `ExactCouple`, `DerivedCouple`, `ConvergentExactCouple` |
| `lean/InfoGeometry/Spectral/Algebra/SpectralSequence.lean` | ~220 | `SpectralSequence`, `ConvergentSpectralSequence`, normal SS, convergence lemmas |
| `tools/sympy/spectral_exact_couple.py` | ~120 | Symbolic `E r`, `d r` computation for a test exact couple |
| `tools/sage/spectral_exact_couple.sage` | ~120 | Same in Sage |
| `tools/singular/spectral_exact_couple.sing` | ~80 | Same in Singular |
| `tools/gap/spectral_exact_couple.g` | ~80 | Same in GAP |

**Verification**: `lake build InfoGeometry.Spectral.Algebra.ExactCouple InfoGeometry.Spectral.Algebra.SpectralSequence` + all 4 CAS scripts emit identical `E₁, E₂, E₃` pages for the test couple.

---

## Naming Conventions

- Source namespace: `Spectral.*` (Lean 2)  
- Target namespace: `InfoGeometry.Spectral.*` (Lean 4)  
- Each file `X.hlean` → `X.lean` in matching subdirectory  
- Use mathlib4 names where they exist (`Module`, `GradedModule`, `ChainComplex`, `Homology`, `HomotopyGroup`, `Suspension`, `SmashProduct`, `Wedge`, `EilenbergMacLaneSpace`, `SpectralObject`)

---

## Non-Goals for This Port

- HoTT-specific constructs (`is_equiv`, `is_contr`, `ptrunc`, `heq`, univalence) — mathlib4 uses classical homotopy theory
- Universe polymorphism tricks from Lean 2 — Lean 4 handles universes differently
- `hlean` syntax — write idiomatic Lean 4

---

## Next Action

Implement Wave 1 (ExactCouple + SpectralSequence) with cross-language verification.
