import InfoGeometry.Canonical.InductiveOperatorTaylorClosure
import InfoGeometry.Convex.RadialLogBarrier

/-!
# InfoGeometry.Convex.InductiveBarrierOptimization

Inductive convex-optimization closure for finite barrier iterations.

This file makes precise the safe common architecture between
finite operator-Taylor prefixes and iterative self-concordant/barrier methods:

* an update map is iterated by `Nat.iterate`;
* feasibility is propagated by a step-preservation theorem;
* barrier/energy descent is propagated by induction;
* linear operator-Taylor prefixes can be used as finite update maps, and their
  no-leakage theorem gives invariant-sector feasibility for every finite
  iterate.

The results are intentionally finite and inductive.  They do not assert that a
finite Taylor prefix converges to an analytic operator function, nor that a
barrier iteration converges to an optimizer.
-/

namespace InfoGeometry.Convex.InductiveBarrierOptimization

open InfoGeometry.Canonical.SymmetryClosureConformalBlocks
open InductiveOperatorTaylorClosure

/-! ## Generic finite barrier iterations -/

/-- The `N`th finite iterate of an update map, with successor applying after the prefix. -/
def iterateUpdate {X : Type*} (step : X → X) : ℕ → X → X
  | 0, x => x
  | N + 1, x => step (iterateUpdate step N x)

@[simp]
theorem iterateUpdate_zero {X : Type*} (step : X → X) (x : X) :
    iterateUpdate step 0 x = x := by
  rfl

@[simp]
theorem iterateUpdate_succ {X : Type*} (step : X → X) (N : ℕ) (x : X) :
    iterateUpdate step (N + 1) x = step (iterateUpdate step N x) := by
  rfl

/-- Feasibility is preserved by every finite iterate of a feasible update. -/
theorem feasible_iterateUpdate {X : Type*} {feasible : X → Prop} {step : X → X}
    (hstep : ∀ x, feasible x → feasible (step x))
    {x : X} (hx : feasible x) (N : ℕ) :
    feasible (iterateUpdate step N x) := by
  induction N with
  | zero => simpa using hx
  | succ N ih =>
      simpa [iterateUpdate] using hstep (iterateUpdate step N x) ih

/-- One-step barrier descent propagates to descent from every finite iterate to the start. -/
theorem barrierValue_iterateUpdate_le_start {X : Type*}
    {feasible : X → Prop} {barrier : X → ℝ} {step : X → X}
    (hfeas : ∀ x, feasible x → feasible (step x))
    (hdesc : ∀ x, feasible x → barrier (step x) ≤ barrier x)
    {x : X} (hx : feasible x) (N : ℕ) :
    barrier (iterateUpdate step N x) ≤ barrier x := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hN : feasible (iterateUpdate step N x) := feasible_iterateUpdate hfeas hx N
      exact le_trans (hdesc (iterateUpdate step N x) hN) ih

/-- Consecutive finite iterates are barrier-monotone under the one-step descent property. -/
theorem barrierValue_iterateUpdate_succ_le {X : Type*}
    {feasible : X → Prop} {barrier : X → ℝ} {step : X → X}
    (hfeas : ∀ x, feasible x → feasible (step x))
    (hdesc : ∀ x, feasible x → barrier (step x) ≤ barrier x)
    {x : X} (hx : feasible x) (N : ℕ) :
    barrier (iterateUpdate step (N + 1) x) ≤ barrier (iterateUpdate step N x) := by
  have hN : feasible (iterateUpdate step N x) := feasible_iterateUpdate hfeas hx N
  simpa [iterateUpdate] using hdesc (iterateUpdate step N x) hN

/-! ## Finite Taylor-prefix updates as invariant-preserving iterations -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A finite operator-Taylor prefix used as a discrete update map. -/
noncomputable def taylorUpdate (c : ℕ → ℂ) (N : ℕ) (A : V →ₗ[ℂ] V) : V → V :=
  operatorTaylorPrefix c N A

/-- If the generator preserves sectors, then the finite Taylor update preserves feasibility. -/
theorem taylorUpdate_preserves_computational
    {D : SectorDecomposition V} {A : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (c : ℕ → ℂ) (N : ℕ) :
    ∀ v : V, v ∈ D.computational → taylorUpdate c N A v ∈ D.computational := by
  intro v hv
  exact (SectorDecomposition.noLeakage_operatorTaylorPrefix hA c N) v hv

/-- Every finite iterate of a finite Taylor-prefix update stays in the computational sector. -/
theorem taylorUpdate_iterate_preserves_computational
    {D : SectorDecomposition V} {A : V →ₗ[ℂ] V}
    (hA : D.PreservesSectors A) (c : ℕ → ℂ) (prefixSteps iterSteps : ℕ)
    {v : V} (hv : v ∈ D.computational) :
    iterateUpdate (taylorUpdate c prefixSteps A) iterSteps v ∈ D.computational :=
  feasible_iterateUpdate (taylorUpdate_preserves_computational hA c prefixSteps) hv iterSteps

/-! ## Radial barrier iteration: a concrete one-dimensional safe instance -/

/-- The open radial domain for the radial log barrier. -/
def RadialInterior (s : ℝ) : Prop :=
  0 ≤ s ∧ s < 1

/-- A radial update is admissible when it stays in the open radial domain. -/
def RadialUpdateAdmissible (step : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, RadialInterior s → RadialInterior (step s)

/-- A radial update is barrier-descending for the finite radial barrier. -/
def RadialBarrierDescending (step : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, RadialInterior s →
    RadialLogBarrier.radialBarrier (step s) ≤ RadialLogBarrier.radialBarrier s

/-- Admissible radial updates preserve the radial domain for every finite iterate. -/
theorem radialInterior_iterateUpdate
    {step : ℝ → ℝ} (hadm : RadialUpdateAdmissible step)
    {s : ℝ} (hs : RadialInterior s) (N : ℕ) :
    RadialInterior (iterateUpdate step N s) :=
  feasible_iterateUpdate hadm hs N

/-- Barrier-descending radial updates are monotone along every finite iterate. -/
theorem radialBarrier_iterateUpdate_le_start
    {step : ℝ → ℝ} (hadm : RadialUpdateAdmissible step)
    (hdesc : RadialBarrierDescending step)
    {s : ℝ} (hs : RadialInterior s) (N : ℕ) :
    RadialLogBarrier.radialBarrier (iterateUpdate step N s) ≤
      RadialLogBarrier.radialBarrier s :=
  barrierValue_iterateUpdate_le_start hadm hdesc hs N

end InfoGeometry.Convex.InductiveBarrierOptimization
