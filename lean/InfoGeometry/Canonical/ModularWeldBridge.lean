import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Volume.ConnesCocycle
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

open scoped BigOperators

/-!
# InfoGeometry.Canonical.ModularWeldBridge

Thin L2→L3 diagnostic bridge:

- Finite diagonal branch is an explicit **shadow/diagnostic** lane.
- It provides finite projective normal-form readouts; it is not the owner
  primitive of the modular theory.
- Finite diagnostic chart: relative modular operator `Δ(q,q₀)` as a diagonal
  operator over projective positive rays (readout mode).
- L3 readout: exponential modular lane.

The core compatibility is:

`Δ(q,q₀) = exp(log-density lift(q,q₀))`.

This file exports a Tomita flow cocycle surface so Connes-Araki consumers have
diagnostic access, while preserving the diagonal lane as a projection channel.

Ownership policy:
finite diagonal statements in this file are intentionally **diagnostic shadows**:
they summarize diagonal-frame data after gauge choice, and are never the semantic
owner of the noncommutative Connes-Araki modular flow.

The finite diagonal interface is therefore pinned as a projection/diagnostic
contract and must not be treated as a primitive owner evidence in downstream
operator-lane composition.
-/

namespace InfoGeometry.Canonical.ModularWeldBridge

open InfoGeometry.Canonical.PositiveRayCore
open RelativeModularOperator
open TomitaTakesaki
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal
open InfoGeometry.Volume.ConnesCocycle

section FiniteWeld

variable {n : ℕ} [Nonempty (Fin n)]

/--
Finite diagnostic lift of the relative log-density lane.

This lane exposes diagonal coordinates after a finite gauge choice; it is
explicitly the **shadow/diagnostic** readout channel, not a primitive operator
object in the noncommutative modular architecture.
-/
noncomputable def relativeLogDensityOperator
    (q q0 : PositiveRay (Fin n)) : FinMat n :=
  diagMatrix (fun i =>
    RelativePotentialCore.relativeLogDensity (α := Fin n) q q0 i)

/-!
L2→L3 weld on the finite diagnostic lane:
the canonical finite relative modular operator is exactly the matrix exponential of
the lifted relative log-density operator.
-/
@[rep_depth operator]
theorem relativeModularOperator_eq_exp_relativeLogDensityOperator
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [relativeModularOperator_diag_eq_exp_relativeLogDensity]
    rw [Real.exp_eq_exp_ℝ]
    unfold relativeLogDensityOperator diagMatrix
    rw [Matrix.exp_diagonal]
    simp only [Matrix.diagonal_apply_eq]
    exact
      (Pi.coe_exp
        (x := fun j : Fin n => RelativePotentialCore.relativeLogDensity q q0 j)
        i).symm
  · rw [relativeModularOperator_offdiag (hij := hij)]
    unfold relativeLogDensityOperator diagMatrix
    rw [Matrix.exp_diagonal]
    simp only [Matrix.diagonal_apply_ne _ hij]

/-- Shadow/diagnostic alias for the finite diagonal weld identity. -/
theorem finiteDiagonalShadow_relativeModularOperator_eq_exp_relativeLogDensity
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  simpa using (relativeModularOperator_eq_exp_relativeLogDensityOperator
    (n := n) q q0)

/-- Owner-safe marker for the finite diagonal regression lane. -/
theorem FiniteDiagonalModularWeldBridge
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  simpa using (finiteDiagonalShadow_relativeModularOperator_eq_exp_relativeLogDensity
    (n := n) q q0)

/-! The finite object above is a readout/diagnostic shadow and does not serve
as the noncommutative modular operator owner lane. -/
theorem finiteDiagonalModularWeldBridge_shadow_only
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  simpa using FiniteDiagonalModularWeldBridge (n := n) q q0

/-- Thin ownership-safe alias reinforcing shadow status in downstream lanes. -/
theorem finiteDiagonalShadowLane
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  simpa using finiteDiagonalModularWeldBridge_shadow_only (n := n) q q0

/-- Diagnostic-only re-export of the finite diagonal shadow law. -/
theorem finiteDiagonalShadowLane_marker
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  simpa using finiteDiagonalShadowLane (n := n) q q0

/-- Final projection marker for the finite diagonal lane:
it is a readout/diagnostic channel and must not be re-used as
noncommutative owner evidence. -/
theorem finiteDiagonalShadowLane_projection_only
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  simpa using finiteDiagonalShadowLane_marker (n := n) q q0

/-- Explicit ownership boundary marker for downstream consumers. -/
theorem finiteDiagonalShadowLane_only_projection
    (q q0 : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q0 =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q0) := by
  simpa using finiteDiagonalShadowLane_projection_only (n := n) q q0

/-- Diagonal lift of the relative log-density is zero on the unit (self) lane. -/
@[simp, rep_depth operator]
theorem relativeLogDensityOperator_self
    (q : PositiveRay (Fin n)) :
    relativeLogDensityOperator (n := n) q q = 0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [relativeLogDensityOperator, diagMatrix, Matrix.diagonal_apply_eq]
    exact
      (RelativePotentialCore.relativeLogDensity_self
        (α := Fin n) (q := q) (a := i))
  · rw [Pi.zero_apply]
    rw [relativeLogDensityOperator, diagMatrix, Matrix.diagonal_apply_ne]
    · rfl
    · simp [hij]

/-- Operator lift of the additive relative log-density cocycle. -/
@[rep_depth operator]
theorem relativeLogDensityOperator_cocycle
    (q q0 q1 : PositiveRay (Fin n)) :
    relativeLogDensityOperator (n := n) q q1 =
      relativeLogDensityOperator (n := n) q q0
        + relativeLogDensityOperator (n := n) q0 q1 := by
  unfold relativeLogDensityOperator diagMatrix
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq]
    exact
      RelativePotentialCore.relativeLogDensity_cocycle
        (q := q) (q0 := q0) (q1 := q1) (a := i)
  · rw [Matrix.add_apply]
    simp only [Matrix.diagonal_apply_ne _ hij]
    ring

/-- Weld self-specialization: `Δ(q|q) = exp(0) = 1`. -/
@[rep_depth operator]
theorem relativeModularOperator_eq_exp_relativeLogDensityOperator_self
    (q : PositiveRay (Fin n)) :
    relativeModularOperator (n := n) q q =
      NormedSpace.exp (relativeLogDensityOperator (n := n) q q) := by
  simp [relativeLogDensityOperator_self]

/-- Exponential of the self-relative logarithmic operator is the identity. -/
@[simp, rep_depth operator]
theorem exp_relativeLogDensityOperator_self
    (q : PositiveRay (Fin n)) :
    NormedSpace.exp (relativeLogDensityOperator (n := n) q q) =
      (1 : FinMat n) := by
  rw [relativeLogDensityOperator_self]
  simp

/--
Shadow-level diagnostic naming: self-relative finite diagonal log-density exponentials
normalize to unit as a diagonal readout check.
-/
theorem finiteDiagonalShadow_exp_self_is_one
    (q : PositiveRay (Fin n)) :
    NormedSpace.exp (relativeLogDensityOperator (n := n) q q) = 1 := by
  simp

end FiniteWeld

section MatrixDetExpTrace

variable {n : ℕ}

/--
Diagonal trace-determinant law for the matrix exponential.

This is the repo-native shadow of the full `det (exp A) = exp (trace A)` theorem:
it is proved by the same diagonal reduction algorithm used elsewhere in the
finite modular lane.
-/
@[rep_depth operator]
theorem det_exp_diagonal_eq_exp_trace
    (v : Fin n → ℝ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      NormedSpace.exp (Matrix.trace (Matrix.diagonal v)) := by
  rw [Matrix.exp_diagonal, Matrix.det_diagonal, Matrix.trace_diagonal]
  simpa [Real.exp_eq_exp_ℝ] using (Real.exp_sum (s := Finset.univ) (f := v)).symm

end MatrixDetExpTrace

section TomitaFlow

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! Tomita flow lemmas here remain on the surface/diagnostic layer for
Connes-Araki consumers. The noncommutative owner witness remains external. -/

/--
Tomita flow carries a canonical derived cocycle by evaluating the flow on
the unit.
-/
@[rep_depth operator]
theorem tomita_modularSign_flowUnitCocycle_isConnesCocycle :
    IsConnesCocycle
      (modularSignAdditiveModularFlow (E := H))
      (flowUnitCocycle
        (H := H)
        (modularSignAdditiveModularFlow (E := H))) := by
  simpa using
    (flowUnitCocycle_isConnesCocycle
      (H := H)
      (modularSignAdditiveModularFlow (E := H)))

/-- Tomita modular-sign flow fixes the operator unit. -/
@[simp, rep_depth operator]
theorem tomita_modularSign_flow_one
    (t : ℝ) :
    modularSignAdditiveModularFlow (E := H) t
      (1 : AlgebraEnd H)
      =
    (1 : AlgebraEnd H) := by
  simpa [InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle]
    using
      (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_eq_one
        (H := H) (σ := modularSignAdditiveModularFlow (E := H)) t)

/-- Tomita modular-sign flow-unit cocycle is a Connes-cocycle equation at each `(s,t)`. -/
@[rep_depth operator]
theorem tomita_modularSign_flowUnitCocycle_cocycle
    (s t : ℝ) :
    flowUnitCocycle (H := H)
      (modularSignAdditiveModularFlow (E := H)) (s + t)
      =
    flowUnitCocycle (H := H)
      (modularSignAdditiveModularFlow (E := H)) s *
    modularSignAdditiveModularFlow (E := H)
      s (flowUnitCocycle (H := H)
        (modularSignAdditiveModularFlow (E := H)) t) := by
  exact InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_cocycle
    (H := H) (σ := modularSignAdditiveModularFlow (E := H)) s t
    -- note: use generic Connes-cocycle decomposition from Volume.ConnesCocycle

@[simp, rep_depth operator] theorem tomita_modularSign_flowUnitCocycle_zero :
    flowUnitCocycle (H := H)
      (modularSignAdditiveModularFlow (E := H)) 0 = 1 := by
  simp

@[simp, rep_depth operator] theorem tomita_modularSign_flowUnitCocycle_one
    (t : ℝ) :
    flowUnitCocycle (H := H) (modularSignAdditiveModularFlow (E := H)) t = 1 := by
  simpa using (InfoGeometry.Volume.ConnesCocycle.flowUnitCocycle_eq_one
    (H := H) (σ := modularSignAdditiveModularFlow (E := H)) t)

end TomitaFlow

end InfoGeometry.Canonical.ModularWeldBridge
