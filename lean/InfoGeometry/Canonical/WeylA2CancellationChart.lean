import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.WeylTwoNodeCancellationChart

/-!
# InfoGeometry.Canonical.WeylA2CancellationChart

Concrete finite `A₂` / `SU(3)`-like cancellation chart.

The chart is still deliberately finite:

* denominator: the 3-node Vandermonde determinant on scalar nodes;
* numerator: the 3-node Vandermonde determinant on the exponential nodes;
* collision theorem: if the denominator vanishes, then the numerator vanishes.

This stays below the threshold of a full Weyl-character theorem while giving a
genuine three-node cancellation witness.
-/

namespace InfoGeometry.Canonical.WeylA2CancellationChart

open InfoGeometry.Canonical.VandermondeExclusionBridge

open scoped Matrix

/-- Three-node scalar chart. -/
@[rep_depth thermo]
structure A2Chart where
  x : ℝ
  y : ℝ
  z : ℝ

namespace A2Chart

variable (C : A2Chart)

/-- The three scalar denominator nodes. -/
@[rep_depth thermo]
def nodes : Fin 3 → ℝ
  | 0 => C.x
  | 1 => C.y
  | 2 => C.z

/-- The exponential numerator nodes. -/
@[rep_depth thermo]
noncomputable def expNodes : Fin 3 → ℝ :=
  fun i => Real.exp (C.nodes i)

/-- Finite Vandermonde witness for the denominator lane. -/
@[rep_depth thermo]
def denominatorWitness : Fin 3 → ℝ :=
  C.nodes

/-- Denominator value. -/
@[rep_depth thermo]
def denominator : ℝ :=
  FiniteVandermondeExclusionWitness.determinant C.denominatorWitness

/-- Numerator value: Vandermonde determinant of the exponential nodes. -/
@[rep_depth thermo]
noncomputable def numerator : ℝ :=
  Matrix.det (Matrix.vandermonde C.expNodes)

/-- Noncollision domain for the denominator nodes. -/
@[rep_depth thermo]
def NoncollisionDomain : Prop :=
  C.denominator ≠ 0

/-- Local quotient on the noncollision domain. -/
@[rep_depth thermo]
noncomputable def quotient (_h : C.NoncollisionDomain) : ℝ :=
  C.numerator / C.denominator

/-- Denominator zero is exactly collision of two scalar nodes. -/
@[rep_depth thermo]
theorem denominator_eq_zero_iff_collision :
    C.denominator = 0 ↔
      ∃ i j : Fin 3, C.nodes i = C.nodes j ∧ i ≠ j :=
  FiniteVandermondeExclusionWitness.determinant_eq_zero_iff_collision
    C.denominatorWitness

/-- Numerator zero is exactly collision of two exponential nodes. -/
@[rep_depth thermo]
theorem numerator_eq_zero_iff_expCollision :
    C.numerator = 0 ↔
      ∃ i j : Fin 3, C.expNodes i = C.expNodes j ∧ i ≠ j := by
  unfold numerator
  simpa using (Matrix.det_vandermonde_eq_zero_iff (v := C.expNodes))

/--
Concrete `A₂` cancellation theorem:
collision of scalar nodes forces collision of exponential nodes, hence the
exponential Vandermonde numerator vanishes whenever the scalar Vandermonde
denominator vanishes.
-/
@[rep_depth thermo]
theorem denominator_zero_forces_numerator_zero
    (hden : C.denominator = 0) :
    C.numerator = 0 := by
  rcases (C.denominator_eq_zero_iff_collision.mp hden) with ⟨i, j, hij, hne⟩
  apply (C.numerator_eq_zero_iff_expCollision).2
  refine ⟨i, j, ?_, hne⟩
  change Real.exp (C.nodes i) = Real.exp (C.nodes j)
  exact congrArg Real.exp hij

/-- The quotient unfolds to the ordinary ratio on the noncollision domain. -/
@[rep_depth thermo]
theorem quotient_eq_ratio (h : C.NoncollisionDomain) :
    C.quotient h = C.numerator / C.denominator := rfl

end A2Chart

end InfoGeometry.Canonical.WeylA2CancellationChart
