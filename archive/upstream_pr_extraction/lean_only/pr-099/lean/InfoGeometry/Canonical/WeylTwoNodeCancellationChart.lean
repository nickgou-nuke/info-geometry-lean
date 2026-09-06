import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.WeylLocalCancellationShadow

/-!
# InfoGeometry.Canonical.WeylTwoNodeCancellationChart

Concrete two-node cancellation chart for the finite Weyl/Vandermonde corridor.

This is the first non-hypothetical cancellation property in the current repo:

* denominator: the 2x2 Vandermonde factor `y - x`,
* numerator: the alternating Gibbs difference `exp x - exp y`,
* collision locus: `x = y`,
* local quotient: defined only on the noncollision domain.

This file does not pretend to be a full Weyl-character theorem.  It is a
concrete finite chart where the numerator-zero-on-collision property is proved,
not assumed.
-/

namespace InfoGeometry.Canonical.WeylTwoNodeCancellationChart

open InfoGeometry.Canonical.WeylAlternatingNumeratorShadow
open InfoGeometry.Canonical.VandermondeExclusionBridge

open scoped BigOperators Matrix

/-- Two-node scalar chart. -/
@[rep_depth thermo]
structure TwoNodeChart where
  x : ℝ
  y : ℝ

namespace TwoNodeChart

variable (C : TwoNodeChart)

/-- The two denominator nodes. -/
@[rep_depth thermo]
def nodes : Fin 2 → ℝ
  | 0 => C.x
  | 1 => C.y

/-- The denominator determinant is the 2x2 Vandermonde determinant. -/
@[rep_depth thermo]
def denominator : ℝ :=
  FiniteVandermondeExclusionWitness.determinant C.nodes

/-- The concrete alternating Gibbs numerator `exp x - exp y`. -/
@[rep_depth thermo]
noncomputable def numerator : ℝ :=
  Real.exp C.x - Real.exp C.y

/-- The noncollision domain for the two-node chart. -/
@[rep_depth thermo]
def NoncollisionDomain : Prop :=
  C.denominator ≠ 0

/-- The local quotient on the noncollision domain. -/
@[rep_depth thermo]
noncomputable def quotient (_h : C.NoncollisionDomain) : ℝ :=
  C.numerator / C.denominator

/-- The denominator unfolds to the expected 2x2 determinant. -/
@[rep_depth thermo]
theorem denominator_eq :
    C.denominator = C.y - C.x := by
  unfold denominator
  simp [FiniteVandermondeExclusionWitness.determinant,
    FiniteVandermondeExclusionWitness.matrix, nodes, Matrix.det_fin_two]

/-- Collision is exactly equality of the two scalar nodes. -/
@[rep_depth thermo]
theorem denominator_eq_zero_iff :
    C.denominator = 0 ↔ C.x = C.y := by
  rw [C.denominator_eq]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- On the collision locus, the alternating numerator vanishes. -/
@[rep_depth thermo]
theorem numerator_eq_zero_of_collision (hxy : C.x = C.y) :
    C.numerator = 0 := by
  unfold numerator
  rw [hxy, sub_self]

/--
Concrete cancellation theorem for the two-node chart:
if the Vandermonde denominator vanishes, then the alternating numerator vanishes.
-/
@[rep_depth thermo]
theorem denominator_zero_forces_numerator_zero
    (hden : C.denominator = 0) :
    C.numerator = 0 := by
  exact C.numerator_eq_zero_of_collision ((C.denominator_eq_zero_iff).mp hden)

/-- The noncollision domain is the same as `x ≠ y`. -/
@[rep_depth thermo]
theorem noncollision_iff :
    C.NoncollisionDomain ↔ C.x ≠ C.y := by
  constructor <;> intro h
  · exact fun hxy => h ((C.denominator_eq_zero_iff).2 hxy)
  · exact fun hden => h ((C.denominator_eq_zero_iff).1 hden)

/-- The quotient unfolds to the ordinary scalar ratio on the noncollision domain. -/
@[rep_depth thermo]
theorem quotient_eq_ratio (h : C.NoncollisionDomain) :
    C.quotient h = (Real.exp C.x - Real.exp C.y) / (C.y - C.x) := by
  unfold quotient numerator
  rw [C.denominator_eq]

/--
Combined packet for the concrete two-node chart.
-/
@[rep_depth thermo]
theorem concrete_cancellation_packet :
    (C.denominator = C.y - C.x)
    ∧ (C.denominator = 0 ↔ C.x = C.y)
    ∧ ((C.denominator = 0) → C.numerator = 0)
    ∧ (C.NoncollisionDomain ↔ C.x ≠ C.y) := by
  exact ⟨C.denominator_eq, C.denominator_eq_zero_iff,
    C.denominator_zero_forces_numerator_zero, C.noncollision_iff⟩

end TwoNodeChart

end InfoGeometry.Canonical.WeylTwoNodeCancellationChart
