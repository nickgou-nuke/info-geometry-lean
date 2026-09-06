import InfoGeometry.Meta.Architecture
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic

/-!
# InfoGeometry.Canonical.QVandermondePhaseLockShadow

Finite `q`-deformed Vandermonde shadow in the complex lane.

This file is an honest owner for the next algebraic step after the real
Vandermonde/cancellation corridor:

* two-node `q`-collision factor `x - q y`,
* three-node `A₂`-style product of `q`-collision factors,
* exact zero-locus characterization,
* norm preservation on the collision locus under the unit-phase property
  `‖q‖ = 1`.

It does **not** claim anything about the Riemann property, Bost-Connes,
KMS spectra, or modular absorption lines.  It is only the finite
`q`-Vandermonde phase-lock shadow.
-/

namespace InfoGeometry.Canonical.QVandermondePhaseLockShadow

/-- Two-node complex `q`-deformed collision chart. -/
@[rep_depth thermo]
structure TwoNodeQChart where
  q : ℂ
  x : ℂ
  y : ℂ

namespace TwoNodeQChart

variable (C : TwoNodeQChart)

/-- The finite two-node `q`-Vandermonde factor. -/
@[rep_depth thermo]
def denominator : ℂ :=
  C.x - C.q * C.y

/-- Unit-phase condition for the deformation parameter. -/
@[rep_depth thermo]
def UnitPhase : Prop :=
  ‖C.q‖ = 1

/-- The `q`-collision locus is exactly `x = q y`. -/
@[rep_depth thermo]
theorem denominator_eq_zero_iff :
    C.denominator = 0 ↔ C.x = C.q * C.y := by
  unfold denominator
  constructor <;> intro h
  · exact sub_eq_zero.mp h
  · simpa [denominator] using sub_eq_zero.mpr h

/-- Away from `q`-collision the deformed factor is nonzero. -/
@[rep_depth thermo]
theorem denominator_ne_zero_iff :
    C.denominator ≠ 0 ↔ C.x ≠ C.q * C.y := by
  exact not_congr C.denominator_eq_zero_iff

/--
If the `q`-phase has unit norm, `q`-locked collision preserves the norm of the
colliding nodes.
-/
@[rep_depth thermo]
theorem norm_eq_of_unitPhase_of_collision
    (hq : C.UnitPhase) (hcol : C.denominator = 0) :
    ‖C.x‖ = ‖C.y‖ := by
  have hx : C.x = C.q * C.y := (C.denominator_eq_zero_iff).1 hcol
  rw [hx, Complex.norm_mul, hq, one_mul]

/-- Combined packet for the two-node phase-lock shadow. -/
@[rep_depth thermo]
theorem two_node_phase_lock_packet :
    (C.denominator = 0 ↔ C.x = C.q * C.y)
    ∧ (C.denominator ≠ 0 ↔ C.x ≠ C.q * C.y)
    ∧ (C.UnitPhase → C.denominator = 0 → ‖C.x‖ = ‖C.y‖) := by
  exact ⟨C.denominator_eq_zero_iff, C.denominator_ne_zero_iff,
    C.norm_eq_of_unitPhase_of_collision⟩

end TwoNodeQChart

/-- Three-node finite `A₂`-style complex `q`-Vandermonde chart. -/
@[rep_depth thermo]
structure A2QChart where
  q : ℂ
  x : ℂ
  y : ℂ
  z : ℂ

namespace A2QChart

variable (C : A2QChart)

/-- Unit-phase condition for the deformation parameter. -/
@[rep_depth thermo]
def UnitPhase : Prop :=
  ‖C.q‖ = 1

/-- The explicit finite `q`-deformed Vandermonde factor in the `A₂` lane. -/
@[rep_depth thermo]
def denominatorFactor : ℂ :=
  (C.y - C.q * C.x) * (C.z - C.q * C.x) * (C.z - C.q * C.y)

/--
The `A₂` `q`-Vandermonde factor vanishes exactly when one of the three
pairwise `q`-collision factors vanishes.
-/
@[rep_depth thermo]
theorem denominatorFactor_eq_zero_iff :
    C.denominatorFactor = 0 ↔
      C.y = C.q * C.x ∨ C.z = C.q * C.x ∨ C.z = C.q * C.y := by
  unfold denominatorFactor
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · left
        exact sub_eq_zero.mp h1
      · right
        left
        exact sub_eq_zero.mp h2
    · right
      right
      exact sub_eq_zero.mp h3
  · intro h
    rcases h with h1 | h2 | h3
    · simp [h1]
    · simp [h2]
    · simp [h3]

/--
Under the unit-phase condition, any vanishing of the finite `q`-Vandermonde
factor forces norm equality for at least one `q`-locked pair.
-/
@[rep_depth thermo]
theorem exists_norm_locked_pair_of_unitPhase_of_collision
    (hq : C.UnitPhase) (hcol : C.denominatorFactor = 0) :
    ‖C.y‖ = ‖C.x‖ ∨ ‖C.z‖ = ‖C.x‖ ∨ ‖C.z‖ = ‖C.y‖ := by
  rcases (C.denominatorFactor_eq_zero_iff).1 hcol with hyx | hzx | hzy
  · left
    rw [hyx, Complex.norm_mul, hq, one_mul]
  · right
    left
    rw [hzx, Complex.norm_mul, hq, one_mul]
  · right
    right
    rw [hzy, Complex.norm_mul, hq, one_mul]

/-- Combined packet for the finite `A₂` `q`-phase-lock shadow. -/
@[rep_depth thermo]
theorem a2_phase_lock_packet :
    (C.denominatorFactor = 0 ↔
      C.y = C.q * C.x ∨ C.z = C.q * C.x ∨ C.z = C.q * C.y)
    ∧
    (C.UnitPhase →
      C.denominatorFactor = 0 →
      ‖C.y‖ = ‖C.x‖ ∨ ‖C.z‖ = ‖C.x‖ ∨ ‖C.z‖ = ‖C.y‖) := by
  exact ⟨C.denominatorFactor_eq_zero_iff,
    C.exists_norm_locked_pair_of_unitPhase_of_collision⟩

end A2QChart

end InfoGeometry.Canonical.QVandermondePhaseLockShadow
