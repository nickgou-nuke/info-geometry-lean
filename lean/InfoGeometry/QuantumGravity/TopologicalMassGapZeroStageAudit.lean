import InfoGeometry.QuantumGravity.TwistorMassGenesis
import InfoGeometry.QuantumGravity.ColimitTwistorMass
import Mathlib.Tactic

/-!
# Zero-stage obstruction in the current finite-stage mass-gap predicates

The two predicates quantified over every natural stage include stage zero.
At that stage the matrix carrier has no columns and therefore contains only
the zero matrix.  This audit records that the current universal predicates
are consequently uninhabited; successor-stage propagation alone cannot prove
them.
-/

namespace InfoGeometry.QuantumGravity.TopologicalMassGapZeroStageAudit

open InfoGeometry.QuantumGravity.TwistorMassGenesis
open InfoGeometry.QuantumGravity.ColimitTwistorMass
open InfoGeometry.Topology.AmplituhedronColimit

/-- The stage-one carrier has a concrete nonzero matrix (the all-ones
matrix). -/
theorem finite_obstruction_at_one :
    InfoGeometry.QuantumGravity.TwistorMassGenesis.finite_obstruction_class 1 := by
  refine ⟨fun _ _ => 1, ?_⟩
  intro h
  have h00 := congrArg (fun M : AmplituhedronAlgebra 1 => M 0 0) h
  norm_num at h00

/-- The zero-column matrix carrier has no nonzero element. -/
theorem no_finite_obstruction_at_zero :
    ¬ InfoGeometry.QuantumGravity.TwistorMassGenesis.finite_obstruction_class 0 := by
  rintro ⟨Z, hZ⟩
  apply hZ
  ext i j
  exact Fin.elim0 j

/-- Starting at stage one, every later matrix carrier has a nonzero element;
the proof propagates the explicit stage-one witness along the injective
finite-stage inclusions. -/
theorem finite_obstruction_at_positive_stage {n : ℕ} (hn : 0 < n) :
    InfoGeometry.QuantumGravity.TwistorMassGenesis.finite_obstruction_class n := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => exact finite_obstruction_at_one
    | succ n ih =>
      exact InfoGeometry.QuantumGravity.TwistorMassGenesis.colimit_injection_preserves_obstruction
        (n + 1) ih

/-- For the current rectangular-matrix predicate, nontriviality is exactly
the assertion that the column index is positive. -/
theorem finite_obstruction_class_iff_positive_stage (n : ℕ) :
    InfoGeometry.QuantumGravity.TwistorMassGenesis.finite_obstruction_class n ↔
      0 < n := by
  constructor
  · intro h
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    exact no_finite_obstruction_at_zero h
  · exact finite_obstruction_at_positive_stage

/-- The all-stages predicate from `TwistorMassGenesis` is false because it
requires an obstruction at stage zero. -/
theorem not_topological_mass_gap :
    ¬ InfoGeometry.QuantumGravity.TwistorMassGenesis.topological_mass_gap := by
  intro h
  exact no_finite_obstruction_at_zero (h 0)

/-- The Planck parameter is irrelevant to the zero-stage obstruction: the
current finite Heisenberg predicate also quantifies over an empty-column
matrix carrier at stage zero. -/
theorem no_finite_heisenberg_obstruction_at_zero (ħ : ℝ) :
    ¬ InfoGeometry.QuantumGravity.ColimitTwistorMass.finite_heisenberg_obstruction 0 ħ := by
  rintro ⟨Z, hZ⟩
  apply hZ
  ext i j
  exact Fin.elim0 j

/-- The finite Heisenberg predicate, as currently defined by nonzero matrix
existence, also holds at every positive stage; its parameter is not used by
the predicate. -/
theorem finite_heisenberg_obstruction_at_positive_stage {n : ℕ} (ħ : ℝ)
    (hn : 0 < n) :
    InfoGeometry.QuantumGravity.ColimitTwistorMass.finite_heisenberg_obstruction n ħ := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => exact finite_obstruction_at_one
    | succ n ih =>
      exact InfoGeometry.QuantumGravity.ColimitTwistorMass.obstruction_persists_in_tower
        (n + 1) ħ ih

/-- In the current definition, the finite “Heisenberg obstruction” is
independent of `ħ` and is equivalent to positivity of the stage index. -/
theorem finite_heisenberg_obstruction_iff_positive_stage (n : ℕ) (ħ : ℝ) :
    InfoGeometry.QuantumGravity.ColimitTwistorMass.finite_heisenberg_obstruction n ħ ↔
      0 < n := by
  change InfoGeometry.QuantumGravity.TwistorMassGenesis.finite_obstruction_class n ↔
    0 < n
  exact finite_obstruction_class_iff_positive_stage n

/-- The universal predicate called the emergent colimit mass gap is false at
every value of `ħ` under its present all-stages definition. -/
theorem not_emergent_colimit_mass_gap (ħ : ℝ) :
    ¬ InfoGeometry.QuantumGravity.ColimitTwistorMass.emergent_colimit_mass_gap ħ := by
  intro h
  exact no_finite_heisenberg_obstruction_at_zero ħ (h 0)

end InfoGeometry.QuantumGravity.TopologicalMassGapZeroStageAudit
