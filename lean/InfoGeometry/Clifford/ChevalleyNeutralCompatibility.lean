/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ChevalleySpinorBlueprint
import InfoGeometry.Canonical.KahlerAtiyahCartanForms

/-!
# Compatibility of the existing Chevalley and neutral exterior owners

The existing `ChevalleySpinorBlueprint` constructs the full representation of
`CliffordAlgebra (Qsplit E)` on `SpinorSpace E = ExteriorAlgebra ℝ E`.
This file identifies its quadratic form with the unscaled neutral form and
its native creation/contraction operators with the Kähler--Atiyah owners.
The resulting anticommutator and vacuum commutator are identities in the
actual noncommutative endomorphism algebra. No second spinor representation
is introduced.

The normalization is `Qsplit E (v, φ) = φ v`. Its polarization is the
canonical symmetric neutral pairing; hence the corresponding symmetric
Clifford metric is one half of that pairing. The assertions here do not
identify exterior parity with an isotropic spinor polarization or construct
a Mukai pairing, an irreducibility theorem, or a para-Kähler manifold.
-/

noncomputable section

namespace InfoGeometry.Clifford.ChevalleyNeutralCompatibility

open InfoGeometry.Clifford.NeutralPhaseSpaceCore
open InfoGeometry.Canonical.KahlerAtiyahCartanForms

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The existing Chevalley quadratic form uses the unscaled neutral normalization. -/
theorem Qsplit_eq_canonicalNeutralFormUnscaled :
    Qsplit E = canonicalNeutralFormUnscaled (E := E) := by
  ext X
  rw [canonicalNeutralFormUnscaled_apply]
  rfl

/-- Polarizing the Chevalley quadratic form gives the canonical neutral pairing. -/
theorem Qsplit_polar_eq_canonicalNeutralBilin (X Y : SplitSpace E) :
    QuadraticMap.polar (Qsplit E) X Y = canonicalNeutralBilin X Y := by
  rw [Qsplit_eq_canonicalNeutralFormUnscaled,
    canonicalNeutralFormUnscaled_polar]

/-- The two exterior-multiplication owners are equal on their actual carrier. -/
theorem extAction_eq_wedgeOperator (v : E) :
    extAction v = wedgeOperator v := by
  apply LinearMap.ext
  intro ω
  rfl

/-- The two contraction owners select the same native `contractLeft` operator. -/
theorem intAction_eq_contractionOperator (φ : Module.Dual ℝ E) :
    intAction φ = contractionOperator φ := rfl

/-- The existing full split action agrees with native wedge plus contraction. -/
theorem spinorAction_eq_wedge_add_contraction (X : SplitSpace E) :
    spinorAction X = wedgeOperator X.1 + contractionOperator X.2 := by
  rw [spinorAction, extAction_eq_wedgeOperator, intAction_eq_contractionOperator]

/-- The full existing spinor action obeys the neutral Clifford anticommutator. -/
theorem spinorAction_anticommutator (X Y : SplitSpace E) :
    spinorAction X * spinorAction Y + spinorAction Y * spinorAction X =
      canonicalNeutralBilin X Y • (1 : Module.End ℝ (SpinorSpace E)) := by
  calc
    spinorAction X * spinorAction Y + spinorAction Y * spinorAction X =
        (wedgeOperator X.1 * wedgeOperator Y.1 +
          wedgeOperator Y.1 * wedgeOperator X.1) +
        (contractionOperator X.2 * wedgeOperator Y.1 +
          wedgeOperator Y.1 * contractionOperator X.2) +
        (contractionOperator Y.2 * wedgeOperator X.1 +
          wedgeOperator X.1 * contractionOperator Y.2) +
        (contractionOperator X.2 * contractionOperator Y.2 +
          contractionOperator Y.2 * contractionOperator X.2) := by
            simp only [spinorAction_eq_wedge_add_contraction, add_mul, mul_add]
            abel
    _ = canonicalNeutralBilin X Y • (1 : Module.End ℝ (SpinorSpace E)) := by
      rw [wedgeOperator_anticommutator_zero,
        contractionOperator_anticommutator_zero,
        contraction_wedge_CAR, contraction_wedge_CAR]
      simp only [zero_add, add_zero, ← add_smul, canonicalNeutralBilin_apply]

/-- The existing pointwise square law is the unscaled neutral law in `End(Λ E)`. -/
theorem spinorAction_sq_neutral (X : SplitSpace E) :
    spinorAction X * spinorAction X =
      canonicalNeutralFormUnscaled X • (1 : Module.End ℝ (SpinorSpace E)) := by
  apply LinearMap.ext
  intro ω
  change spinorAction X (spinorAction X ω) = canonicalNeutralFormUnscaled X • ω
  rw [spinorAction_sq, Qsplit_eq_canonicalNeutralFormUnscaled, Algebra.smul_def]

/-- Generator evaluation for the already constructed native Clifford representation. -/
@[simp] theorem abstractSpinorRep_ι (X : SplitSpace E) :
    abstractSpinorRep E (CliffordAlgebra.ι (Qsplit E) X) = spinorAction X := by
  exact CliffordAlgebra.lift_ι_apply _ _ X

/-- Pure vector generators of the existing representation act by wedge multiplication. -/
@[simp] theorem abstractSpinorRep_ι_fst (v : E) :
    abstractSpinorRep E
        (CliffordAlgebra.ι (Qsplit E) (v, (0 : Module.Dual ℝ E))) =
      wedgeOperator v := by
  rw [abstractSpinorRep_ι, spinorAction_eq_wedge_add_contraction]
  simp [contractionOperator]

/-- Pure covector generators of the existing representation act by contraction. -/
@[simp] theorem abstractSpinorRep_ι_snd (φ : Module.Dual ℝ E) :
    abstractSpinorRep E (CliffordAlgebra.ι (Qsplit E) ((0 : E), φ)) =
      contractionOperator φ := by
  rw [abstractSpinorRep_ι, spinorAction_eq_wedge_add_contraction]
  simp [wedgeOperator]

/-- Restriction of the existing full action to a metric graph is its Cartan action. -/
theorem spinorAction_metricGraph (g : LinearMap.BilinForm ℝ E) (v : E) :
    spinorAction (metricGraph g v) = cartanCliffordAction g v := by
  rw [spinorAction_eq_wedge_add_contraction]
  rfl

/-- Vacuum evaluation of the ordered commutator detects the vector-covector pairing. -/
theorem int_ext_commutator_apply_one (φ : Module.Dual ℝ E) (v : E) :
    (intAction φ * extAction v - extAction v * intAction φ) (1 : SpinorSpace E) =
      algebraMap ℝ (SpinorSpace E) (φ v) := by
  change
    CliffordAlgebra.contractLeft φ (CliffordAlgebra.ι 0 v * 1) -
        CliffordAlgebra.ι 0 v * CliffordAlgebra.contractLeft φ (1 : SpinorSpace E) =
      algebraMap ℝ (SpinorSpace E) (φ v)
  rw [mul_one, CliffordAlgebra.contractLeft_ι,
    CliffordAlgebra.contractLeft_one, mul_zero, sub_zero]

/-- Creation and contraction cannot commute when their evaluation pairing is nonzero. -/
theorem int_ext_not_commute (φ : Module.Dual ℝ E) (v : E) (hφv : φ v ≠ 0) :
    intAction φ * extAction v ≠ extAction v * intAction φ := by
  intro hcomm
  have hz :
      (intAction φ * extAction v - extAction v * intAction φ)
        (1 : SpinorSpace E) = 0 := by
    rw [hcomm, sub_self]
    rfl
  rw [int_ext_commutator_apply_one] at hz
  exact hφv ((ExteriorAlgebra.algebraMap_eq_zero_iff E (φ v)).mp hz)

end InfoGeometry.Clifford.ChevalleyNeutralCompatibility
