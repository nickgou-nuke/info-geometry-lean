import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Physics.Algebra.TripotentPeirceProjectors

/-!
# Operator trifactor of the split-octonion axial flow

The normalized commutator `D = (1/2) ad_ell` is an endomorphism of the full
canonical Zorn carrier.  This owner proves its tripotence directly from the
canonical coordinates and then specializes the existing noncommutative
tripotent projector calculus to `Module.End ℝ CanonicalZorn`.

The zero projector is a proved algebraic null-sector projector.  No analytic
defect, KMS, Fredholm, or thermodynamic identification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Physics.Algebra

abbrev CZ := CanonicalZorn
abbrev EndCZ := Module.End ℝ CZ

/-- Normalized axial grading operator `D = (1/2) ad_ell`. -/
noncomputable def ellGrading : EndCZ :=
  (1 / 2 : ℝ) • ellCommutator

@[simp] theorem ellGrading_apply (X : CZ) :
    ellGrading X = (1 / 2 : ℝ) • ellCommutator X :=
  rfl

/-- The unnormalized axial commutator satisfies its global cubic polynomial
on every canonical Zorn vector. -/
theorem ellCommutator_cube_apply (X : CZ) :
    ellCommutator (ellCommutator (ellCommutator X)) =
      (4 : ℝ) • ellCommutator X := by
  ext i <;>
    simp [ellCommutator, lUnit,
      InfoGeometry.Algebra.Zorn.G2TrifactorSU3.zMul,
      Equiv.smul_def, InfoGeometry.Canonical.ZornMatrix.coordEquiv,
      InfoGeometry.Canonical.ZornMatrix.dot,
      InfoGeometry.Canonical.ZornMatrix.cross]
  all_goals (try fin_cases i) <;> ring_nf

/-- Basis-independent operator identity `(ad_ell)^3 = 4 ad_ell`. -/
theorem ellCommutator_cube :
    ellCommutator ^ 3 = (4 : ℝ) • ellCommutator := by
  apply LinearMap.ext
  intro X
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply,
    LinearMap.smul_apply]
  exact ellCommutator_cube_apply X

/-- The normalized axial grading is a genuine tripotent endomorphism. -/
theorem ellGrading_tripotent : ellGrading ^ 3 = ellGrading := by
  apply LinearMap.ext
  intro X
  simp only [ellGrading, pow_succ, pow_zero, one_mul,
    Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_smul]
  rw [ellCommutator_cube_apply]
  module

/-- Positive projector of the normalized axial flow. -/
noncomputable def flowPPlus : EndCZ :=
  projPos ellGrading

/-- Zero/null projector of the normalized axial flow. -/
noncomputable def flowPZero : EndCZ :=
  projZero ellGrading

/-- Negative projector of the normalized axial flow. -/
noncomputable def flowPMinus : EndCZ :=
  projNeg ellGrading

theorem flowPPlus_idempotent : flowPPlus * flowPPlus = flowPPlus := by
  exact projPos_idempotent (T := ellGrading) (by
    simpa [pow_three] using ellGrading_tripotent)

theorem flowPZero_idempotent : flowPZero * flowPZero = flowPZero := by
  exact projZero_idempotent (T := ellGrading) (by
    simpa [pow_three] using ellGrading_tripotent)

theorem flowPMinus_idempotent : flowPMinus * flowPMinus = flowPMinus := by
  exact projNeg_idempotent (T := ellGrading) (by
    simpa [pow_three] using ellGrading_tripotent)

/-- The three native operator projectors resolve the identity. -/
theorem flow_projectors_sum :
    flowPPlus + flowPZero + flowPMinus = 1 := by
  exact proj_sum_eq_id (T := ellGrading)

/-- The normalized generator annihilates its zero/null projector. -/
theorem ellGrading_mul_flowPZero : ellGrading * flowPZero = 0 := by
  unfold flowPZero projZero
  calc
    ellGrading * (1 - ellGrading * ellGrading) =
        ellGrading - ellGrading * ellGrading * ellGrading := by noncomm_ring
    _ = 0 := by
      have h : ellGrading * ellGrading * ellGrading = ellGrading := by
        simpa [pow_three] using ellGrading_tripotent
      rw [h]
      simp

/-- The normalized generator is reconstructed from its active projectors. -/
theorem flowPPlus_sub_flowPMinus :
    flowPPlus - flowPMinus = ellGrading := by
  exact projPos_sub_projNeg (T := ellGrading)

end InfoGeometry.Lie.SplitOctonionEllOperatorTrifactor
