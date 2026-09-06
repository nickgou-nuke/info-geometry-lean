import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import InfoGeometry.Physics.Algebra.LogCFTDiracCommutator

/-!
# Conditional Krein and spectral-commutator interfaces

The Krein adjoint is represented by an explicit fundamental symmetry and an
explicit candidate adjoint.  Self-adjointness is therefore a property-based
statement.  The monodromy theorem below is an ordinary bounded-operator
identity; it is not a KMS or spectral-triple theorem.
-/

namespace InfoGeometry.Physics.Algebra

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

structure KreinSpaceStructure (H : Type*) [NormedAddCommGroup H]
    [NormedSpace ℝ H] where
  J : H →L[ℝ] H

def KreinSpaceStructureLaws
    (K : KreinSpaceStructure H) : Prop :=
  K.J.comp K.J = 1

def kreinOperatorAdjoint (K : KreinSpaceStructure H) (_T Tstar : H →L[ℝ] H) : H →L[ℝ] H :=
  K.J.comp (Tstar.comp K.J)

theorem continuous_kreinAdjoint
    (K : KreinSpaceStructure H) :
    Continuous (fun A : H →L[ℝ] H => kreinOperatorAdjoint K A A) := by
  unfold kreinOperatorAdjoint
  simpa [ContinuousLinearMap.comp_assoc] using
    (ContinuousLinearMap.postcomp (E := H) (F := H) (G := H) K.J).continuous.comp
      (ContinuousLinearMap.precomp (E := H) (F := H) (G := H) K.J).continuous

theorem spectral_dirac_monodromy_commutator
    (M : ContinuousMonodromyOperator H) (D : H →L[ℝ] H) :
    D.comp (M.lambda • ((1 : H →L[ℝ] H) + M.N)) -
        (M.lambda • ((1 : H →L[ℝ] H) + M.N)).comp D =
      M.lambda • (D.comp M.N - M.N.comp D) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.sub_apply]
  rw [map_smul, map_add]
  module

/-- The reduced monodromy commutator depends continuously on the Dirac operator. -/
theorem continuous_spectral_dirac_monodromy_commutator
    (M : ContinuousMonodromyOperator H) :
    Continuous (fun D : H →L[ℝ] H =>
      M.lambda • (D.comp M.N - M.N.comp D)) := by
  have hpre : Continuous (fun D : H →L[ℝ] H => D.comp M.N) :=
    (ContinuousLinearMap.precomp (E := H) (F := H) (G := H) M.N).continuous
  have hpost : Continuous (fun D : H →L[ℝ] H => M.N.comp D) :=
    (ContinuousLinearMap.postcomp (E := H) (F := H) (G := H) M.N).continuous
  simpa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply] using
    (Continuous.smul continuous_const (hpre.sub hpost))

theorem spectral_dirac_commutator_norm_bound
    (M : ContinuousMonodromyOperator H) (D : H →L[ℝ] H) :
    ‖M.lambda • (D.comp M.N - M.N.comp D)‖ ≤
      |M.lambda| * ‖D.comp M.N - M.N.comp D‖ := by
  exact ContinuousLinearMap.opNorm_smul_le M.lambda
    (D.comp M.N - M.N.comp D)

end InfoGeometry.Physics.Algebra
