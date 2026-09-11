import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Algebra.KreinSpectralDiracCommutator

/-!
# Topological Krein spectral-Dirac readout

This owner packages the already-proved continuity statements for the Krein
adjoint and the reduced spectral Dirac commutator as a topological layer.
It does not introduce any new modular, KMS, or spectral-triple claims.
-/

namespace InfoGeometry.Topology.KreinSpectralDiracTopological

open InfoGeometry.Physics.Algebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The Krein adjoint packaged as a topological map on bounded operators. -/
def kreinAdjointMap (K : KreinSpaceStructure H) :
  (H →L[ℝ] H) → (H →L[ℝ] H) :=
  fun T => kreinOperatorAdjoint K T T

/-- The Krein adjoint map is continuous. -/
theorem continuous_kreinAdjointMap
    (K : KreinSpaceStructure H) :
    Continuous (kreinAdjointMap K) := by
  simpa [kreinAdjointMap] using
    (continuous_kreinAdjoint (H := H) K)

/-- The reduced spectral Dirac commutator packaged as a topological map. -/
def spectralDiracCommutatorMap
    (M : ContinuousMonodromyOperator H) :
    (H →L[ℝ] H) → (H →L[ℝ] H) :=
  fun D => M.lambda • (D.comp M.N - M.N.comp D)

/-- The reduced spectral Dirac commutator depends continuously on the Dirac operator. -/
theorem continuous_spectralDiracCommutatorMap
    (M : ContinuousMonodromyOperator H) :
    Continuous (spectralDiracCommutatorMap M) := by
  simpa [spectralDiracCommutatorMap] using
    (continuous_spectral_dirac_monodromy_commutator (H := H) M)

@[simp] theorem kreinAdjointMap_apply
    (K : KreinSpaceStructure H) (T : H →L[ℝ] H) :
    kreinAdjointMap K T = kreinOperatorAdjoint K T T :=
  rfl

@[simp] theorem spectralDiracCommutatorMap_apply
    (M : ContinuousMonodromyOperator H) (D : H →L[ℝ] H) :
    spectralDiracCommutatorMap M D =
      M.lambda • (D.comp M.N - M.N.comp D) :=
  rfl
