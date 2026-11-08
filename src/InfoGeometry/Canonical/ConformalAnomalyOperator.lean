import InfoGeometry.Canonical.ConformalAnomalySource
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Canonical.ConformalUnification

open InfoGeometry.Canonical.KKTCore

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ConformalInference

variable (CI : ConformalInference E)

/--
Operator-owner package for the conformal anomaly source:
the noncommutative obstruction operator is primary; KKT structure records its
grade-zero/block form.
-/
@[rep_depth krein] def ObstructionOperatorOwner
    (X : InfoGeometry.Quantum.RealSplitCl11Action E) : Prop :=
  CI.projectorObstruction =
      CI.spectralChiralProjector * CI.metricChiralProjector
        - CI.metricChiralProjector * CI.spectralChiralProjector ∧
  IsGZero X CI.projectorObstruction ∧
  CI.projectorObstruction
      = plusProjector X * CI.projectorObstruction * plusProjector X
        + minusProjector X * CI.projectorObstruction * minusProjector X ∧
  plusProjector X * CI.projectorObstruction * minusProjector X = 0 ∧
  minusProjector X * CI.projectorObstruction * plusProjector X = 0

/--
Operator-owner package for the bounded squashed obstruction readout:
the operator remains grade-zero and block-diagonal in the same KKT split.
-/
@[rep_depth krein] def SquashedObstructionOperatorOwner
    (X : InfoGeometry.Quantum.RealSplitCl11Action E) : Prop :=
  IsGZero X CI.squashedProjectorObstruction ∧
  CI.squashedProjectorObstruction
      = plusProjector X * CI.squashedProjectorObstruction * plusProjector X
        + minusProjector X * CI.squashedProjectorObstruction * minusProjector X ∧
  plusProjector X * CI.squashedProjectorObstruction * minusProjector X = 0 ∧
  minusProjector X * CI.squashedProjectorObstruction * plusProjector X = 0

/--
Canonical operator-owner constructor:
explicit KKT wing witnesses force the obstruction into the grade-zero diagonal
block form, without any vanishing assumption.
-/
@[rep_depth krein] theorem obstructionOperatorOwner_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : IsGOne X CI.A)
    (hAMP : IsGNegOne X CI.A_MP)
    (hAD : IsGNegOne X CI.A_D) :
    ObstructionOperatorOwner (CI := CI) X := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact CI.projectorObstruction_eq_commutator
  · exact CI.projectorObstruction_isGZero_of_kkt_wings (X := X) hA hAMP hAD
  · exact CI.projectorObstruction_eq_diagonal_blocks_of_kkt_wings
      (X := X) hA hAMP hAD
  · exact CI.projectorObstruction_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings
      (X := X) hA hAMP hAD
  · exact CI.projectorObstruction_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings
      (X := X) hA hAMP hAD

/--
Canonical operator-owner constructor for the bounded squashed obstruction.
-/
@[rep_depth krein] theorem squashedObstructionOperatorOwner_of_kkt_wings
    (X : InfoGeometry.Quantum.RealSplitCl11Action E)
    (hA : IsGOne X CI.A)
    (hAMP : IsGNegOne X CI.A_MP)
    (hAD : IsGNegOne X CI.A_D) :
    SquashedObstructionOperatorOwner (CI := CI) X := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact CI.squashedProjectorObstruction_isGZero_of_kkt_wings
      (X := X) hA hAMP hAD
  · exact CI.squashedProjectorObstruction_eq_diagonal_blocks_of_kkt_wings
      (X := X) hA hAMP hAD
  · exact CI.squashedProjectorObstruction_plusProjector_mul_mul_minusProjector_eq_zero_of_kkt_wings
      (X := X) hA hAMP hAD
  · exact CI.squashedProjectorObstruction_minusProjector_mul_mul_plusProjector_eq_zero_of_kkt_wings
      (X := X) hA hAMP hAD

/--
Dilation-source identity on the operator layer:
under right-projector commutation, the dilation commutator is `-1/2` times the
projector-obstruction operator.
-/
@[rep_depth krein] theorem dilationSource_eq_neg_half_projectorObstruction_of_rightProjector_commute
    (hRight :
      CI.P_D * CI.P_MP_right = CI.P_MP_right * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D
      = -((2 : ℝ)⁻¹) • CI.projectorObstruction := by
  exact
    CI.spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_rightProjector_commute
      hRight

/--
Primary structured dilation-source identity on the operator layer:
if left/right Moore-Penrose projectors agree and the Drazin projector commutes
with the left metric projector, the dilation commutator is `-1/2` times the
projector-obstruction operator.
-/
@[rep_depth krein] theorem
    dilationSource_eq_neg_half_projectorObstruction_of_projectorAgreement_of_metricProjector_commute
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D
      = -((2 : ℝ)⁻¹) • CI.projectorObstruction := by
  exact
    CI.spectralProjector_commutator_dilation_eq_neg_half_projectorObstruction_of_projectorAgreement_of_metricProjector_commute
      hProj hLeft

/-- Canonical export alias for the structured dilation-source route. -/
@[rep_depth krein] theorem
    dilationSource_eq_neg_half_projectorObstruction_of_structuredProjectorHypotheses
    (hProj : CI.P_MP_right = CI.P_MP)
    (hLeft : CI.P_D * CI.P_MP = CI.P_MP * CI.P_D) :
    CI.P_D * CI.D - CI.D * CI.P_D
      = -((2 : ℝ)⁻¹) • CI.projectorObstruction := by
  exact
    CI.dilationSource_eq_neg_half_projectorObstruction_of_projectorAgreement_of_metricProjector_commute
      hProj hLeft

end ConformalInference

end InfoGeometry.Canonical.ConformalUnification
