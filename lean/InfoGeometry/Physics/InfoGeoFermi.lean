import Mathlib.Tactic
import InfoGeometry.Physics.IsospinMirrorDynamics
import InfoGeometry.Physics.TKKIsospinEmbedding
import InfoGeometry.Physics.TKKZorn

namespace InfoGeometry.Physics

variable {R : Type*} [CommRing R]
variable {L : Type*} [AddCommGroup L] [Module R L] [LieRing L] [LieAlgebra R L]
    [TKKAlgebra R L]

/-- A projective nuclear state is canonically a nonzero vector in the ambient
TKK Lie algebra.  The subtype is the native proof-bearing carrier; no custom
record is needed for the value plus its nonvanishing proposition. -/
abbrev TKKNuclearState (L : Type*) [Zero L] := {x : L // x ≠ 0}

namespace TKKNuclearState

abbrev state_vector (ψ : TKKNuclearState L) : L := ψ.1

abbrev is_projective_ray (ψ : TKKNuclearState L) : ψ.state_vector ≠ 0 := ψ.2

end TKKNuclearState

/-- The abstract Fisher metric in this file is the zero baseline.  Nontrivial
metric deformation is owned by the concrete Zorn lane in `TKKZorn.lean`. -/
def TKKFisherInformationMetric (_x _y : TKKNuclearState L) : R :=
  0

/-- Fermi transport by a zero-grade generator, with the required projective
nonzero proof supplied explicitly. -/
def fermi_operator (g0 : L) (ψ : TKKNuclearState L)
    (h_nonzero : ⁅g0, ψ.state_vector⁆ ≠ 0) : TKKNuclearState L :=
  ⟨⁅g0, ψ.state_vector⁆, h_nonzero⟩

/-- Gamow-Teller transport by a linear operator, with the required projective
nonzero proof supplied explicitly. -/
def gamow_teller_operator (T : L →ₗ[R] L) (ψ : TKKNuclearState L)
    (h_nonzero : T ψ.state_vector ≠ 0) : TKKNuclearState L :=
  ⟨T ψ.state_vector, h_nonzero⟩

/-- The zero abstract Fisher metric is invariant under proof-carrying Fermi
transport. -/
theorem fermi_isometry_invariance (g0 : L)
    (hF : ∀ ψ : TKKNuclearState L, ⁅g0, ψ.state_vector⁆ ≠ 0)
    (x y : TKKNuclearState L) :
    TKKFisherInformationMetric (R := R)
        (fermi_operator g0 x (hF x))
        (fermi_operator g0 y (hF y)) =
      TKKFisherInformationMetric (R := R) x y := by
  rfl

/-- In the abstract zero-metric baseline there is no Gamow-Teller metric
deformation witness.  Concrete nonzero deformation must use the Zorn metric. -/
theorem no_gt_metric_deformation_for_zero_metric
    (T : L →ₗ[R] L)
    (hT : ∀ ψ : TKKNuclearState L, T ψ.state_vector ≠ 0) :
    ¬ ∃ x y : TKKNuclearState L,
      TKKFisherInformationMetric (R := R)
          (gamow_teller_operator T x (hT x))
          (gamow_teller_operator T y (hT y)) ≠
        TKKFisherInformationMetric (R := R) x y := by
  rintro ⟨x, y, hneq⟩
  exact hneq rfl

/-- The generic triality map can be used as a Gamow-Teller transport operator
whenever projective nonvanishing is supplied. -/
theorem triality_gt_zero_metric_no_deformation
    (hT : ∀ ψ : TKKNuclearState L, TrialityProjector (R := R) (L := L) ψ.state_vector ≠ 0) :
    ¬ ∃ x y : TKKNuclearState L,
      TKKFisherInformationMetric (R := R)
          (gamow_teller_operator (TrialityProjector (R := R) (L := L)) x (hT x))
          (gamow_teller_operator (TrialityProjector (R := R) (L := L)) y (hT y)) ≠
        TKKFisherInformationMetric (R := R) x y := by
  exact no_gt_metric_deformation_for_zero_metric
    (R := R) (L := L) (TrialityProjector (R := R) (L := L)) hT

end InfoGeometry.Physics
