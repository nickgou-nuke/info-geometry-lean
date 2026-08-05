import Mathlib.Tactic
import InfoGeometry.Canonical.CliffordDiracAlgebra
import InfoGeometry.Canonical.TrichotomyClosureBundle

namespace InfoGeometry.Canonical.TrichotomySummaryTheorems

open InfoGeometry.Canonical.CliffordDiracAlgebra
open InfoGeometry.Canonical.CausalConeProjectorBridge
open InfoGeometry.Canonical.TrichotomyClosureBundle
open InfoGeometry.Canonical.RealTomitaStandardSubspace

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Summary row (elliptic): `Op² = -1`. -/
theorem row_elliptic (A : Module.End ℝ V) :
    IsElliptic A ↔ A * A = -(1 : Module.End ℝ V) := by
  rfl

/-- Summary row (hyperbolic): `Op² = +1`. -/
theorem row_hyperbolic (A : Module.End ℝ V) :
    IsHyperbolic A ↔ A * A = (1 : Module.End ℝ V) := by
  rfl

/-- Summary row (parabolic): `Op² = 0`. -/
theorem row_parabolic (A : Module.End ℝ V) :
    IsParabolic A ↔ A * A = (0 : Module.End ℝ V) := by
  rfl

/-- Summary row (projective): `P² = P`. -/
theorem row_projective (P : Module.End ℝ V) :
    IsProjector P ↔ P * P = P := by
  rfl

/-- Hyperbolic involution gives projector splitting into `P±`. -/
theorem row_projector_split_of_involution (J : Module.End ℝ V) (hJ : IsInvolution J) :
    IsProjector (Pplus J) ∧ IsProjector (Pminus J) ∧
    Pplus J + Pminus J = (1 : Module.End ℝ V) ∧
    Pplus J * Pminus J = (0 : Module.End ℝ V) := by
  refine ⟨Projector.Pplus_idempotent (J := J) hJ,
    Projector.Pminus_idempotent (J := J) hJ,
    Projector.Pplus_add_Pminus (J := J),
    Projector.Pplus_comp_Pminus (J := J) hJ⟩

/-- Combined operator-table statement as a product of the four row equivalences. -/
theorem summary_operator_table (A P : Module.End ℝ V) :
    (IsElliptic A ↔ A * A = -(1 : Module.End ℝ V)) ∧
    (IsHyperbolic A ↔ A * A = (1 : Module.End ℝ V)) ∧
    (IsParabolic A ↔ A * A = (0 : Module.End ℝ V)) ∧
    (IsProjector P ↔ P * P = P) := by
  exact ⟨row_elliptic (A := A), row_hyperbolic (A := A), row_parabolic (A := A), row_projective (P := P)⟩

/-- Combined closure citation for trichotomy with cone-sector projector compatibility. -/
theorem summary_trichotomy_sector_closure
    (T : KANTriple V) {S : CausalSplit V} {Q : Module.End ℝ V}
    (hQ : IsConeCompatibleProjector S Q) :
    IsElliptic T.K ∧ IsHyperbolic T.A ∧ IsParabolic T.N ∧
    (∀ x, x ∈ S.bulk → Q x ∈ S.bulk) ∧
    (∀ x, x ∈ S.boundary → Q x ∈ S.boundary) ∧
    (∀ x, x ∈ S.nullCone → Q x ∈ S.nullCone) :=
  trichotomy_closed_under_sector_split (T := T) hQ

section StandardSector

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Combined closure citation for reduced Tomita transport on the standard physical sector. -/
theorem summary_tomita_reduced_involutive
    (K : Submodule ℝ H) (hK : IsStandardSubspace (H := H) K)
    (z : ↥(K ⊔ ImaginarySubmodule (H := H) K)) :
    reducedTransport (standardPhysicalProjector (H := H) K) (TomitaOnStandard (H := H) K hK)
      (reducedTransport (standardPhysicalProjector (H := H) K) (TomitaOnStandard (H := H) K hK) z)
      = z :=
  tomita_causal_reduction_involutive (H := H) K hK z

end StandardSector

end InfoGeometry.Canonical.TrichotomySummaryTheorems
