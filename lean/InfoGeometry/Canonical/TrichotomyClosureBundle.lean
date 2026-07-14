import Mathlib
import InfoGeometry.Canonical.CliffordDiracAlgebra
import InfoGeometry.Canonical.CausalConeProjectorBridge

namespace TrichotomyClosureBundle

open InfoGeometry.Canonical.CliffordDiracAlgebra
open InfoGeometry.Canonical.CausalConeProjectorBridge
open InfoGeometry.Canonical.RealTomitaStandardSubspace

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Trichotomy (`K,A,N`) plus cone-compatible projector sector laws in one bundle. -/
theorem trichotomy_closed_under_sector_split
    (T : KANTriple V) {S : CausalSplit V} {P : Module.End ℝ V}
    (hP : IsConeCompatibleProjector S P) :
    IsElliptic T.K ∧ IsHyperbolic T.A ∧ IsParabolic T.N ∧
    (∀ x, x ∈ S.bulk → P x ∈ S.bulk) ∧
    (∀ x, x ∈ S.boundary → P x ∈ S.boundary) ∧
    (∀ x, x ∈ S.nullCone → P x ∈ S.nullCone) := by
  refine ⟨T.k_sq, T.a_sq, T.n_sq, ?_, ?_, ?_⟩
  · exact cone_projector_preserves_bulk hP
  · exact cone_projector_preserves_boundary hP
  · exact cone_projector_preserves_null hP

/-- Parabolic (`N²=0`) boundary channel is exact and remains in the boundary sector. -/
theorem nilpotent_boundary_channel_exact
    (S : CausalSplit V) (N : Module.End ℝ V)
    (hPar : IsParabolic N) (hBoundary : IsBoundaryStable S N) :
    ∀ x, x ∈ S.boundary → N (N x) = 0 ∧ N (N x) ∈ S.boundary := by
  intro x hx
  have hNx : N x ∈ S.boundary := hBoundary x hx
  have hNNxBoundary : N (N x) ∈ S.boundary := hBoundary (N x) hNx
  have hNNxZero : N (N x) = 0 := by
    simpa [IsParabolic, Module.End.mul_eq_comp, LinearMap.comp_apply] using
      congrArg (fun f : Module.End ℝ V => f x) hPar
  exact ⟨hNNxZero, hNNxBoundary⟩

/-- Hyperbolic transport (`N²=1`) preserves projected bulk states under Drazin data. -/
theorem hyperbolic_transport_preserves_projected_bulk
    {S : CausalSplit V} (D : DrazinProjectorData S)
    (hHyp : IsHyperbolic D.N) (hNbulk : IsBulkStable S D.N) :
    ∀ x, x ∈ S.bulk → D.P (D.N (D.N x)) = x := by
  intro x hx
  have hNNx : D.N (D.N x) = x := by
    simpa [IsHyperbolic, Module.End.mul_eq_comp, LinearMap.comp_apply] using
      congrArg (fun f : Module.End ℝ V => f x) hHyp
  have hNxBulk : D.N x ∈ S.bulk := hNbulk x hx
  have hNNxBulk : D.N (D.N x) ∈ S.bulk := hNbulk (D.N x) hNxBulk
  have hFix : D.P (D.N (D.N x)) = D.N (D.N x) := D.hBulkFix (D.N (D.N x)) hNNxBulk
  simpa [hNNx] using hFix

section StandardSector

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Reduced Tomita transport is involutive on the standard physical sector. -/
theorem tomita_causal_reduction_involutive
    (K : Submodule ℝ H) (hK : IsStandardSubspace (H := H) K)
    (z : ↥(K ⊔ ImaginarySubmodule (H := H) K)) :
    reducedTransport (standardPhysicalProjector (H := H) K) (TomitaOnStandard (H := H) K hK)
      (reducedTransport (standardPhysicalProjector (H := H) K) (TomitaOnStandard (H := H) K hK) z)
      = z :=
  reduced_tomita_on_standard_involutive (H := H) K hK z

end StandardSector

end TrichotomyClosureBundle
