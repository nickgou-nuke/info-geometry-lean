import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CliffordDiracAlgebra
import InfoGeometry.Canonical.RealTomitaStandardSubspace

namespace InfoGeometry.Canonical.CausalConeProjectorBridge

open InfoGeometry.Canonical.CliffordDiracAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Real sector split: bulk, boundary, and null cone sectors. -/
structure CausalSplit (V : Type*) [AddCommGroup V] [Module ℝ V] where
  bulk : Submodule ℝ V
  boundary : Submodule ℝ V
  nullCone : Submodule ℝ V

/-- Endomorphism preserving each causal sector. -/
def IsConeCompatibleProjector (S : CausalSplit V) (P : Module.End ℝ V) : Prop :=
  IsProjector P ∧
  (∀ x, x ∈ S.bulk → P x ∈ S.bulk) ∧
  (∀ x, x ∈ S.boundary → P x ∈ S.boundary) ∧
  (∀ x, x ∈ S.nullCone → P x ∈ S.nullCone)

/-- Bulk-stability of an operator. -/
def IsBulkStable (S : CausalSplit V) (T : Module.End ℝ V) : Prop :=
  ∀ x, x ∈ S.bulk → T x ∈ S.bulk

/-- Boundary-stability of an operator. -/
def IsBoundaryStable (S : CausalSplit V) (T : Module.End ℝ V) : Prop :=
  ∀ x, x ∈ S.boundary → T x ∈ S.boundary

/-- Null-sector stability of an operator. -/
def IsNullStable (S : CausalSplit V) (T : Module.End ℝ V) : Prop :=
  ∀ x, x ∈ S.nullCone → T x ∈ S.nullCone

/-- Abstract Drazin-style compatibility data for transport on the bulk sector. -/
structure DrazinProjectorData (S : CausalSplit V) where
  P : Module.End ℝ V
  N : Module.End ℝ V
  hProj : IsProjector P
  hComm : P * N = N * P
  hBulkFix : ∀ x, x ∈ S.bulk → P x = x

/-- Abstract Moore–Penrose boundary lift package. -/
structure MoorePenroseBoundaryLift (S : CausalSplit V) where
  proj : Module.End ℝ V
  hProj : IsProjector proj
  lift : S.boundary →ₗ[ℝ] V
  proj_on_lift : ∀ b : S.boundary, proj (lift b) = (b : V)

theorem cone_projector_preserves_bulk {S : CausalSplit V} {P : Module.End ℝ V}
    (hP : IsConeCompatibleProjector S P) :
    ∀ x, x ∈ S.bulk → P x ∈ S.bulk :=
  hP.2.1

theorem cone_projector_preserves_boundary {S : CausalSplit V} {P : Module.End ℝ V}
    (hP : IsConeCompatibleProjector S P) :
    ∀ x, x ∈ S.boundary → P x ∈ S.boundary :=
  hP.2.2.1

theorem cone_projector_preserves_null {S : CausalSplit V} {P : Module.End ℝ V}
    (hP : IsConeCompatibleProjector S P) :
    ∀ x, x ∈ S.nullCone → P x ∈ S.nullCone :=
  hP.2.2.2

/-- Drazin-compatible projector transport is bulk-stable. -/
theorem drazin_transport_stable_on_bulk {S : CausalSplit V}
    (D : DrazinProjectorData S)
    (hNbulk : IsBulkStable S D.N) :
    ∀ x, x ∈ S.bulk → D.P (D.N x) ∈ S.bulk := by
  intro x hx
  have hNx : D.N x ∈ S.bulk := hNbulk x hx
  have hPx : D.P (D.N x) = D.N x := D.hBulkFix (D.N x) hNx
  simpa [hPx] using hNx

/-- The Moore–Penrose lift is a right-inverse to the boundary projector on lifted states. -/
theorem moore_penrose_boundary_lift {S : CausalSplit V}
    (M : MoorePenroseBoundaryLift S) (b : S.boundary) :
    M.proj (M.lift b) = (b : V) :=
  M.proj_on_lift b

/-- Reduced transport by projector sandwich on the physical sector. -/
def reducedTransport (P T : Module.End ℝ V) : Module.End ℝ V := P * T * P

/-- On projected states, reduced transport acts by projected transport. -/
theorem tomita_reduced_on_physical_sector (P T : Module.End ℝ V)
    (hP : IsProjector P) (x : V) :
    reducedTransport P T (P x) = P (T (P x)) := by
  have hPx : P (P x) = P x := by
    simpa [IsProjector, Module.End.mul_eq_comp, LinearMap.comp_apply] using
      congrArg (fun f : Module.End ℝ V => f x) hP
  simp [reducedTransport, Module.End.mul_eq_comp, LinearMap.comp_apply, hPx]

section StandardSubspaceBridge

open InfoGeometry.Canonical.RealTomitaStandardSubspace

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On the physical standard-subspace domain, the identity is the canonical projector. -/
def standardPhysicalProjector (K : Submodule ℝ H) :
    Module.End ℝ ↥(K ⊔ ImaginarySubmodule (H := H) K) :=
  (1 : Module.End ℝ ↥(K ⊔ ImaginarySubmodule (H := H) K))

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma standardPhysicalProjector_isProjector (K : Submodule ℝ H) :
    IsProjector (standardPhysicalProjector (H := H) K) := by
  simp [standardPhysicalProjector, IsProjector]

/-- Reduced transport with the canonical physical projector equals the Tomita transport itself. -/
lemma reduced_tomita_on_standard_eq_tomita
    (K : Submodule ℝ H) (hK : IsStandardSubspace (H := H) K) :
    reducedTransport (standardPhysicalProjector (H := H) K) (TomitaOnStandard (H := H) K hK)
      = TomitaOnStandard (H := H) K hK := by
  ext z
  simp [reducedTransport, standardPhysicalProjector]

/-- On the standard physical sector, reduced Tomita transport is involutive. -/
lemma reduced_tomita_on_standard_involutive
    (K : Submodule ℝ H) (hK : IsStandardSubspace (H := H) K)
    (z : ↥(K ⊔ ImaginarySubmodule (H := H) K)) :
    reducedTransport (standardPhysicalProjector (H := H) K) (TomitaOnStandard (H := H) K hK)
      (reducedTransport (standardPhysicalProjector (H := H) K) (TomitaOnStandard (H := H) K hK) z) = z := by
  simpa [reduced_tomita_on_standard_eq_tomita (H := H) K hK] using
    tomitaOnStandard_involutive (H := H) K hK z

end StandardSubspaceBridge

end InfoGeometry.Canonical.CausalConeProjectorBridge
