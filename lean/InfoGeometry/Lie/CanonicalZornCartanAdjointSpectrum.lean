import InfoGeometry.Lie.CanonicalZornCartanAdjointAction
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Generic joint eigenspaces for the native Cartan adjoint action

This owner supplies only the intrinsic joint-eigenspace calculus for the
already constructed native Cartan plane.  Concrete finite-dimensional
spectrum computations live in the downstream root-decomposition owner.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum

open InfoGeometry.Lie.CanonicalZornCartanAdjointAction
open InfoGeometry.Lie.SplitOctonionAxialCartanDerivation
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev Der := CanonicalZornCartanAdjointAction.Der
abbrev Weight := TracelessWeight →ₗ[ℝ] ℝ

noncomputable def cartanBasis : Fin 2 → TracelessWeight :=
  fun i => tracelessWeightEquiv (Pi.single i (1 : ℝ))

theorem cartanBasis_linearIndependent :
    LinearIndependent ℝ cartanBasis := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h' := congrArg (fun x : TracelessWeight => x.1 1) h
    simp [cartanBasis, tracelessWeightEquiv] at h'
  · intro a h
    have h' := congrArg (fun x : TracelessWeight => x.1 1) h
    have h'' := congrArg (fun x : TracelessWeight => x.1 0) h
    simp [cartanBasis, tracelessWeightEquiv] at h' h''

def jointEigenspace (α : Weight) : Submodule ℝ Der where
  carrier := {D : Der | ∀ k, adCartan k D = α k • D}
  zero_mem' := by
    intro k
    rw [map_zero, smul_zero]
  add_mem' := by
    intro D E hD hE k
    rw [map_add, hD k, hE k, smul_add]
  smul_mem' := by
    intro r D hD k
    rw [LinearMap.map_smul, hD k, smul_comm]

@[simp] theorem mem_jointEigenspace_iff (α : Weight) (D : Der) :
    D ∈ jointEigenspace α ↔
      ∀ k, adCartan k D = α k • D := Iff.rfl

theorem jointEigenspace_disjoint_of_ne (α β : Weight) (hαβ : α ≠ β) :
    jointEigenspace α ⊓ jointEigenspace β = ⊥ := by
  rw [← disjoint_iff, Submodule.disjoint_def]
  intro D hα hβ
  obtain ⟨k, hk⟩ : ∃ k, α k ≠ β k := by
    contrapose! hαβ
    ext k
    exact hαβ k
  have hEq : α k • D = β k • D := by
    rw [← hα k, ← hβ k]
  have hsmul : (α k - β k) • D = 0 := by
    rw [sub_smul, hEq, sub_self]
  exact (smul_eq_zero.mp hsmul).resolve_left (sub_ne_zero.mpr hk)

theorem cartan_mem_jointEigenspace_zero (k : TracelessWeight) :
    (axialCartanLieEquiv k : Der) ∈ jointEigenspace 0 := by
  intro l
  change ⁅(axialCartanLieEquiv l : Der), (axialCartanLieEquiv k : Der)⁆ =
    (0 : ℝ) • (axialCartanLieEquiv k : Der)
  rw [zero_smul]
  have h := axialCartanDerivationLinear_lie_bracket_zero l k
  simpa only [axialCartanLieEquiv_apply] using h

theorem cartanBasis_mem_jointEigenspace_zero (i : Fin 2) :
    (axialCartanLieEquiv (cartanBasis i) : Der) ∈ jointEigenspace 0 :=
  cartan_mem_jointEigenspace_zero (cartanBasis i)

theorem lie_mem_jointEigenspace_add
    (α β : Weight) {X Y : Der}
    (hX : X ∈ jointEigenspace α) (hY : Y ∈ jointEigenspace β) :
    ⁅X, Y⁆ ∈ jointEigenspace (α + β) := by
  intro k
  rw [adCartan_apply, leibniz_lie]
  have h1 : ⁅axialCartanLieEquiv k, X⁆ = α k • X := by
    rw [← adCartan_apply]
    exact hX k
  have h2 : ⁅axialCartanLieEquiv k, Y⁆ = β k • Y := by
    rw [← adCartan_apply]
    exact hY k
  rw [h1, h2, smul_lie, lie_smul, ← add_smul]
  rfl

end InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
