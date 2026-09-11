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

local instance : Module ℝ Der :=
  LieSubalgebra.instModuleSubtypeMemOfIsScalarTower
    ℝ (CanonicalZornDerivation.EndCZ) Der

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
  carrier := {D : Der | ∀ k, adCartan k D = (SMul.smul (α k) D : Der)}
  zero_mem' := by
    intro k
    rw [map_zero]
    exact (Module.toDistribMulAction.smul_zero (α k)).symm
  add_mem' := by
    intro D E hD hE k
    rw [map_add, hD k, hE k]
    exact (Module.toDistribMulAction.smul_add (α k) D E).symm
  smul_mem' := by
    intro r D hD k
    change adCartan k (SMul.smul r D) =
      (SMul.smul (α k) (SMul.smul r D) : Der)
    calc
      adCartan k (SMul.smul r D) =
          SMul.smul r (adCartan k D) := (adCartan k).map_smul r D
      _ = SMul.smul r (SMul.smul (α k) D) := congrArg (SMul.smul r) (hD k)
      _ = SMul.smul (α k) (SMul.smul r D) := by
        exact smul_comm r (α k) D

@[simp] theorem mem_jointEigenspace_iff (α : Weight) (D : Der) :
    D ∈ jointEigenspace α ↔
      ∀ k, adCartan k D = (SMul.smul (α k) D : Der) := Iff.rfl

theorem jointEigenspace_disjoint_of_ne (α β : Weight) (hαβ : α ≠ β) :
    jointEigenspace α ⊓ jointEigenspace β = ⊥ := by
  rw [← disjoint_iff, Submodule.disjoint_def]
  intro D hα hβ
  obtain ⟨k, hk⟩ : ∃ k, α k ≠ β k := by
    by_contra h
    push_neg at h
    apply hαβ
    ext k
    exact h k
  have hEq :
      (Module.toDistribMulAction.smul (α k) D : Der) =
        Module.toDistribMulAction.smul (β k) D := by
    calc
      Module.toDistribMulAction.smul (α k) D = adCartan k D := (hα k).symm
      _ = Module.toDistribMulAction.smul (β k) D := hβ k
  have hsmul :
      (Module.toDistribMulAction.smul (α k - β k) D : Der) = 0 := by
    calc
      Module.toDistribMulAction.smul (α k - β k) D =
          Module.toDistribMulAction.smul (α k) D -
            Module.toDistribMulAction.smul (β k) D := by
        exact sub_smul _ _ _
      _ = 0 := by rw [hEq, sub_self]
  exact (smul_eq_zero.mp hsmul).resolve_left (sub_ne_zero.mpr hk)

theorem cartan_mem_jointEigenspace_zero (k : TracelessWeight) :
    (axialCartanLieEquiv k : Der) ∈ jointEigenspace 0 := by
  intro l
  change adCartan l (axialCartanLieEquiv k : Der) =
    (SMul.smul (0 : ℝ) (axialCartanLieEquiv k : Der) : Der)
  change ⁅(axialCartanLieEquiv l : Der), (axialCartanLieEquiv k : Der)⁆ = _
  have h := axialCartanDerivationLinear_lie_bracket_zero l k
  have hz : (SMul.smul (0 : ℝ) (axialCartanLieEquiv k : Der) : Der) = 0 :=
    Module.zero_smul _
  rw [hz]
  simpa only [axialCartanLieEquiv_apply] using h

theorem cartanBasis_mem_jointEigenspace_zero (i : Fin 2) :
    (axialCartanLieEquiv (cartanBasis i) : Der) ∈ jointEigenspace 0 := by
  exact cartan_mem_jointEigenspace_zero (cartanBasis i)

theorem lie_mem_jointEigenspace_add
    (α β : Weight) {X Y : Der}
    (hX : X ∈ jointEigenspace α) (hY : Y ∈ jointEigenspace β) :
    ⁅X, Y⁆ ∈ jointEigenspace (α + β) := by
  change ∀ k, adCartan k ⁅X, Y⁆ =
    (SMul.smul ((α + β) k) ⁅X, Y⁆ : Der)
  change (∀ k, adCartan k X = (SMul.smul (α k) X : Der)) at hX
  change (∀ k, adCartan k Y = (SMul.smul (β k) Y : Der)) at hY
  intro k
  change ⁅(axialCartanLieEquiv k : Der), ⁅X, Y⁆⁆ = _
  have hX' : ⁅(axialCartanLieEquiv k : Der), X⁆ =
      (SMul.smul (α k) X : Der) := by
    simpa only [adCartan_apply] using hX k
  have hY' : ⁅(axialCartanLieEquiv k : Der), Y⁆ =
      (SMul.smul (β k) Y : Der) := by
    simpa only [adCartan_apply] using hY k
  rw [leibniz_lie]
  rw [hX', hY']
  apply Subtype.ext
  change ⁅(α k) • (X : CanonicalZornDerivation.EndCZ),
      (Y : CanonicalZornDerivation.EndCZ)⁆ +
      ⁅(X : CanonicalZornDerivation.EndCZ),
        (β k) • (Y : CanonicalZornDerivation.EndCZ)⁆ =
      (α k + β k) • ⁅(X : CanonicalZornDerivation.EndCZ),
        (Y : CanonicalZornDerivation.EndCZ)⁆
  rw [smul_lie, lie_smul]
  exact (add_smul (α k) (β k) ⁅(X : CanonicalZornDerivation.EndCZ),
    (Y : CanonicalZornDerivation.EndCZ)⁆).symm

end InfoGeometry.Lie.CanonicalZornCartanAdjointSpectrum
