import InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Restricted chiral representations of the native `Spin(5,5)` matrix action

The preceding owners prove that the matrix action of `Spin(5,5)` preserves the
two chiral projector sectors.  This file packages that fact as genuine monoid
homomorphisms on the two submodules.  It makes no claim about a Spin-to-SO
kernel, a double cover, or an identification with an independently defined
chiral carrier.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinGroupRestrictedChiralRepresentation

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinGroupChiralSectorBridge
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep

private theorem chiralPlusProjector_mem_projection_vector (ψ : SpinorSpace 5) :
    Matrix.mulVec chiralPlusProjector (Matrix.mulVec chiralPlusProjector ψ) =
      Matrix.mulVec chiralPlusProjector ψ := by
  rw [Matrix.mulVec_mulVec, chiralPlusProjector_idempotent]

private theorem chiralMinusProjector_mem_projection_vector (ψ : SpinorSpace 5) :
    Matrix.mulVec chiralMinusProjector (Matrix.mulVec chiralMinusProjector ψ) =
      Matrix.mulVec chiralMinusProjector ψ := by
  rw [Matrix.mulVec_mulVec, chiralMinusProjector_idempotent]

private def restrictMatrixAction
    (S : Submodule ℝ (SpinorSpace 5))
    (A : SpinorMatrix 5)
    (hA : ∀ v : SpinorSpace 5, v ∈ S → Matrix.mulVec A v ∈ S) :
    Module.End ℝ S :=
  { toFun := fun v => ⟨Matrix.mulVec A v.1, hA v.1 v.2⟩
    map_add' := by
      intro v w
      apply Subtype.ext
      simp [Matrix.mulVec_add]
    map_smul' := by
      intro a v
      apply Subtype.ext
      simp [Matrix.mulVec_smul] }

@[simp] private theorem restrictMatrixAction_apply
    (S : Submodule ℝ (SpinorSpace 5))
    (A : SpinorMatrix 5)
    (hA : ∀ v : SpinorSpace 5, v ∈ S → Matrix.mulVec A v ∈ S)
    (v : S) :
    restrictMatrixAction S A hA v =
      ⟨Matrix.mulVec A v.1, hA v.1 v.2⟩ := rfl

noncomputable def chiralPlusRepresentation :
    Spin55 →* Module.End ℝ chiralPlusSector where
  toFun g :=
    restrictMatrixAction chiralPlusSector
      (cl55SpinorAlgEquiv (g : Cl55))
      (fun v hv => spinGroup_matrix_maps_chiralPlusSector g hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [restrictMatrixAction, Matrix.one_mulVec]
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change Matrix.mulVec
        (cl55SpinorAlgEquiv ((g * h : Spin55) : Cl55)) v.1 =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
        (Matrix.mulVec (cl55SpinorAlgEquiv (h : Cl55)) v.1)
    rw [Matrix.mulVec_mulVec]
    rw [show cl55SpinorAlgEquiv ((g * h : Spin55) : Cl55) =
        cl55SpinorAlgEquiv (g : Cl55) * cl55SpinorAlgEquiv (h : Cl55) by
      change cl55SpinorAlgEquiv ((g : Cl55) * (h : Cl55)) = _
      exact map_mul cl55SpinorAlgEquiv (g : Cl55) (h : Cl55)]

noncomputable def chiralMinusRepresentation :
    Spin55 →* Module.End ℝ chiralMinusSector where
  toFun g :=
    restrictMatrixAction chiralMinusSector
      (cl55SpinorAlgEquiv (g : Cl55))
      (fun v hv => spinGroup_matrix_maps_chiralMinusSector g hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simp [restrictMatrixAction, Matrix.one_mulVec]
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change Matrix.mulVec
        (cl55SpinorAlgEquiv ((g * h : Spin55) : Cl55)) v.1 =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
        (Matrix.mulVec (cl55SpinorAlgEquiv (h : Cl55)) v.1)
    rw [Matrix.mulVec_mulVec]
    rw [show cl55SpinorAlgEquiv ((g * h : Spin55) : Cl55) =
        cl55SpinorAlgEquiv (g : Cl55) * cl55SpinorAlgEquiv (h : Cl55) by
      change cl55SpinorAlgEquiv ((g : Cl55) * (h : Cl55)) = _
      exact map_mul cl55SpinorAlgEquiv (g : Cl55) (h : Cl55)]

@[simp] theorem chiralPlusRepresentation_val (g : Spin55) (v : chiralPlusSector) :
    chiralPlusRepresentation g v =
      ⟨Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v.1,
        spinGroup_matrix_maps_chiralPlusSector g v.2⟩ := rfl

@[simp] theorem chiralPlusRepresentation_coe (g : Spin55) (v : chiralPlusSector) :
    (chiralPlusRepresentation g v).1 =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v.1 := by
  rfl

@[simp] theorem chiralMinusRepresentation_val (g : Spin55) (v : chiralMinusSector) :
    chiralMinusRepresentation g v =
      ⟨Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v.1,
        spinGroup_matrix_maps_chiralMinusSector g v.2⟩ := rfl

@[simp] theorem chiralMinusRepresentation_coe (g : Spin55) (v : chiralMinusSector) :
    (chiralMinusRepresentation g v).1 =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v.1 := by
  rfl

theorem chiralRepresentations_block_readout
    (g : Spin55) (ψ : SpinorSpace 5) :
    Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) ψ =
      (chiralPlusRepresentation g
        ⟨Matrix.mulVec chiralPlusProjector ψ, chiralPlusProjector_mem_projection_vector ψ⟩).1 +
      (chiralMinusRepresentation g
        ⟨Matrix.mulVec chiralMinusProjector ψ, chiralMinusProjector_mem_projection_vector ψ⟩).1 := by
  change Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) ψ =
    Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
        (Matrix.mulVec chiralPlusProjector ψ) +
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
        (Matrix.mulVec chiralMinusProjector ψ)
  rw [← Matrix.mulVec_add]
  congr 1
  calc
    ψ = Matrix.mulVec (1 : SpinorMatrix 5) ψ := (Matrix.one_mulVec ψ).symm
    _ = Matrix.mulVec (chiralPlusProjector + chiralMinusProjector) ψ := by
      rw [chiralProjectors_complementary]
    _ = Matrix.mulVec chiralPlusProjector ψ +
        Matrix.mulVec chiralMinusProjector ψ := by
      rw [Matrix.add_mulVec]

theorem chiralRepresentations_block_decomp_apply
    (g : Spin55) (ψ : SpinorSpace 5) :
    let e := chiralPlusSector.prodEquivOfIsCompl chiralMinusSector chiralSectors_isCompl
    e.symm (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) ψ) =
      (chiralPlusRepresentation g
        ⟨Matrix.mulVec chiralPlusProjector ψ,
          chiralPlusProjector_mem_projection_vector ψ⟩,
        chiralMinusRepresentation g
          ⟨Matrix.mulVec chiralMinusProjector ψ,
            chiralMinusProjector_mem_projection_vector ψ⟩) := by
  intro e
  refine e.toEquiv.injective ?_
  change e (e.symm (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) ψ)) =
      e ((chiralPlusRepresentation g
        ⟨Matrix.mulVec chiralPlusProjector ψ,
          chiralPlusProjector_mem_projection_vector ψ⟩,
        chiralMinusRepresentation g
          ⟨Matrix.mulVec chiralMinusProjector ψ,
            chiralMinusProjector_mem_projection_vector ψ⟩))
  rw [e.apply_symm_apply]
  rw [Submodule.coe_prodEquivOfIsCompl']
  change Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) ψ =
    (chiralPlusRepresentation g
      ⟨Matrix.mulVec chiralPlusProjector ψ, chiralPlusProjector_mem_projection_vector ψ⟩).1 +
    (chiralMinusRepresentation g
      ⟨Matrix.mulVec chiralMinusProjector ψ, chiralMinusProjector_mem_projection_vector ψ⟩).1
  rw [chiralPlusRepresentation_coe, chiralMinusRepresentation_coe]
  simpa [Matrix.mulVec_mulVec] using (chiralRepresentations_block_readout (g := g) ψ)

theorem chiralRepresentations_block_diagonality
    (g : Spin55) (vplus : chiralPlusSector) (vminus : chiralMinusSector) :
    let e := chiralPlusSector.prodEquivOfIsCompl chiralMinusSector chiralSectors_isCompl
    e.symm (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus)) ) =
      (chiralPlusRepresentation g vplus, chiralMinusRepresentation g vminus) := by
  intro e
  have hvplus : chiralPlus (vplus : SpinorSpace 5) := by
    exact (chiralPlus_iff_projector_fixed (vplus : SpinorSpace 5)).2 vplus.2
  have hvminus : chiralMinus (vminus : SpinorSpace 5) := by
    exact (chiralMinus_iff_projector_fixed (vminus : SpinorSpace 5)).2 vminus.2
  have hproj_plus : Matrix.mulVec chiralPlusProjector (e (vplus, vminus)) =
      (vplus : SpinorSpace 5) := by
    calc
      Matrix.mulVec chiralPlusProjector (e (vplus, vminus))
          = Matrix.mulVec chiralPlusProjector ((vplus : SpinorSpace 5) + (vminus : SpinorSpace 5)) := by
            simp [e, Submodule.coe_prodEquivOfIsCompl']
      _ = Matrix.mulVec chiralPlusProjector (vplus : SpinorSpace 5) +
          Matrix.mulVec chiralPlusProjector (vminus : SpinorSpace 5) := by
            simp [Matrix.mulVec_add]
      _ = (vplus : SpinorSpace 5) := by
            rw [← matrixApply_eq_mulVec, ← matrixApply_eq_mulVec,
              chiralPlusProjector_apply_of_chiralPlus (vplus : SpinorSpace 5) hvplus,
              chiralPlusProjector_apply_of_chiralMinus (vminus : SpinorSpace 5) hvminus]
            simp
  have hproj_minus : Matrix.mulVec chiralMinusProjector (e (vplus, vminus)) =
      (vminus : SpinorSpace 5) := by
    calc
      Matrix.mulVec chiralMinusProjector (e (vplus, vminus))
          = Matrix.mulVec chiralMinusProjector ((vplus : SpinorSpace 5) + (vminus : SpinorSpace 5)) := by
            simp [e, Submodule.coe_prodEquivOfIsCompl']
      _ = Matrix.mulVec chiralMinusProjector (vplus : SpinorSpace 5) +
          Matrix.mulVec chiralMinusProjector (vminus : SpinorSpace 5) := by
            simp [Matrix.mulVec_add]
      _ = (vminus : SpinorSpace 5) := by
            rw [← matrixApply_eq_mulVec, ← matrixApply_eq_mulVec,
              chiralMinusProjector_apply_of_chiralPlus (vplus : SpinorSpace 5) hvplus,
              chiralMinusProjector_apply_of_chiralMinus (vminus : SpinorSpace 5) hvminus]
            simp
  have hdecomp :
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus)) =
        (chiralPlusRepresentation g vplus).1 + (chiralMinusRepresentation g vminus).1 := by
    calc
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus))
          = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
              (Matrix.mulVec chiralPlusProjector (e (vplus, vminus))) +
            Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
              (Matrix.mulVec chiralMinusProjector (e (vplus, vminus))) := by
            simpa [Matrix.add_mulVec] using
              (chiralRepresentations_block_readout (g := g) (ψ := e (vplus, vminus)))
      _ = (chiralPlusRepresentation g vplus).1 + (chiralMinusRepresentation g vminus).1 := by
            rw [hproj_plus, hproj_minus, chiralPlusRepresentation_coe, chiralMinusRepresentation_coe]
  let x : SpinorSpace 5 :=
    Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus))
  have h1 : e (e.symm x) = x := by
    simp
  have h2 : x = e (chiralPlusRepresentation g vplus, chiralMinusRepresentation g vminus) := by
    unfold x
    calc
      x = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus)) := rfl
      _ = (chiralPlusRepresentation g vplus).1 + (chiralMinusRepresentation g vminus).1 := hdecomp
      _ = e (chiralPlusRepresentation g vplus, chiralMinusRepresentation g vminus) := by
            simp [Submodule.coe_prodEquivOfIsCompl', e]
  exact e.injective (h1.trans h2)

/-- Block reconstruction in the full carrier: matrix action preserves the chiral splitting. -/
theorem chiralRepresentations_block_action
    (g : Spin55) (vplus : chiralPlusSector) (vminus : chiralMinusSector) :
    let e := chiralPlusSector.prodEquivOfIsCompl chiralMinusSector chiralSectors_isCompl
    Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus)) =
      e (chiralPlusRepresentation g vplus, chiralMinusRepresentation g vminus) := by
  intro e
  have hvplus : chiralPlus (vplus : SpinorSpace 5) := by
    exact (chiralPlus_iff_projector_fixed (vplus : SpinorSpace 5)).2 vplus.2
  have hvminus : chiralMinus (vminus : SpinorSpace 5) := by
    exact (chiralMinus_iff_projector_fixed (vminus : SpinorSpace 5)).2 vminus.2
  have hplus :
      Matrix.mulVec chiralPlusProjector (e (vplus, vminus)) =
        (vplus : SpinorSpace 5) := by
    calc
      Matrix.mulVec chiralPlusProjector (e (vplus, vminus))
          = Matrix.mulVec chiralPlusProjector ((vplus : SpinorSpace 5) + (vminus : SpinorSpace 5)) := by
            simp [e, Submodule.coe_prodEquivOfIsCompl']
      _ = Matrix.mulVec chiralPlusProjector (vplus : SpinorSpace 5) +
          Matrix.mulVec chiralPlusProjector (vminus : SpinorSpace 5) := by
            rw [Matrix.mulVec_add]
      _ = (vplus : SpinorSpace 5) := by
            rw [← matrixApply_eq_mulVec, ← matrixApply_eq_mulVec,
              chiralPlusProjector_apply_of_chiralPlus (vplus : SpinorSpace 5) hvplus,
              chiralPlusProjector_apply_of_chiralMinus (vminus : SpinorSpace 5) hvminus]
            simp
  have hminus :
      Matrix.mulVec chiralMinusProjector (e (vplus, vminus)) =
        (vminus : SpinorSpace 5) := by
    calc
      Matrix.mulVec chiralMinusProjector (e (vplus, vminus))
          = Matrix.mulVec chiralMinusProjector ((vplus : SpinorSpace 5) + (vminus : SpinorSpace 5)) := by
            simp [e, Submodule.coe_prodEquivOfIsCompl']
      _ = Matrix.mulVec chiralMinusProjector (vplus : SpinorSpace 5) +
          Matrix.mulVec chiralMinusProjector (vminus : SpinorSpace 5) := by
            rw [Matrix.mulVec_add]
      _ = (vminus : SpinorSpace 5) := by
            rw [← matrixApply_eq_mulVec, ← matrixApply_eq_mulVec,
              chiralMinusProjector_apply_of_chiralPlus (vplus : SpinorSpace 5) hvplus,
              chiralMinusProjector_apply_of_chiralMinus (vminus : SpinorSpace 5) hvminus]
            simp
  have hdecomp :
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus))
        = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
          (Matrix.mulVec chiralPlusProjector (e (vplus, vminus))) +
          Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
            (Matrix.mulVec chiralMinusProjector (e (vplus, vminus))) := by
    simpa [Matrix.mulVec_add] using
      (chiralRepresentations_block_readout (g := g) (ψ := e (vplus, vminus)))
  have hblock :
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus))
        = (chiralPlusRepresentation g vplus).1 + (chiralMinusRepresentation g vminus).1 := by
    calc
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (e (vplus, vminus))
          = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
            (Matrix.mulVec chiralPlusProjector (e (vplus, vminus))) +
            Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55))
              (Matrix.mulVec chiralMinusProjector (e (vplus, vminus))) := hdecomp
      _ = (chiralPlusRepresentation g vplus).1 + (chiralMinusRepresentation g vminus).1 := by
            rw [hplus, hminus, chiralPlusRepresentation_coe, chiralMinusRepresentation_coe]
  simpa [Submodule.coe_prodEquivOfIsCompl', e] using hblock

theorem chiralPlusRepresentation_action_injective (g : Spin55) :
    Function.Injective (chiralPlusRepresentation g) := by
  intro v w h
  have h' := congrArg (chiralPlusRepresentation g⁻¹) h
  change (chiralPlusRepresentation g⁻¹ * chiralPlusRepresentation g) v =
    (chiralPlusRepresentation g⁻¹ * chiralPlusRepresentation g) w at h'
  simpa only [← map_mul, inv_mul_cancel, map_one] using h'

theorem chiralMinusRepresentation_action_injective (g : Spin55) :
    Function.Injective (chiralMinusRepresentation g) := by
  intro v w h
  have h' := congrArg (chiralMinusRepresentation g⁻¹) h
  change (chiralMinusRepresentation g⁻¹ * chiralMinusRepresentation g) v =
    (chiralMinusRepresentation g⁻¹ * chiralMinusRepresentation g) w at h'
  simpa only [← map_mul, inv_mul_cancel, map_one] using h'



end InfoGeometry.Clifford.Cl55SpinGroupRestrictedChiralRepresentation
