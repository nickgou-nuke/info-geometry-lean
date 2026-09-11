import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesStokesLift

namespace InfoGeometry.Canonical

open CategoryTheory

noncomputable section

def hestenesStokesFlowTopCatHom
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    TopCat.of HestenesStokesCarrier ⟶ TopCat.of HestenesStokesCarrier :=
  TopCat.ofHom
    (hestenesStokesFlowContinuousMap K I hK hI hKI hK_cont hI_cont p)

def hestenesStokesFlowInverseTopCatHom
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    TopCat.of HestenesStokesCarrier ⟶ TopCat.of HestenesStokesCarrier :=
  TopCat.ofHom
    (hestenesStokesFlowInverseContinuousMap K I hK hI hKI hK_cont hI_cont p)

@[simp] theorem hestenesStokesFlowTopCatHom_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ)
    (q : HestenesStokesCarrier) :
    hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont p q =
      hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p q := rfl

theorem hestenesStokesFlowTopCatHom_comp_inverse
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont p ≫
        hestenesStokesFlowInverseTopCatHom K I hK hI hKI hK_cont hI_cont p =
      𝟙 (TopCat.of HestenesStokesCarrier) := by
  apply TopCat.hom_ext
  simpa [hestenesStokesFlowTopCatHom, hestenesStokesFlowInverseTopCatHom] using
    hestenesStokesFlowInverseContinuousMap_comp K I hK hI hKI hK_cont hI_cont p

theorem hestenesStokesFlowInverseTopCatHom_comp
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    hestenesStokesFlowInverseTopCatHom K I hK hI hKI hK_cont hI_cont p ≫
        hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont p =
      𝟙 (TopCat.of HestenesStokesCarrier) := by
  apply TopCat.hom_ext
  simpa [hestenesStokesFlowTopCatHom, hestenesStokesFlowInverseTopCatHom] using
    hestenesStokesFlowContinuousMap_comp_inverse K I hK hI hKI hK_cont hI_cont p

theorem hestenesStokesFlowTopCatHom_isIso
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    IsIso (hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont p) := by
  refine IsIso.mk ⟨hestenesStokesFlowInverseTopCatHom K I hK hI hKI
    hK_cont hI_cont p, ?_, ?_⟩
  · exact hestenesStokesFlowTopCatHom_comp_inverse K I hK hI hKI
      hK_cont hI_cont p
  · exact hestenesStokesFlowInverseTopCatHom_comp K I hK hI hKI
      hK_cont hI_cont p

theorem hestenesStokesFlowTopCatHom_zero
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) :
    hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont (0, 0) =
      𝟙 (TopCat.of HestenesStokesCarrier) := by
  apply ConcreteCategory.hom_ext
  intro q
  change hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (0, 0) q = q
  exact congrArg (fun f : HestenesStokesCarrier ≃ₜ HestenesStokesCarrier => f q)
    (hestenesStokesFlow_zero K I hK hI hKI hK_cont hI_cont)

theorem hestenesStokesFlowTopCatHom_comp
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (p q : ℝ × ℝ) :
    hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont p ≫
        hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont q =
      hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont (q + p) := by
  apply ConcreteCategory.hom_ext
  intro x
  change (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont q)
      ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p) x) = _
  exact congrArg (fun f : HestenesStokesCarrier ≃ₜ HestenesStokesCarrier => f x)
    (hestenesStokesFlow_trans K I hK hI hKI hK_cont hI_cont p q)

def hestenesStokesFlowTopCatIso
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    TopCat.of HestenesStokesCarrier ≅ TopCat.of HestenesStokesCarrier :=
  { hom := hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont p
    inv := hestenesStokesFlowInverseTopCatHom K I hK hI hKI hK_cont hI_cont p
    hom_inv_id := hestenesStokesFlowTopCatHom_comp_inverse K I hK hI hKI
      hK_cont hI_cont p
    inv_hom_id := hestenesStokesFlowInverseTopCatHom_comp K I hK hI hKI
      hK_cont hI_cont p }

theorem hestenesStokesFlowTopCatIso_hom_isIso
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    IsIso ((hestenesStokesFlowTopCatIso K I hK hI hKI hK_cont hI_cont p).hom) :=
  (hestenesStokesFlowTopCatIso K I hK hI hKI hK_cont hI_cont p).isIso_hom

theorem hestenesStokesFlowTopCatIso_symm
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    (hestenesStokesFlowTopCatIso K I hK hI hKI hK_cont hI_cont p).symm =
      hestenesStokesFlowTopCatIso K I hK hI hKI hK_cont hI_cont
        (-p.1, -p.2) := by
  apply Iso.ext
  apply ConcreteCategory.hom_ext
  intro q
  change (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm q = _
  change (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm q =
    hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2) q
  have hfg := congrArg
    (fun f : HestenesStokesCarrier ≃ₜ HestenesStokesCarrier => f q)
    (hestenesStokesFlow_neg_trans K I hK hI hKI hK_cont hI_cont p)
  simp only [Homeomorph.trans_apply, Homeomorph.refl_apply] at hfg
  change (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p)
      ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2)) q) = q at hfg
  calc
    (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm q =
        (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm
          ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p)
            (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2) q)) := by
              rw [hfg]
    _ = hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2) q := by
      exact (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).left_inv _

theorem hestenesStokesFlowInverseTopCatHom_eq_neg
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [AddCommGroup HestenesStokesCarrier]
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    hestenesStokesFlowInverseTopCatHom K I hK hI hKI hK_cont hI_cont p =
      hestenesStokesFlowTopCatHom K I hK hI hKI hK_cont hI_cont
        (-p.1, -p.2) := by
  apply ConcreteCategory.hom_ext
  intro q
  change (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm q =
    hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2) q
  have hfg := congrArg
    (fun f : HestenesStokesCarrier ≃ₜ HestenesStokesCarrier => f q)
    (hestenesStokesFlow_neg_trans K I hK hI hKI hK_cont hI_cont p)
  simp only [Homeomorph.trans_apply, Homeomorph.refl_apply] at hfg
  change (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p)
      ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2)) q) = q at hfg
  calc
    (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm q =
        (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm
          ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p)
            (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2) q)) := by
              rw [hfg]
    _ = hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2) q := by
      exact (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).left_inv _

end

end InfoGeometry.Canonical
