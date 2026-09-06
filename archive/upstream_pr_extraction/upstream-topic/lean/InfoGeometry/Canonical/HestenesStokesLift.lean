import InfoGeometry.Canonical.HestenesLoxodromicRotorTopological
import InfoGeometry.Canonical.HestenesMirrorLoxodromic
import InfoGeometry.Canonical.HestenesRealMirrorTopological
import InfoGeometry.Canonical.TwoSheetStokesCoordinates

namespace InfoGeometry.Canonical

set_option maxHeartbeats 1000000

noncomputable section

abbrev HestenesStokesCarrier :=
  TwoSheetStokesCoordinates.StokesQuad

def hestenesStokesLift
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (η θ : ℝ) (q : HestenesStokesCarrier) : HestenesStokesCarrier :=
  realLoxodromicAction K I η θ q

theorem hestenesStokesLift_zero
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (q : HestenesStokesCarrier) :
    hestenesStokesLift K I 0 0 q = q := by
  exact realLoxodromicAction_zero K I q

theorem mirror_hestenesStokesLift
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (J : HestenesStokesCarrier ≃ₗ[ℝ] HestenesStokesCarrier)
    (hJK : ∀ v, J (K v) = -(K (J v)))
    (hJI : ∀ v, J (I v) = -(I (J v)))
    (η θ : ℝ) (q : HestenesStokesCarrier) :
    J (hestenesStokesLift K I η θ q) =
      hestenesStokesLift K I (-η) (-θ) (J q) := by
  exact mirror_realLoxodromicAction K I J hJK hJI η θ q

theorem continuous_mirror_hestenesStokesLift
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (J : HestenesStokesCarrier ≃ₗ[ℝ] HestenesStokesCarrier)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (hJ_cont : Continuous J) :
    Continuous (fun p : ℝ × ℝ × HestenesStokesCarrier =>
      J (hestenesStokesLift K I p.1 p.2.1 p.2.2)) := by
  exact hJ_cont.comp
    (continuous_realLoxodromicAction K I hK_cont hI_cont)

theorem hestenesStokesLift_inverse
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    (η θ : ℝ) (q : HestenesStokesCarrier) :
    hestenesStokesLift K I (-η) (-θ)
        (hestenesStokesLift K I η θ q) = q := by
  exact realLoxodromicAction_inverse K I hK hI hKI η θ q

theorem continuous_hestenesStokesLift
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) :
    Continuous (fun p : ℝ × ℝ × HestenesStokesCarrier =>
      hestenesStokesLift K I p.1 p.2.1 p.2.2) := by
  exact continuous_realLoxodromicAction K I hK_cont hI_cont

def hestenesStokesLiftContinuousMap
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) :
    C(ℝ × ℝ × HestenesStokesCarrier, HestenesStokesCarrier) :=
  { toFun := fun p => hestenesStokesLift K I p.1 p.2.1 p.2.2
    continuous_toFun := continuous_hestenesStokesLift K I hK_cont hI_cont }

@[simp] theorem hestenesStokesLiftContinuousMap_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (p : ℝ × ℝ × HestenesStokesCarrier) :
    hestenesStokesLiftContinuousMap K I hK_cont hI_cont p =
      hestenesStokesLift K I p.1 p.2.1 p.2.2 := rfl

set_option maxHeartbeats 5000000 in
def hestenesStokesLiftHomeomorph
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (η θ : ℝ) :
    HestenesStokesCarrier ≃ₜ HestenesStokesCarrier := by
  exact
    (realRotorHomeomorph I hI hI_cont θ).trans
      (realBoostHomeomorph K hK hK_cont η)

theorem hestenesStokesLiftHomeomorph_zero
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (q : HestenesStokesCarrier) :
    hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont 0 0 q = q := by
  exact hestenesStokesLift_zero K I q

theorem hestenesStokesLiftHomeomorph_symm
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (η θ : ℝ) :
    (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).symm =
      hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont
        (-η) (-θ) := by
  apply Homeomorph.ext
  intro q
  change realRotorAction I (-θ) (realBoostAction K (-η) q) =
    realBoostAction K (-η) (realRotorAction I (-θ) q)
  exact (realLoxodromicAction_commute K I hKI (-η) (-θ) q).symm

theorem hestenesStokesLiftHomeomorph_trans_symm
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (η θ : ℝ) :
    (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).trans
        (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).symm =
      Homeomorph.refl HestenesStokesCarrier := by
  apply Homeomorph.ext
  intro q
  simpa using
    (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).right_inv q

theorem hestenesStokesLiftHomeomorph_symm_trans
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (η θ : ℝ) :
    (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).symm.trans
        (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ) =
      Homeomorph.refl HestenesStokesCarrier := by
  apply Homeomorph.ext
  intro q
  simpa using
    (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).left_inv q

@[simp] theorem hestenesStokesLiftHomeomorph_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (η θ : ℝ) (q : HestenesStokesCarrier) :
    hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ q =
      hestenesStokesLift K I η θ q := rfl

@[simp] theorem hestenesStokesLiftHomeomorph_symm_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (η θ : ℝ) (q : HestenesStokesCarrier) :
    (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).symm q =
      hestenesStokesLift K I (-η) (-θ) q := by
  change realRotorAction I (-θ) (realBoostAction K (-η) q) =
    realBoostAction K (-η) (realRotorAction I (-θ) q)
  exact (realLoxodromicAction_commute K I hKI (-η) (-θ) q).symm

theorem hestenesStokesLiftHomeomorph_trans_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (η₁ θ₁ η₂ θ₂ : ℝ) (q : HestenesStokesCarrier) :
    (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η₁ θ₁).trans
        (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η₂ θ₂) q =
      hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont
        (η₂ + η₁) (θ₂ + θ₁) q := by
  change hestenesStokesLift K I η₂ θ₂
      (hestenesStokesLift K I η₁ θ₁ q) =
    hestenesStokesLift K I (η₂ + η₁) (θ₂ + θ₁) q
  exact realLoxodromicAction_add K I hK hI hKI η₂ θ₂ η₁ θ₁ q

theorem hestenesStokesLiftHomeomorph_trans
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (η₁ θ₁ η₂ θ₂ : ℝ) :
    (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η₁ θ₁).trans
        (hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η₂ θ₂) =
      hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont
        (η₂ + η₁) (θ₂ + θ₁) := by
  apply Homeomorph.ext
  intro q
  exact hestenesStokesLiftHomeomorph_trans_apply
    K I hK hI hKI hK_cont hI_cont η₁ θ₁ η₂ θ₂ q

theorem mirror_hestenesStokesLiftHomeomorph_conjugate_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (J : HestenesStokesCarrier ≃ₗ[ℝ] HestenesStokesCarrier)
    (hJ : IsRealMirror J)
    (hJK : ∀ v, J (K v) = -(K (J v)))
    (hJI : ∀ v, J (I v) = -(I (J v)))
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (hJ_cont : Continuous J) (η θ : ℝ) (q : HestenesStokesCarrier) :
    (realMirrorHomeomorph J hJ hJ_cont).trans
        ((hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).trans
          (realMirrorHomeomorph J hJ hJ_cont)) q =
      hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont
        (-η) (-θ) q := by
  change J (hestenesStokesLift K I η θ (J q)) =
    hestenesStokesLift K I (-η) (-θ) q
  rw [mirror_hestenesStokesLift K I J hJK hJI]
  rw [realMirror_is_involutive J hJ q]

theorem mirror_hestenesStokesLiftHomeomorph_conjugate
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (J : HestenesStokesCarrier ≃ₗ[ℝ] HestenesStokesCarrier)
    (hJ : IsRealMirror J)
    (hJK : ∀ v, J (K v) = -(K (J v)))
    (hJI : ∀ v, J (I v) = -(I (J v)))
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (hJ_cont : Continuous J) (η θ : ℝ) :
    (realMirrorHomeomorph J hJ hJ_cont).trans
        ((hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont η θ).trans
          (realMirrorHomeomorph J hJ hJ_cont)) =
      hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont
        (-η) (-θ) := by
  apply Homeomorph.ext
  intro q
  exact mirror_hestenesStokesLiftHomeomorph_conjugate_apply
    K I J hJ hJK hJI hK hI hKI hK_cont hI_cont hJ_cont η θ q

def hestenesStokesParameterAdd
    (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ :=
  (p.1.1 + p.2.1, p.1.2 + p.2.2)

theorem continuous_hestenesStokesParameterAdd :
    Continuous (hestenesStokesParameterAdd) := by
  exact (continuous_fst.fst.add continuous_snd.fst).prodMk
    (continuous_fst.snd.add continuous_snd.snd)

def hestenesStokesCompositionAction
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (p : (ℝ × ℝ) × (ℝ × ℝ)) (q : HestenesStokesCarrier) :
    HestenesStokesCarrier :=
  hestenesStokesLift K I (hestenesStokesParameterAdd p).1
    (hestenesStokesParameterAdd p).2 q

set_option maxHeartbeats 5000000 in
theorem continuous_hestenesStokesCompositionAction
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) :
    Continuous (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) × HestenesStokesCarrier =>
      hestenesStokesCompositionAction K I p.1 p.2) := by
  have hsum : Continuous (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) × HestenesStokesCarrier =>
      hestenesStokesParameterAdd p.1) :=
    continuous_hestenesStokesParameterAdd.comp continuous_fst
  have hparameterMap : Continuous (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) × HestenesStokesCarrier =>
      ((hestenesStokesParameterAdd p.1).1,
        (hestenesStokesParameterAdd p.1).2, p.2)) :=
    hsum.fst.prodMk (hsum.snd.prodMk continuous_snd)
  simpa only [hestenesStokesCompositionAction] using
    (continuous_realLoxodromicAction K I hK_cont hI_cont).comp hparameterMap

def hestenesStokesFlow
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (p : ℝ × ℝ) : HestenesStokesCarrier ≃ₜ HestenesStokesCarrier :=
  hestenesStokesLiftHomeomorph K I hK hI hKI hK_cont hI_cont p.1 p.2

theorem hestenesStokesFlow_zero
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) :
    hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (0, 0) =
      Homeomorph.refl HestenesStokesCarrier := by
  apply Homeomorph.ext
  intro q
  change hestenesStokesLift K I 0 0 q = q
  exact hestenesStokesLift_zero K I q

theorem hestenesStokesFlow_trans
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (p q : ℝ × ℝ) :
    (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).trans
        (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont q) =
      hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (q + p) := by
  exact hestenesStokesLiftHomeomorph_trans K I hK hI hKI hK_cont hI_cont
    p.1 p.2 q.1 q.2

theorem mirror_hestenesStokesFlow_conjugate
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (J : HestenesStokesCarrier ≃ₗ[ℝ] HestenesStokesCarrier)
    (hJ : IsRealMirror J)
    (hJK : ∀ v, J (K v) = -(K (J v)))
    (hJI : ∀ v, J (I v) = -(I (J v)))
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (hJ_cont : Continuous J) (p : ℝ × ℝ) :
    (realMirrorHomeomorph J hJ hJ_cont).trans
        ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).trans
          (realMirrorHomeomorph J hJ hJ_cont)) =
      hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2) := by
  exact mirror_hestenesStokesLiftHomeomorph_conjugate
    K I J hJ hJK hJI hK hI hKI hK_cont hI_cont hJ_cont p.1 p.2

theorem hestenesStokesFlow_trans_neg
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).trans
        (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2)) =
      Homeomorph.refl HestenesStokesCarrier := by
  rw [hestenesStokesFlow_trans K I hK hI hKI hK_cont hI_cont]
  have hp : (-p.1, -p.2) + p = (0, 0) := by
    ext <;> simp
  rw [hp]
  exact hestenesStokesFlow_zero K I hK hI hKI hK_cont hI_cont

theorem hestenesStokesFlow_neg_trans
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (-p.1, -p.2)).trans
        (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p) =
      Homeomorph.refl HestenesStokesCarrier := by
  rw [hestenesStokesFlow_trans K I hK hI hKI hK_cont hI_cont]
  have hp : p + (-p.1, -p.2) = (0, 0) := by
    ext <;> simp
  rw [hp]
  exact hestenesStokesFlow_zero K I hK hI hKI hK_cont hI_cont

theorem continuous_hestenesStokesFlow_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    Continuous (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p) :=
  (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).continuous

theorem continuous_hestenesStokesFlow_inverse_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    Continuous ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm) :=
  (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm.continuous

def hestenesStokesFlowContinuousMap
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    C(HestenesStokesCarrier, HestenesStokesCarrier) :=
  { toFun := hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p
    continuous_toFun :=
      continuous_hestenesStokesFlow_apply K I hK hI hKI hK_cont hI_cont p }

@[simp] theorem hestenesStokesFlowContinuousMap_apply
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ)
    (q : HestenesStokesCarrier) :
    hestenesStokesFlowContinuousMap K I hK hI hKI hK_cont hI_cont p q =
      hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p q := rfl

def hestenesStokesFlowInverseContinuousMap
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    C(HestenesStokesCarrier, HestenesStokesCarrier) :=
  { toFun := (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm
    continuous_toFun :=
      continuous_hestenesStokesFlow_inverse_apply K I hK hI hKI
        hK_cont hI_cont p }

theorem hestenesStokesFlowContinuousMap_comp
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I)
    (p q : ℝ × ℝ) :
    (hestenesStokesFlowContinuousMap K I hK hI hKI hK_cont hI_cont q).comp
        (hestenesStokesFlowContinuousMap K I hK hI hKI hK_cont hI_cont p) =
      hestenesStokesFlowContinuousMap K I hK hI hKI hK_cont hI_cont (q + p) := by
  apply ContinuousMap.ext
  intro x
  change
    (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont q)
        ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p) x) =
      (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont (q + p)) x
  exact congrArg (fun f : HestenesStokesCarrier ≃ₜ HestenesStokesCarrier => f x)
    (hestenesStokesFlow_trans K I hK hI hKI hK_cont hI_cont p q)

theorem hestenesStokesFlowContinuousMap_comp_inverse
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    (hestenesStokesFlowContinuousMap K I hK hI hKI hK_cont hI_cont p).comp
        (hestenesStokesFlowInverseContinuousMap K I hK hI hKI hK_cont hI_cont p) =
      ContinuousMap.id HestenesStokesCarrier := by
  apply ContinuousMap.ext
  intro q
  change
    (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p)
        ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm q) = q
  exact (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).right_inv q

theorem hestenesStokesFlowInverseContinuousMap_comp
    (K I : HestenesStokesCarrier →ₗ[ℝ] HestenesStokesCarrier)
    (hK : IsRealInvolution K)
    (hI : IsRealComplexStructure I)
    (hKI : K.comp I = I.comp K)
    [TopologicalSpace HestenesStokesCarrier]
    [IsTopologicalAddGroup HestenesStokesCarrier]
    [ContinuousSMul ℝ HestenesStokesCarrier]
    (hK_cont : Continuous K) (hI_cont : Continuous I) (p : ℝ × ℝ) :
    (hestenesStokesFlowInverseContinuousMap K I hK hI hKI hK_cont hI_cont p).comp
        (hestenesStokesFlowContinuousMap K I hK hI hKI hK_cont hI_cont p) =
      ContinuousMap.id HestenesStokesCarrier := by
  apply ContinuousMap.ext
  intro q
  change
    (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).symm
        ((hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p) q) = q
  exact (hestenesStokesFlow K I hK hI hKI hK_cont hI_cont p).left_inv q

end

end InfoGeometry.Canonical
