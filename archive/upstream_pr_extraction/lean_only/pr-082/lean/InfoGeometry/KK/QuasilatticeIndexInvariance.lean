import InfoGeometry.Canonical.QuasilatticeDirac
import InfoGeometry.KK.DiracFredholmIndex
import InfoGeometry.Krein.ExponentialIsometry
import InfoGeometry.Meta.Architecture
import Mathlib.Algebra.Module.Submodule.Map

open scoped InnerProductSpace

/-!
# InfoGeometry.KK.QuasilatticeIndexInvariance

Operatorial Bogoliubov-flow transport of the real split-Krein Fredholm index.

This file stays in the KK layer. It does not route the proof through the old
scalar or diagonal analytical-index facade. Instead it works directly with the
transported bounded Dirac operator, the ambient chirality projectors, and the
transported `±` chiral kernel slices.
-/

namespace InfoGeometry.KK

open InfoGeometry.Canonical
open InfoGeometry.Canonical.QuasilatticeDirac
open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Krein

namespace RealSplitKreinKasparovCycle

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

noncomputable local instance : NormedRing EndH := inferInstance
noncomputable local instance : NormedAlgebra ℝ EndH := inferInstance
local instance : IsTopologicalRing EndH := inferInstance
local instance : CompleteSpace EndH := inferInstance

/-- The inverse Bogoliubov flow acting on the doubled carrier. -/
@[rep_depth transport]
noncomputable def inverseQuasilatticeFlow
    (V : BogoliubovVielbeinBundle (E := E)) (t : ℝ) : H₂ ≃ₗ[ℝ] H₂ :=
  (InfoGeometry.Krein.expAutomorphism (H := H₂) (A := -V.connectionGenerator) t).toLinearEquiv

/-- The transported bounded Dirac family in the quasilattice frame. -/
@[rep_depth transport]
noncomputable def quasilatticeDiracFamily
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂) :
    ℝ → H₂ →ₗ[ℝ] H₂ :=
  fun t => (quasilatticeDirac V X.F t).toLinearMap

/-- The fixed ambient chirality family used by the operatorial KK index. -/
@[rep_depth transport]
noncomputable def quasilatticeChiralityFamily
    (_V : BogoliubovVielbeinBundle (E := E))
    (_X : RealSplitKreinDiracFredholmModule A B H₂) :
    ℝ → H₂ →ₗ[ℝ] H₂ :=
  fun _ => (KreinGradedModule.gradeCLM (H := H₂)).toLinearMap

/-- Positive transported chiral kernel slice for the quasilattice Dirac family. -/
@[rep_depth transport]
noncomputable def quasilatticeChiralKernelSlicePlus
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂) (t : ℝ) : Submodule ℝ H₂ :=
  LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap ⊓
    LinearMap.range (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap

/-- Negative transported chiral kernel slice for the quasilattice Dirac family. -/
@[rep_depth transport]
noncomputable def quasilatticeChiralKernelSliceMinus
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂) (t : ℝ) : Submodule ℝ H₂ :=
  LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap ⊓
    LinearMap.range (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap

/-- Operatorial Fredholm surface for the transported quasilattice Dirac family. -/
@[rep_depth transport]
def QuasilatticeChiralFredholmSurface
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂) (t : ℝ) : Prop :=
  FiniteDimensional ℝ (quasilatticeChiralKernelSlicePlus V X t) ∧
  FiniteDimensional ℝ (quasilatticeChiralKernelSliceMinus V X t)

/-- Operatorial analytical index of the transported quasilattice Dirac family. -/
@[rep_depth transport]
noncomputable def quasilatticeAnalyticalIndex
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂) (t : ℝ)
    (hVX : QuasilatticeChiralFredholmSurface V X t) : ℤ := by
  rcases hVX with ⟨hPlus, hMinus⟩
  letI := hPlus
  letI := hMinus
  exact
    (Module.finrank ℝ (quasilatticeChiralKernelSlicePlus V X t) : ℤ) -
      (Module.finrank ℝ (quasilatticeChiralKernelSliceMinus V X t) : ℤ)

omit [KreinSpace H₂] [KreinGradedModule H₂] in
@[simp] lemma quasilatticeDirac_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH) :
    quasilatticeDirac V D 0 = D := by
  unfold quasilatticeDirac InfoGeometry.Canonical.expTransport
  rw [zero_smul, NormedSpace.exp_zero, zero_smul, NormedSpace.exp_zero]
  simp

omit [CompleteSpace E] [KreinSpace H₂] [KreinGradedModule H₂] in
/-- Conjugacy transports kernels exactly along an invertible linear map. -/
@[rep_depth transport] lemma map_ker_eq_of_conjugacy
    (Ds D0 : H₂ →ₗ[ℝ] H₂)
    (e : H₂ ≃ₗ[ℝ] H₂)
    (hConj : D0.comp e.toLinearMap = e.toLinearMap.comp Ds) :
    (LinearMap.ker Ds).map e.toLinearMap = LinearMap.ker D0 := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨x, hx, rfl⟩
    change D0 (e x) = 0
    have hConjX : D0 (e x) = e (Ds x) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj x)
    rw [hConjX, hx, map_zero]
  · intro hv
    refine ⟨e.symm v, ?_, by simp⟩
    have hConjX : D0 (e (e.symm v)) = e (Ds (e.symm v)) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj (e.symm v))
    have hImageZero : e (Ds (e.symm v)) = 0 := by
      calc
        e (Ds (e.symm v)) = D0 (e (e.symm v)) := by simpa using hConjX.symm
        _ = D0 v := by simp
        _ = 0 := hv
    exact e.injective (by simpa using hImageZero)

omit [CompleteSpace E] [KreinSpace H₂] [KreinGradedModule H₂] in
/-- Conjugacy transports ranges exactly along an invertible linear map. -/
@[rep_depth transport] lemma map_range_eq_of_conjugacy
    (Ps P0 : H₂ →ₗ[ℝ] H₂)
    (e : H₂ ≃ₗ[ℝ] H₂)
    (hConj : P0.comp e.toLinearMap = e.toLinearMap.comp Ps) :
    (LinearMap.range Ps).map e.toLinearMap = LinearMap.range P0 := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨x, hx, rfl⟩
    rcases hx with ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    have hConjY : P0 (e y) = e (Ps y) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj y)
    simp [hConjY]
  · intro hv
    rcases hv with ⟨x, rfl⟩
    refine ⟨Ps (e.symm x), ?_, ?_⟩
    · exact ⟨e.symm x, rfl⟩
    · have hConjX : P0 (e (e.symm x)) = e (Ps (e.symm x)) := by
        simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj (e.symm x))
      simpa using hConjX.symm

@[rep_depth transport] lemma gradeCLM_comp_eq_comp_gradeCLM_of_isEven
    {T : EndH}
    (hT : KreinGradedModule.IsEven (H := H₂) T) :
    (KreinGradedModule.gradeCLM (H := H₂)).comp T
      = T.comp (KreinGradedModule.gradeCLM (H := H₂)) := by
  let Γ : EndH := KreinGradedModule.gradeCLM (H := H₂)
  have hEven : Γ.comp (T.comp Γ) = T := by
    simpa [Γ, KreinGradedModule.IsEven, KreinGradedModule.gradeConj] using hT
  calc
    Γ.comp T = (Γ.comp (T.comp Γ)).comp Γ := by
      simp [Γ, ContinuousLinearMap.comp_assoc]
    _ = T.comp Γ := by rw [hEven]

@[rep_depth transport] lemma commute_gradeCLM_of_isEven
    {T : EndH}
    (hT : KreinGradedModule.IsEven (H := H₂) T) :
    Commute (KreinGradedModule.gradeCLM (H := H₂)) T := by
  simpa using gradeCLM_comp_eq_comp_gradeCLM_of_isEven (E := E) hT

@[rep_depth transport] lemma inverseQuasilatticeFlow_commutes_grade
    (V : BogoliubovVielbeinBundle (E := E))
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (KreinGradedModule.gradeCLM (H := H₂)).toLinearMap.comp
        (inverseQuasilatticeFlow (E := E) V t).toLinearMap
      =
    (inverseQuasilatticeFlow (E := E) V t).toLinearMap.comp
      (KreinGradedModule.gradeCLM (H := H₂)).toLinearMap := by
  let Γ : EndH := KreinGradedModule.gradeCLM (H := H₂)
  let eNeg : EndH := NormedSpace.exp (t • (-V.connectionGenerator))
  have hCommΓX : Commute Γ V.connectionGenerator :=
    commute_gradeCLM_of_isEven (E := E) hEven
  have hCommΓeNeg : Commute Γ eNeg := by
    have hCommΓneg : Commute Γ (-V.connectionGenerator) := hCommΓX.neg_right
    have hCommΓsmul : Commute Γ (t • (-V.connectionGenerator)) := hCommΓneg.smul_right t
    simpa [eNeg] using hCommΓsmul.exp_right
  have hCommLin :
      Γ.toLinearMap.comp eNeg.toLinearMap = eNeg.toLinearMap.comp Γ.toLinearMap := by
    simpa [ContinuousLinearMap.mul_def] using
      congrArg ContinuousLinearMap.toLinearMap hCommΓeNeg.eq
  have hFlowCLM :
      (((InfoGeometry.Krein.expAutomorphism (H := H₂) (A := -V.connectionGenerator) t :
            H₂ ≃L[ℝ] H₂) : H₂ →L[ℝ] H₂)) = eNeg := by
    simp [eNeg, InfoGeometry.Krein.expAutomorphism_toContinuousLinearMap]
  have hFlowLin :
      (inverseQuasilatticeFlow (E := E) V t).toLinearMap = eNeg.toLinearMap := by
    change
      (((InfoGeometry.Krein.expAutomorphism (H := H₂) (A := -V.connectionGenerator) t :
            H₂ ≃L[ℝ] H₂) : H₂ →L[ℝ] H₂)).toLinearMap = eNeg.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap hFlowCLM
  rw [hFlowLin]
  simpa [Γ] using hCommLin

omit [CompleteSpace E] [KreinSpace H₂] [KreinGradedModule H₂] in
@[rep_depth transport] lemma projectorPlus_comp_of_conjugacy
    (Γs Γ0 : H₂ →ₗ[ℝ] H₂)
    (e : H₂ ≃ₗ[ℝ] H₂)
    (hConj : Γ0.comp e.toLinearMap = e.toLinearMap.comp Γs) :
    (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γ0)).comp e.toLinearMap
      =
    e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γs)) := by
  ext x
  · have hConjX : Γ0 (e x) = e (Γs x) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj x)
    have hWhole :
        ((((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γ0)).comp e.toLinearMap) x
          =
        (e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γs))) x := by
      calc
        ((((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γ0)).comp e.toLinearMap) x
            = ((2 : ℝ)⁻¹) • (e x + e (Γs x)) := by
                simp [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply, hConjX]
        _ = (e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γs))) x := by
                simp [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply, map_add]
    simpa using congrArg WithLp.fst hWhole
  · have hConjX : Γ0 (e x) = e (Γs x) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj x)
    have hWhole :
        ((((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γ0)).comp e.toLinearMap) x
          =
        (e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γs))) x := by
      calc
        ((((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γ0)).comp e.toLinearMap) x
            = ((2 : ℝ)⁻¹) • (e x + e (Γs x)) := by
                simp [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply, hConjX]
        _ = (e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + Γs))) x := by
                simp [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply, map_add]
    simpa using congrArg WithLp.snd hWhole

omit [CompleteSpace E] [KreinSpace H₂] [KreinGradedModule H₂] in
@[rep_depth transport] lemma projectorMinus_comp_of_conjugacy
    (Γs Γ0 : H₂ →ₗ[ℝ] H₂)
    (e : H₂ ≃ₗ[ℝ] H₂)
    (hConj : Γ0.comp e.toLinearMap = e.toLinearMap.comp Γs) :
    (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γ0)).comp e.toLinearMap
      =
    e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γs)) := by
  ext x
  · have hConjX : Γ0 (e x) = e (Γs x) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj x)
    have hWhole :
        ((((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γ0)).comp e.toLinearMap) x
          =
        (e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γs))) x := by
      calc
        ((((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γ0)).comp e.toLinearMap) x
            = ((2 : ℝ)⁻¹) • (e x - e (Γs x)) := by
                simp [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply, hConjX]
        _ = (e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γs))) x := by
                simp [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply, map_sub]
    simpa using congrArg WithLp.fst hWhole
  · have hConjX : Γ0 (e x) = e (Γs x) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj x)
    have hWhole :
        ((((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γ0)).comp e.toLinearMap) x
          =
        (e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γs))) x := by
      calc
        ((((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γ0)).comp e.toLinearMap) x
            = ((2 : ℝ)⁻¹) • (e x - e (Γs x)) := by
                simp [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply, hConjX]
        _ = (e.toLinearMap.comp (((2 : ℝ)⁻¹) • ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - Γs))) x := by
                simp [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply, map_sub]
    simpa using congrArg WithLp.snd hWhole

@[rep_depth transport] lemma inverseQuasilatticeFlow_commutes_chiralProjectorPlus
    (V : BogoliubovVielbeinBundle (E := E))
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap.comp
        (inverseQuasilatticeFlow (E := E) V t).toLinearMap
      =
    (inverseQuasilatticeFlow (E := E) V t).toLinearMap.comp
      (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap := by
  let e := inverseQuasilatticeFlow (E := E) V t
  have hProj :
      (((2 : ℝ)⁻¹) •
          ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + (KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)).comp
          e.toLinearMap
        =
      e.toLinearMap.comp
        (((2 : ℝ)⁻¹) •
          ((LinearMap.id : H₂ →ₗ[ℝ] H₂) + (KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)) := by
    exact projectorPlus_comp_of_conjugacy
      ((KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)
      ((KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)
      e
      (inverseQuasilatticeFlow_commutes_grade (E := E) V hEven t)
  simpa [e, KreinGradedModule.gradeProjPlus] using hProj

@[rep_depth transport] lemma inverseQuasilatticeFlow_commutes_chiralProjectorMinus
    (V : BogoliubovVielbeinBundle (E := E))
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap.comp
        (inverseQuasilatticeFlow (E := E) V t).toLinearMap
      =
    (inverseQuasilatticeFlow (E := E) V t).toLinearMap.comp
      (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap := by
  let e := inverseQuasilatticeFlow (E := E) V t
  have hProj :
      (((2 : ℝ)⁻¹) •
          ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - (KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)).comp
          e.toLinearMap
        =
      e.toLinearMap.comp
        (((2 : ℝ)⁻¹) •
          ((LinearMap.id : H₂ →ₗ[ℝ] H₂) - (KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)) := by
    exact projectorMinus_comp_of_conjugacy
      ((KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)
      ((KreinGradedModule.gradeCLM (H := H₂)).toLinearMap)
      e
      (inverseQuasilatticeFlow_commutes_grade (E := E) V hEven t)
  simpa [e, KreinGradedModule.gradeProjMinus] using hProj

omit [KreinSpace H₂] [KreinGradedModule H₂] in
@[rep_depth transport] lemma inverseQuasilatticeFlow_conjugates_dirac
    (V : BogoliubovVielbeinBundle (E := E))
    (D : EndH) (t : ℝ) :
    D.toLinearMap.comp (inverseQuasilatticeFlow (E := E) V t).toLinearMap
      =
    (inverseQuasilatticeFlow (E := E) V t).toLinearMap.comp
      (quasilatticeDirac V D t).toLinearMap := by
  let eNeg : EndH := NormedSpace.exp (t • (-V.connectionGenerator))
  let ePos : EndH := NormedSpace.exp (t • V.connectionGenerator)
  have hComm : Commute (t • (-V.connectionGenerator)) (t • V.connectionGenerator) := by
    rw [smul_neg]
    exact (Commute.refl (t • V.connectionGenerator)).neg_left
  have hCancel : eNeg * ePos = (1 : EndH) := by
    calc
      eNeg * ePos
        = NormedSpace.exp (t • (-V.connectionGenerator) + t • V.connectionGenerator) := by
            symm
            simpa [eNeg, ePos] using NormedSpace.exp_add_of_commute hComm
      _ = (1 : EndH) := by
            simp
  have hMain : D.comp eNeg = eNeg.comp (quasilatticeDirac V D t) := by
    unfold quasilatticeDirac InfoGeometry.Canonical.expTransport
    calc
      D.comp eNeg = ((ContinuousLinearMap.id ℝ H₂).comp D).comp eNeg := by
        simp
      _ = ((eNeg.comp ePos).comp D).comp eNeg := by
        rw [show eNeg.comp ePos = ContinuousLinearMap.id ℝ H₂ by
          simpa [ContinuousLinearMap.mul_def] using hCancel]
      _ = eNeg.comp (((ePos.comp D).comp eNeg)) := by
        simp [ContinuousLinearMap.comp_assoc]
  have hMainLin :
      D.toLinearMap.comp eNeg.toLinearMap
        =
      eNeg.toLinearMap.comp (quasilatticeDirac V D t).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hMain
  have hFlowCLM :
      (((InfoGeometry.Krein.expAutomorphism (H := H₂) (A := -V.connectionGenerator) t :
            H₂ ≃L[ℝ] H₂) : H₂ →L[ℝ] H₂)) = eNeg := by
    simp [eNeg, InfoGeometry.Krein.expAutomorphism_toContinuousLinearMap]
  have hFlowLin :
      (inverseQuasilatticeFlow (E := E) V t).toLinearMap = eNeg.toLinearMap := by
    change
      (((InfoGeometry.Krein.expAutomorphism (H := H₂) (A := -V.connectionGenerator) t :
            H₂ ≃L[ℝ] H₂) : H₂ →L[ℝ] H₂)).toLinearMap = eNeg.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap hFlowCLM
  rw [hFlowLin]
  exact hMainLin

@[rep_depth transport] theorem quasilatticeChiralKernelSlicePlus_map_eq
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (quasilatticeChiralKernelSlicePlus (E := E) V X t).map
        (inverseQuasilatticeFlow (E := E) V t).toLinearMap
      =
    X.chiralKernelSlicePlus := by
  let e := inverseQuasilatticeFlow (E := E) V t
  have hKer :
      (LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap).map e.toLinearMap
        =
      LinearMap.ker X.F.toLinearMap := by
    exact map_ker_eq_of_conjugacy
      (Ds := (quasilatticeDirac V X.F t).toLinearMap)
      (D0 := X.F.toLinearMap)
      (e := e)
      (inverseQuasilatticeFlow_conjugates_dirac (E := E) V X.F t)
  have hRange :
      (LinearMap.range (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap).map e.toLinearMap
        =
      LinearMap.range (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap := by
    exact map_range_eq_of_conjugacy
      (Ps := (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap)
      (P0 := (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap)
      (e := e)
      (inverseQuasilatticeFlow_commutes_chiralProjectorPlus (E := E) V hEven t)
  unfold quasilatticeChiralKernelSlicePlus RealSplitKreinKasparovCycle.chiralKernelSlicePlus
  calc
    (LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap ⊓
        LinearMap.range (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap).map e.toLinearMap
      =
        (LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap).map e.toLinearMap ⊓
          (LinearMap.range (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap).map e.toLinearMap := by
            simpa using
              (Submodule.map_inf (f := e.toLinearMap)
                (p := LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap)
                (q := LinearMap.range (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap)
                e.injective)
    _ = LinearMap.ker X.F.toLinearMap ⊓
          LinearMap.range (KreinGradedModule.gradeProjPlus (H := H₂)).toLinearMap := by
            rw [hKer, hRange]

@[rep_depth transport] theorem quasilatticeChiralKernelSliceMinus_map_eq
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    (quasilatticeChiralKernelSliceMinus (E := E) V X t).map
        (inverseQuasilatticeFlow (E := E) V t).toLinearMap
      =
    X.chiralKernelSliceMinus := by
  let e := inverseQuasilatticeFlow (E := E) V t
  have hKer :
      (LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap).map e.toLinearMap
        =
      LinearMap.ker X.F.toLinearMap := by
    exact map_ker_eq_of_conjugacy
      (Ds := (quasilatticeDirac V X.F t).toLinearMap)
      (D0 := X.F.toLinearMap)
      (e := e)
      (inverseQuasilatticeFlow_conjugates_dirac (E := E) V X.F t)
  have hRange :
      (LinearMap.range (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap).map e.toLinearMap
        =
      LinearMap.range (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap := by
    exact map_range_eq_of_conjugacy
      (Ps := (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap)
      (P0 := (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap)
      (e := e)
      (inverseQuasilatticeFlow_commutes_chiralProjectorMinus (E := E) V hEven t)
  unfold quasilatticeChiralKernelSliceMinus RealSplitKreinKasparovCycle.chiralKernelSliceMinus
  calc
    (LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap ⊓
        LinearMap.range (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap).map e.toLinearMap
      =
        (LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap).map e.toLinearMap ⊓
          (LinearMap.range (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap).map e.toLinearMap := by
            simpa using
              (Submodule.map_inf (f := e.toLinearMap)
                (p := LinearMap.ker (quasilatticeDirac V X.F t).toLinearMap)
                (q := LinearMap.range (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap)
                e.injective)
    _ = LinearMap.ker X.F.toLinearMap ⊓
          LinearMap.range (KreinGradedModule.gradeProjMinus (H := H₂)).toLinearMap := by
            rw [hKer, hRange]

/-- Positive transported chiral kernel slice is linearly equivalent to the baseline one. -/
@[rep_depth transport]
noncomputable def quasilatticeChiralKernelSlicePlusEquiv
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeChiralKernelSlicePlus V X t ≃ₗ[ℝ] X.chiralKernelSlicePlus := by
  let e := inverseQuasilatticeFlow (E := E) V t
  let eMap :
      quasilatticeChiralKernelSlicePlus V X t ≃ₗ[ℝ]
        (quasilatticeChiralKernelSlicePlus V X t).map e.toLinearMap :=
    Submodule.equivMapOfInjective
      (f := e.toLinearMap) (i := e.injective)
      (p := quasilatticeChiralKernelSlicePlus V X t)
  exact eMap.trans <|
    LinearEquiv.ofEq _ _
      (quasilatticeChiralKernelSlicePlus_map_eq (E := E) V X hEven t)

/-- Negative transported chiral kernel slice is linearly equivalent to the baseline one. -/
@[rep_depth transport]
noncomputable def quasilatticeChiralKernelSliceMinusEquiv
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeChiralKernelSliceMinus V X t ≃ₗ[ℝ] X.chiralKernelSliceMinus := by
  let e := inverseQuasilatticeFlow (E := E) V t
  let eMap :
      quasilatticeChiralKernelSliceMinus V X t ≃ₗ[ℝ]
        (quasilatticeChiralKernelSliceMinus V X t).map e.toLinearMap :=
    Submodule.equivMapOfInjective
      (f := e.toLinearMap) (i := e.injective)
      (p := quasilatticeChiralKernelSliceMinus V X t)
  exact eMap.trans <|
    LinearEquiv.ofEq _ _
      (quasilatticeChiralKernelSliceMinus_map_eq (E := E) V X hEven t)

/-- The baseline Fredholm surface transports to every quasilattice time slice. -/
@[rep_depth transport]
noncomputable def quasilatticeChiralFredholmSurfaceOf
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    QuasilatticeChiralFredholmSurface V X t := by
  refine ⟨?_, ?_⟩
  ·
    rcases hX with ⟨hPlus, hMinus⟩
    letI := hPlus
    exact FiniteDimensional.of_injective
      (quasilatticeChiralKernelSlicePlusEquiv (E := E) V X hEven t).toLinearMap
      (quasilatticeChiralKernelSlicePlusEquiv (E := E) V X hEven t).injective
  ·
    rcases hX with ⟨hPlus, hMinus⟩
    letI := hMinus
    exact FiniteDimensional.of_injective
      (quasilatticeChiralKernelSliceMinusEquiv (E := E) V X hEven t).toLinearMap
      (quasilatticeChiralKernelSliceMinusEquiv (E := E) V X hEven t).injective

/-- Bogoliubov transport preserves the operatorial KK analytical index. -/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_eq_initial
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (t : ℝ) :
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t)
      =
    X.analyticalIndex hX := by
  let hQt := quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t
  rcases hX with ⟨hPlus, hMinus⟩
  rcases hQt with ⟨hPlusQt, hMinusQt⟩
  letI := hPlus
  letI := hMinus
  letI := hPlusQt
  letI := hMinusQt
  have hPlusFinrank :
      Module.finrank ℝ (quasilatticeChiralKernelSlicePlus V X t)
        =
      Module.finrank ℝ X.chiralKernelSlicePlus :=
    (quasilatticeChiralKernelSlicePlusEquiv (E := E) V X hEven t).finrank_eq
  have hMinusFinrank :
      Module.finrank ℝ (quasilatticeChiralKernelSliceMinus V X t)
        =
      Module.finrank ℝ X.chiralKernelSliceMinus :=
    (quasilatticeChiralKernelSliceMinusEquiv (E := E) V X hEven t).finrank_eq
  change
    ((Module.finrank ℝ (quasilatticeChiralKernelSlicePlus V X t) : ℤ) -
        (Module.finrank ℝ (quasilatticeChiralKernelSliceMinus V X t) : ℤ))
      =
    ((Module.finrank ℝ X.chiralKernelSlicePlus : ℤ) -
        (Module.finrank ℝ X.chiralKernelSliceMinus : ℤ))
  rw [hPlusFinrank, hMinusFinrank]

/-- Any two quasilattice time slices carry the same operatorial KK analytical index. -/
@[rep_depth transport]
theorem quasilatticeAnalyticalIndex_eq
    (V : BogoliubovVielbeinBundle (E := E))
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hEven : KreinGradedModule.IsEven (H := H₂) V.connectionGenerator)
    (s t : ℝ) :
    quasilatticeAnalyticalIndex V X s
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven s)
      =
    quasilatticeAnalyticalIndex V X t
        (quasilatticeChiralFredholmSurfaceOf (E := E) V X hX hEven t) := by
  rw [quasilatticeAnalyticalIndex_eq_initial (E := E) V X hX hEven s,
    quasilatticeAnalyticalIndex_eq_initial (E := E) V X hX hEven t]

end RealSplitKreinKasparovCycle

end InfoGeometry.KK
