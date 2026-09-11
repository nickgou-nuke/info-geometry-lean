import InfoGeometry.Canonical.RealDoubledKreinMirrorTopologicalProjection
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Continuous direct-sum maps for the real mirror splitting

The even and odd continuous operator submodules are assembled into explicit
continuous maps in both directions.  The reconstruction theorem is the
topological direct-sum statement proved here; no C*-completion is assumed.
-/

namespace InfoGeometry.Canonical.DoubledHestenesKreinData

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable (K : DoubledHestenesKreinData V)

noncomputable def mirrorEvenPartInto :
    ContinuousOperator V →L[ℝ] mirrorEvenSubmodule K :=
  (mirrorEvenPartContinuousLinear K).codRestrict
    (mirrorEvenSubmodule K) (fun T => mirrorEvenPart_mem K T)

noncomputable def mirrorOddPartInto :
    ContinuousOperator V →L[ℝ] mirrorOddSubmodule K :=
  (mirrorOddPartContinuousLinear K).codRestrict
    (mirrorOddSubmodule K) (fun T => mirrorOddPart_mem K T)

noncomputable def mirrorEvenPartFrom :
    mirrorEvenSubmodule K →L[ℝ] ContinuousOperator V :=
  LinearMap.toContinuousLinearMap (Submodule.subtype (mirrorEvenSubmodule K))

noncomputable def mirrorOddPartFrom :
    mirrorOddSubmodule K →L[ℝ] ContinuousOperator V :=
  LinearMap.toContinuousLinearMap (Submodule.subtype (mirrorOddSubmodule K))

noncomputable def mirrorProjectionToProduct :
    ContinuousOperator V →L[ℝ]
      (mirrorEvenSubmodule K × mirrorOddSubmodule K) :=
  ContinuousLinearMap.prod
    (mirrorEvenPartInto K) (mirrorOddPartInto K)

noncomputable def mirrorProjectionFromProduct :
    (mirrorEvenSubmodule K × mirrorOddSubmodule K) →L[ℝ]
      ContinuousOperator V :=
  (mirrorEvenPartFrom K).comp
      (ContinuousLinearMap.fst ℝ (mirrorEvenSubmodule K)
        (mirrorOddSubmodule K)) +
    (mirrorOddPartFrom K).comp
      (ContinuousLinearMap.snd ℝ (mirrorEvenSubmodule K)
        (mirrorOddSubmodule K))

@[simp] theorem mirrorProjectionToProduct_fst (T : ContinuousOperator V) :
    (mirrorProjectionToProduct K T).1 = mirrorEvenPart K T := by
  rfl

@[simp] theorem mirrorProjectionToProduct_snd (T : ContinuousOperator V) :
    (mirrorProjectionToProduct K T).2 = mirrorOddPart K T := by
  rfl

theorem mirrorProjectionFromProduct_apply
    (p : mirrorEvenSubmodule K × mirrorOddSubmodule K) :
    mirrorProjectionFromProduct K p = p.1 + p.2 := by
  rfl

theorem mirrorProjectionFromProduct_toProduct (T : ContinuousOperator V) :
    mirrorProjectionFromProduct K (mirrorProjectionToProduct K T) = T := by
  change mirrorEvenPart K T + mirrorOddPart K T = T
  exact mirrorEvenPart_add_oddPart K T

end
end InfoGeometry.Canonical.DoubledHestenesKreinData
