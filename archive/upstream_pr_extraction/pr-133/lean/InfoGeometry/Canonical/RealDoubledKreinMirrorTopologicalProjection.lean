import InfoGeometry.Canonical.RealDoubledKreinMirrorTopological

/-!
# Continuous even/odd mirror projections

This owner packages the algebraic mirror splitting as continuous linear maps.
It does not assert a C*-completion, a Hilbert adjoint, or an analytic spectral
calculus beyond the bounded operator space already present in the imported
owner.
-/

namespace InfoGeometry.Canonical.DoubledHestenesKreinData

open CategoryTheory

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable (K : DoubledHestenesKreinData V)

noncomputable def mirrorEvenPartContinuousLinear :
    ContinuousOperator V →L[ℝ] ContinuousOperator V :=
  (1 / 2 : ℝ) •
    (ContinuousLinearMap.id ℝ (ContinuousOperator V) +
      mirrorConjugateContinuousLinear K)

noncomputable def mirrorOddPartContinuousLinear :
    ContinuousOperator V →L[ℝ] ContinuousOperator V :=
  (1 / 2 : ℝ) •
    (ContinuousLinearMap.id ℝ (ContinuousOperator V) -
      mirrorConjugateContinuousLinear K)

@[simp] theorem mirrorEvenPartContinuousLinear_apply
    (T : ContinuousOperator V) :
    mirrorEvenPartContinuousLinear K T = mirrorEvenPart K T := by
  simp [mirrorEvenPartContinuousLinear, mirrorEvenPart,
    mirrorConjugateContinuousLinear_apply]

@[simp] theorem mirrorOddPartContinuousLinear_apply
    (T : ContinuousOperator V) :
    mirrorOddPartContinuousLinear K T = mirrorOddPart K T := by
  simp [mirrorOddPartContinuousLinear, mirrorOddPart,
    mirrorConjugateContinuousLinear_apply]

theorem mirrorEvenPartContinuousLinear_idempotent
    (T : ContinuousOperator V) :
    mirrorEvenPartContinuousLinear K
        (mirrorEvenPartContinuousLinear K T) =
      mirrorEvenPartContinuousLinear K T := by
  have hfix : mirrorConjugateContinuous K (mirrorEvenPart K T) =
      mirrorEvenPart K T :=
    (mem_mirrorEvenSubmodule_iff K (mirrorEvenPart K T)).1
      (mirrorEvenPart_mem K T)
  calc
    mirrorEvenPartContinuousLinear K
        (mirrorEvenPartContinuousLinear K T) =
        mirrorEvenPart K (mirrorEvenPartContinuousLinear K T) :=
      mirrorEvenPartContinuousLinear_apply K
        (mirrorEvenPartContinuousLinear K T)
    _ = mirrorEvenPart K (mirrorEvenPart K T) := by
      rw [mirrorEvenPartContinuousLinear_apply K T]
    _ = mirrorEvenPart K T := by
      change (1 / 2 : ℝ) •
        (mirrorEvenPart K T + mirrorConjugateContinuous K
          (mirrorEvenPart K T)) = mirrorEvenPart K T
      rw [hfix]
      module
    _ = mirrorEvenPartContinuousLinear K T :=
      (mirrorEvenPartContinuousLinear_apply K T).symm

theorem mirrorOddPartContinuousLinear_idempotent
    (T : ContinuousOperator V) :
    mirrorOddPartContinuousLinear K
        (mirrorOddPartContinuousLinear K T) =
      mirrorOddPartContinuousLinear K T := by
  have hfix : mirrorConjugateContinuous K (mirrorOddPart K T) =
      -mirrorOddPart K T :=
    (mem_mirrorOddSubmodule_iff K (mirrorOddPart K T)).1
      (mirrorOddPart_mem K T)
  calc
    mirrorOddPartContinuousLinear K
        (mirrorOddPartContinuousLinear K T) =
        mirrorOddPart K (mirrorOddPartContinuousLinear K T) :=
      mirrorOddPartContinuousLinear_apply K
        (mirrorOddPartContinuousLinear K T)
    _ = mirrorOddPart K (mirrorOddPart K T) := by
      rw [mirrorOddPartContinuousLinear_apply K T]
    _ = mirrorOddPart K T := by
      change (1 / 2 : ℝ) •
        (mirrorOddPart K T - mirrorConjugateContinuous K
          (mirrorOddPart K T)) = mirrorOddPart K T
      rw [hfix]
      module
    _ = mirrorOddPartContinuousLinear K T :=
      (mirrorOddPartContinuousLinear_apply K T).symm

theorem mirrorContinuousProjection_reconstruction
    (T : ContinuousOperator V) :
    mirrorEvenPartContinuousLinear K T +
        mirrorOddPartContinuousLinear K T = T := by
  rw [mirrorEvenPartContinuousLinear_apply,
    mirrorOddPartContinuousLinear_apply]
  exact mirrorEvenPart_add_oddPart K T

theorem mirrorContinuousProjection_disjoint
    (T : ContinuousOperator V)
    (hEven : mirrorEvenPartContinuousLinear K T = 0)
    (hOdd : mirrorOddPartContinuousLinear K T = 0) :
    T = 0 := by
  have hsum := mirrorContinuousProjection_reconstruction K T
  rw [hEven, hOdd, zero_add] at hsum
  exact hsum.symm

noncomputable def mirrorEvenPartTopCatHom :
    TopCat.of (ContinuousOperator V) ⟶ TopCat.of (ContinuousOperator V) :=
  TopCat.ofHom
    (ContinuousMap.mk (mirrorEvenPartContinuousLinear K)
      (mirrorEvenPartContinuousLinear K).continuous)

noncomputable def mirrorOddPartTopCatHom :
    TopCat.of (ContinuousOperator V) ⟶ TopCat.of (ContinuousOperator V) :=
  TopCat.ofHom
    (ContinuousMap.mk (mirrorOddPartContinuousLinear K)
      (mirrorOddPartContinuousLinear K).continuous)

@[simp] theorem mirrorEvenPartTopCatHom_apply
    (T : ContinuousOperator V) :
    mirrorEvenPartTopCatHom K T = mirrorEvenPart K T := by
  rfl

@[simp] theorem mirrorOddPartTopCatHom_apply
    (T : ContinuousOperator V) :
    mirrorOddPartTopCatHom K T = mirrorOddPart K T := by
  rfl

end
end InfoGeometry.Canonical.DoubledHestenesKreinData
