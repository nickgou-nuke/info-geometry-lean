import InfoGeometry.Canonical.RealDoubledKreinMirror
import Mathlib

/-!
# Continuous real doubled-Krein mirror

On a finite-dimensional real normed carrier, the algebraic mirror conjugation
extends canonically to continuous linear operators.  This owner adds only
that topological packaging; it does not introduce an antilinear map, a
Krein-adjoint theorem, or a C*-completion.
-/

noncomputable section

namespace InfoGeometry.Canonical.DoubledHestenesKreinData

open CategoryTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable (K : DoubledHestenesKreinData V)

abbrev ContinuousOperator (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] := V →L[ℝ] V

def mirrorContinuous : ContinuousOperator V :=
  LinearMap.toContinuousLinearMap K.mirror.toLinearMap

def mirrorSymmContinuous : ContinuousOperator V :=
  LinearMap.toContinuousLinearMap K.mirror.symm.toLinearMap

def clockContinuous : ContinuousOperator V :=
  LinearMap.toContinuousLinearMap K.clock

def mirrorConjugateContinuous (T : ContinuousOperator V) : ContinuousOperator V :=
  (mirrorContinuous K).comp
    (T.comp (mirrorSymmContinuous K))

theorem continuous_mirrorConjugateContinuous :
    Continuous (fun T : ContinuousOperator V =>
      mirrorConjugateContinuous K T) := by
  have hpre : Continuous (fun T : ContinuousOperator V =>
      T.comp (mirrorSymmContinuous K)) :=
    (ContinuousLinearMap.precomp (E := V) (F := V) (G := V)
      (mirrorSymmContinuous K)).continuous
  have hpost : Continuous (fun T : ContinuousOperator V =>
      (mirrorContinuous K).comp T) :=
    (ContinuousLinearMap.postcomp (E := V) (F := V) (G := V)
      (mirrorContinuous K)).continuous
  exact hpost.comp hpre

noncomputable def mirrorConjugateContinuousLinear :
    (ContinuousOperator V) →L[ℝ] (ContinuousOperator V) :=
  (ContinuousLinearMap.postcomp (E := V) (F := V) (G := V)
      (mirrorContinuous K)).comp
    (ContinuousLinearMap.precomp (E := V) (F := V) (G := V)
      (mirrorSymmContinuous K))

@[simp] theorem mirrorConjugateContinuousLinear_apply
    (T : ContinuousOperator V) :
    mirrorConjugateContinuousLinear K T =
      mirrorConjugateContinuous K T := rfl

noncomputable def mirrorConjugateTopCatHom :
    TopCat.of (ContinuousOperator V) ⟶ TopCat.of (ContinuousOperator V) :=
  TopCat.ofHom
    (ContinuousMap.mk (mirrorConjugateContinuousLinear K)
      (mirrorConjugateContinuousLinear K).continuous)

@[simp] theorem mirrorConjugateTopCatHom_apply
    (T : ContinuousOperator V) :
    mirrorConjugateTopCatHom K T = mirrorConjugateContinuous K T := rfl

@[simp] theorem mirrorConjugateContinuous_apply
    (T : ContinuousOperator V) (v : V) :
    mirrorConjugateContinuous K T v =
      K.mirror (T (K.mirror.symm v)) := by
  rfl

theorem mirrorConjugateContinuous_mul
    (T U : ContinuousOperator V) :
    mirrorConjugateContinuous K (T.comp U) =
      (mirrorConjugateContinuous K T).comp
        (mirrorConjugateContinuous K U) := by
  ext v
  simp [mirrorConjugateContinuous, mirrorContinuous, mirrorSymmContinuous,
    ContinuousLinearMap.comp_apply, Function.comp_def]

theorem mirrorConjugateContinuous_clock :
    mirrorConjugateContinuous K (clockContinuous K) =
      -(clockContinuous K) := by
  ext v
  have h := congrArg (fun f : V →ₗ[ℝ] V => f v) K.mirror_clock
  simpa [mirrorConjugateContinuous, mirrorContinuous, mirrorSymmContinuous,
    clockContinuous, LinearMap.comp_apply] using h

theorem mirrorConjugateContinuous_involutive
    (T : ContinuousOperator V) :
    mirrorConjugateContinuous K
        (mirrorConjugateContinuous K T) = T := by
  have hmirror : K.mirror.symm = K.mirror := by
    apply LinearEquiv.ext
    intro v
    apply K.mirror.injective
    simp [mirror_sq_apply]
  ext v
  simp [mirrorConjugateContinuous, mirrorContinuous, mirrorSymmContinuous,
    ContinuousLinearMap.comp_apply, hmirror, mirror_sq_apply]

def continuousOperatorCommutator
    (T U : ContinuousOperator V) : ContinuousOperator V :=
  T.comp U - U.comp T

def HasContinuousGrade
    (clock : ContinuousOperator V) (k : ℤ) (T : ContinuousOperator V) : Prop :=
  continuousOperatorCommutator clock T = (k : ℝ) • T

theorem mirrorConjugateContinuous_sub
    (T U : ContinuousOperator V) :
    mirrorConjugateContinuous K (T - U) =
      mirrorConjugateContinuous K T - mirrorConjugateContinuous K U := by
  ext v
  simp [mirrorConjugateContinuous, mirrorContinuous, mirrorSymmContinuous,
    ContinuousLinearMap.sub_apply]

theorem mirrorConjugateContinuous_smul
    (a : ℝ) (T : ContinuousOperator V) :
    mirrorConjugateContinuous K (a • T) =
      a • mirrorConjugateContinuous K T := by
  ext v
  simp [mirrorConjugateContinuous, mirrorContinuous, mirrorSymmContinuous,
    ContinuousLinearMap.smul_apply]

theorem mirrorConjugateContinuous_commutator
    (T U : ContinuousOperator V) :
    mirrorConjugateContinuous K (continuousOperatorCommutator T U) =
      continuousOperatorCommutator
        (mirrorConjugateContinuous K T)
        (mirrorConjugateContinuous K U) := by
  simp only [continuousOperatorCommutator, mirrorConjugateContinuous_sub,
    mirrorConjugateContinuous_mul]

theorem mirror_reverses_continuous_operator_grade
    {k : ℤ} {T : ContinuousOperator V}
    (hT : HasContinuousGrade (clockContinuous K) k T) :
    HasContinuousGrade (clockContinuous K) (-k)
      (mirrorConjugateContinuous K T) := by
  have htransport := congrArg (mirrorConjugateContinuous K) hT
  rw [mirrorConjugateContinuous_commutator,
    mirrorConjugateContinuous_clock,
    mirrorConjugateContinuous_smul] at htransport
  change continuousOperatorCommutator
      (-(clockContinuous K)) (mirrorConjugateContinuous K T) =
    (k : ℝ) • mirrorConjugateContinuous K T at htransport
  change continuousOperatorCommutator (clockContinuous K)
      (mirrorConjugateContinuous K T) =
    ((-k : ℤ) : ℝ) • mirrorConjugateContinuous K T
  calc
    continuousOperatorCommutator (clockContinuous K)
        (mirrorConjugateContinuous K T) =
      -continuousOperatorCommutator (-(clockContinuous K))
        (mirrorConjugateContinuous K T) := by
          ext v
          simp [continuousOperatorCommutator]
          abel
    _ = -((k : ℝ) • mirrorConjugateContinuous K T) := by
      rw [htransport]
    _ = ((-k : ℤ) : ℝ) • mirrorConjugateContinuous K T := by
      simp

def mirrorEvenSubmodule : Submodule ℝ (ContinuousOperator V) :=
  LinearMap.ker
    ((mirrorConjugateContinuousLinear K).toLinearMap - LinearMap.id)

def mirrorOddSubmodule : Submodule ℝ (ContinuousOperator V) :=
  LinearMap.ker
    ((mirrorConjugateContinuousLinear K).toLinearMap + LinearMap.id)

theorem mem_mirrorEvenSubmodule_iff (T : ContinuousOperator V) :
    T ∈ mirrorEvenSubmodule K ↔
      mirrorConjugateContinuous K T = T := by
  change (mirrorConjugateContinuous K T - T = 0) ↔ _
  exact sub_eq_zero

theorem mem_mirrorOddSubmodule_iff (T : ContinuousOperator V) :
    T ∈ mirrorOddSubmodule K ↔
      mirrorConjugateContinuous K T = -T := by
  change (mirrorConjugateContinuous K T + T = 0) ↔ _
  constructor
  · intro h
    exact eq_neg_of_add_eq_zero_left h
  · intro h
    rw [h]
    abel

def mirrorEvenPart (T : ContinuousOperator V) : ContinuousOperator V :=
  (1 / 2 : ℝ) • (T + mirrorConjugateContinuous K T)

def mirrorOddPart (T : ContinuousOperator V) : ContinuousOperator V :=
  (1 / 2 : ℝ) • (T - mirrorConjugateContinuous K T)

theorem mirrorEvenPart_mem (T : ContinuousOperator V) :
    mirrorEvenPart K T ∈ mirrorEvenSubmodule K := by
  rw [mem_mirrorEvenSubmodule_iff]
  change mirrorConjugateContinuousLinear K
      ((1 / 2 : ℝ) • (T + mirrorConjugateContinuousLinear K T)) =
    (1 / 2 : ℝ) • (T + mirrorConjugateContinuousLinear K T)
  rw [map_smul, map_add, mirrorConjugateContinuousLinear_apply,
    mirrorConjugateContinuousLinear_apply,
    mirrorConjugateContinuous_involutive]
  module

theorem mirrorOddPart_mem (T : ContinuousOperator V) :
    mirrorOddPart K T ∈ mirrorOddSubmodule K := by
  rw [mem_mirrorOddSubmodule_iff]
  change mirrorConjugateContinuousLinear K
      ((1 / 2 : ℝ) • (T - mirrorConjugateContinuousLinear K T)) =
    -((1 / 2 : ℝ) • (T - mirrorConjugateContinuousLinear K T))
  rw [map_smul, map_sub, mirrorConjugateContinuousLinear_apply,
    mirrorConjugateContinuousLinear_apply,
    mirrorConjugateContinuous_involutive]
  module

theorem mirrorEvenPart_add_oddPart (T : ContinuousOperator V) :
    mirrorEvenPart K T + mirrorOddPart K T = T := by
  unfold mirrorEvenPart mirrorOddPart
  module

theorem mirrorEvenOdd_disjoint :
    Disjoint (mirrorEvenSubmodule K) (mirrorOddSubmodule K) := by
  refine Submodule.disjoint_def.2 ?_
  intro T hEven hOdd
  have hEven' := (mem_mirrorEvenSubmodule_iff K T).1 hEven
  have hOdd' := (mem_mirrorOddSubmodule_iff K T).1 hOdd
  have hzero : T + T = 0 := by
    calc
      T + T = mirrorConjugateContinuous K T + T := by rw [hEven']
      _ = 0 := by rw [hOdd']; abel
  have hhalf := congrArg (fun X : ContinuousOperator V =>
      (1 / 2 : ℝ) • X) hzero
  have hhalf' : (1 / 2 : ℝ) • T + (1 / 2 : ℝ) • T = 0 := by
    simpa only [smul_add, smul_zero] using hhalf
  calc
    T = (1 : ℝ) • T := by simp
    _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • T := by norm_num
    _ = (1 / 2 : ℝ) • T + (1 / 2 : ℝ) • T := by rw [add_smul]
    _ = 0 := hhalf'

theorem mirrorEvenOdd_sup_eq_top :
    mirrorEvenSubmodule K ⊔ mirrorOddSubmodule K = ⊤ := by
  apply top_unique
  intro T hT
  refine Submodule.mem_sup.2 ?_
  exact ⟨mirrorEvenPart K T, mirrorEvenPart_mem K T,
    mirrorOddPart K T, mirrorOddPart_mem K T,
    mirrorEvenPart_add_oddPart K T⟩

theorem mirrorEvenOdd_isCompl :
    IsCompl (mirrorEvenSubmodule K) (mirrorOddSubmodule K) :=
  ⟨mirrorEvenOdd_disjoint K, by
    simpa [codisjoint_iff] using mirrorEvenOdd_sup_eq_top K⟩

end InfoGeometry.Canonical.DoubledHestenesKreinData
