import InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FiniteHestenesDirichletFilteredColimitBridge
import InfoGeometry.Canonical.FiniteHestenesDirichletOperatorBridge

/-!
# Concrete Hestenes phase readout through the filtered Dirichlet colimit

This is the concrete specialization of the generic finite Hestenes--Dirichlet
filtered-colimit bridge.  The coefficient stages and their colimit are reused
unchanged; only the already kernel-checked trigonometric Hestenes phase flow is
instantiated here.

No analytic exponential, norm completion, or infinite Dirichlet convergence is
asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.ConcreteHestenesDirichletFilteredColimit

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.ConcreteChiralHodgeDiracHestenesColimit
open InfoGeometry.Canonical.FiniteHestenesDirichletFilteredColimitBridge
open InfoGeometry.Canonical.FiniteHestenesDirichletOperatorBridge
open InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge

abbrev ConcreteHestenesDirichletStage (n : ℕ) :=
  HestenesDirichletStage n

/-! ## Canonical arithmetic coefficient representatives

These are coefficient vectors in the finite stages, not infinite sequences or
operator series.  Their readouts therefore remain inside the filtered-colimit
semantics of this file.
-/

def oneCoefficients : ℕ → ℝ := fun _ => 1

def mobiusCoefficients : ℕ → ℝ :=
  fun n => (ArithmeticFunction.moebius n : ℝ)

def concreteHestenesPhaseStageCoefficients
    (f : ℕ → ℝ) (n : ℕ) : ConcreteHestenesDirichletStage n :=
  fun j => f (j.1 + 1)

def concreteHestenesPhaseStageReadout (n : ℕ) :
    ConcreteHestenesDirichletStage n →ₗ[ℝ]
      Module.End ℝ DoubledExterior3 :=
  hestenesDirichletStageReadout concreteHestenesPhaseModularDatum n

def concreteHestenesPhaseCoefficientStageReadout
    (f : ℕ → ℝ) (n : ℕ) :
    Module.End ℝ DoubledExterior3 :=
  concreteHestenesPhaseStageReadout n
    (concreteHestenesPhaseStageCoefficients f n)

@[simp] theorem concreteHestenesPhaseStageCoefficients_apply
    (f : ℕ → ℝ) (n : ℕ) (j : Fin (n + 1)) :
    concreteHestenesPhaseStageCoefficients f n j = f (j.1 + 1) := rfl

def concreteHestenesPhaseLogStageReadout (n : ℕ) :
    Module.End ℝ DoubledExterior3 :=
  concreteHestenesPhaseCoefficientStageReadout
    (fun k => Real.log k) n

def concreteHestenesPhaseMangoldtStageReadout (n : ℕ) :
    Module.End ℝ DoubledExterior3 :=
  concreteHestenesPhaseCoefficientStageReadout mangoldtCoefficients n

theorem concreteHestenesPhaseCoefficientStageReadout_apply
    (f : ℕ → ℝ) (n : ℕ) (x : DoubledExterior3) :
    concreteHestenesPhaseCoefficientStageReadout f n x =
      ∑ j : Fin (n + 1),
        f (j.1 + 1) • concreteHestenesPhaseFlow
          (Real.log (j.1 + 1 : ℕ)) x := by
  simp [concreteHestenesPhaseCoefficientStageReadout,
    concreteHestenesPhaseStageReadout,
    hestenesDirichletStageReadout, concreteHestenesPhaseModularDatum]

theorem concreteHestenesPhaseCoefficientStageReadout_eq_finite
    (f : ℕ → ℝ) (n : ℕ) :
    concreteHestenesPhaseCoefficientStageReadout f n =
      finiteHestenesDirichletOperator concreteHestenesPhaseModularDatum
        (n + 1) f := by
  have hsum (m : ℕ) (x : DoubledExterior3) :
      (∑ j : Fin (m + 1), f (j.1 + 1) • concreteHestenesPhaseFlow
        (Real.log (j.1 + 1 : ℕ)) x) =
        ∑ k ∈ Finset.Icc 1 (m + 1), f k •
          concreteHestenesPhaseFlow (Real.log k) x := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Fin.sum_univ_castSucc]
        rw [Finset.sum_Icc_succ_top (by omega)]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [ih]
  apply LinearMap.ext
  intro x
  rw [concreteHestenesPhaseCoefficientStageReadout_apply,
    finiteHestenesDirichletOperator_apply]
  exact hsum n x

theorem concreteHestenesPhaseLogStageReadout_eq_finite
    (n : ℕ) :
    concreteHestenesPhaseLogStageReadout n =
      finiteHestenesLogOperator concreteHestenesPhaseModularDatum (n + 1) := by
  simpa [concreteHestenesPhaseLogStageReadout,
    finiteHestenesLogOperator] using
    concreteHestenesPhaseCoefficientStageReadout_eq_finite
      logCoefficients n

theorem concreteHestenesPhaseMangoldtStageReadout_eq_finite
    (n : ℕ) :
    concreteHestenesPhaseMangoldtStageReadout n =
      finiteHestenesMangoldtOperator concreteHestenesPhaseModularDatum
        (n + 1) := by
  simpa [concreteHestenesPhaseMangoldtStageReadout,
    finiteHestenesMangoldtOperator] using
    concreteHestenesPhaseCoefficientStageReadout_eq_finite
      mangoldtCoefficients n

def concreteHestenesPhaseReadoutColimitMap :
    HestenesDirichletCoefficientColimit ⟶
      colimit (hestenesDirichletTargetFunctor (M := DoubledExterior3)) :=
  hestenesDirichletReadoutColimitMap concreteHestenesPhaseModularDatum

theorem concreteHestenesPhaseReadoutColimitMap_on_stage
    (n : ℕ) (a : ConcreteHestenesDirichletStage n) :
    concreteHestenesPhaseReadoutColimitMap
        ((colimit.ι hestenesDirichletStageFunctor n).hom a) =
      (colimit.ι
        (hestenesDirichletTargetFunctor (M := DoubledExterior3)) n).hom
        (concreteHestenesPhaseStageReadout n a) := by
  exact hestenesDirichletReadoutColimit_on_stage
    concreteHestenesPhaseModularDatum n a

theorem concreteHestenesPhaseReadoutColimitMap_on_coefficients
    (f : ℕ → ℝ) (n : ℕ) :
    concreteHestenesPhaseReadoutColimitMap
        ((colimit.ι hestenesDirichletStageFunctor n).hom
          (concreteHestenesPhaseStageCoefficients f n)) =
      (colimit.ι
        (hestenesDirichletTargetFunctor (M := DoubledExterior3)) n).hom
        (concreteHestenesPhaseCoefficientStageReadout f n) := by
  exact concreteHestenesPhaseReadoutColimitMap_on_stage n
    (concreteHestenesPhaseStageCoefficients f n)

theorem concreteHestenesPhaseReadoutColimitMap_on_one
    (n : ℕ) :
    concreteHestenesPhaseReadoutColimitMap
        ((colimit.ι hestenesDirichletStageFunctor n).hom
          (concreteHestenesPhaseStageCoefficients oneCoefficients n)) =
      (colimit.ι
        (hestenesDirichletTargetFunctor (M := DoubledExterior3)) n).hom
        (concreteHestenesPhaseCoefficientStageReadout oneCoefficients n) := by
  exact concreteHestenesPhaseReadoutColimitMap_on_coefficients oneCoefficients n

theorem concreteHestenesPhaseReadoutColimitMap_on_mobius
    (n : ℕ) :
    concreteHestenesPhaseReadoutColimitMap
        ((colimit.ι hestenesDirichletStageFunctor n).hom
          (concreteHestenesPhaseStageCoefficients mobiusCoefficients n)) =
      (colimit.ι
        (hestenesDirichletTargetFunctor (M := DoubledExterior3)) n).hom
        (concreteHestenesPhaseCoefficientStageReadout mobiusCoefficients n) := by
  exact concreteHestenesPhaseReadoutColimitMap_on_coefficients mobiusCoefficients n

theorem concreteHestenesPhaseReadoutColimitMap_on_log
    (n : ℕ) :
    concreteHestenesPhaseReadoutColimitMap
        ((colimit.ι hestenesDirichletStageFunctor n).hom
          (concreteHestenesPhaseStageCoefficients logCoefficients n)) =
      (colimit.ι
        (hestenesDirichletTargetFunctor (M := DoubledExterior3)) n).hom
        (concreteHestenesPhaseCoefficientStageReadout logCoefficients n) := by
  exact concreteHestenesPhaseReadoutColimitMap_on_coefficients logCoefficients n

theorem concreteHestenesPhaseReadoutColimitMap_on_mangoldt
    (n : ℕ) :
    concreteHestenesPhaseReadoutColimitMap
        ((colimit.ι hestenesDirichletStageFunctor n).hom
          (concreteHestenesPhaseStageCoefficients mangoldtCoefficients n)) =
      (colimit.ι
        (hestenesDirichletTargetFunctor (M := DoubledExterior3)) n).hom
        (concreteHestenesPhaseCoefficientStageReadout mangoldtCoefficients n) := by
  exact concreteHestenesPhaseReadoutColimitMap_on_coefficients mangoldtCoefficients n

theorem concreteHestenesPhaseStageReadout_apply
    (n : ℕ) (a : ConcreteHestenesDirichletStage n)
    (x : DoubledExterior3) :
    concreteHestenesPhaseStageReadout n a x =
      ∑ j : Fin (n + 1),
        (a j) • concreteHestenesPhaseFlow
          (Real.log (j.1 + 1 : ℕ)) x := by
  exact hestenesDirichletStageReadout_apply
    concreteHestenesPhaseModularDatum n a x

theorem concreteHestenesPhaseCoefficientStageReadout_commutes_phase
    (f : ℕ → ℝ) (n : ℕ) :
    hestenesPhase3 ∘ₗ concreteHestenesPhaseCoefficientStageReadout f n =
      concreteHestenesPhaseCoefficientStageReadout f n ∘ₗ hestenesPhase3 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply]
  dsimp [concreteHestenesPhaseCoefficientStageReadout,
    concreteHestenesPhaseStageReadout, hestenesDirichletStageReadout]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  change hestenesPhase3
      (∑ j : Fin (n + 1), (f (j.1 + 1)) •
        concreteHestenesPhaseModularDatum.realFlow
          (Real.log (j.1 + 1 : ℕ)) x) =
    ∑ j : Fin (n + 1), (f (j.1 + 1)) •
      concreteHestenesPhaseModularDatum.realFlow
        (Real.log (j.1 + 1 : ℕ)) (hestenesPhase3 x)
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrArg (fun T : Module.End ℝ DoubledExterior3 => T x)
    (concreteHestenesPhaseFlow_commutes_phase
      (Real.log (j.1 + 1 : ℕ)))
  have hs := congrArg (fun y : DoubledExterior3 => f (j.1 + 1) • y) h
  simpa [concreteHestenesPhaseModularDatum, Module.End.mul_apply,
    Prod.smul_mk] using hs

end InfoGeometry.Canonical.ConcreteHestenesDirichletFilteredColimit
