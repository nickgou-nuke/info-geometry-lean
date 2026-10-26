/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearRealKreinFeshbach
import InfoGeometry.Physics.NuclearComplementaryResolvent
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite native-real realization of the owned complementary inverse

The inverse is still the existing `NuclearComplementaryResolvent.liftInverse`
on the actual native submodule `ker P`. Finite dimension supplies continuity
of that linear map. The explicit forward-map hypothesis on the complementary
equivalence remains the only invertibility input; no inverse on the full
ambient carrier is assumed.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearRealKreinComplementaryResolvent

open InfoGeometry.Krein

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [CompleteSpace V] [FiniteDimensional ℝ V] [KreinSpace V]

/-- The owned complementary inverse, made continuous on a finite real carrier. -/
def liftInverse (P : V →L[ℝ] V) (hP : P * P = P)
    (e : LinearMap.ker P.toLinearMap ≃ₗ[ℝ] LinearMap.ker P.toLinearMap) : V →L[ℝ] V :=
  LinearMap.toContinuousLinearMap
    (NuclearComplementaryResolvent.liftInverse P.toLinearMap
      (congrArg ContinuousLinearMap.toLinearMap hP) e)

@[simp] theorem liftInverse_toLinearMap (P : V →L[ℝ] V) (hP : P * P = P)
    (e : LinearMap.ker P.toLinearMap ≃ₗ[ℝ] LinearMap.ker P.toLinearMap) :
    (liftInverse P hP e).toLinearMap =
      NuclearComplementaryResolvent.liftInverse P.toLinearMap
        (congrArg ContinuousLinearMap.toLinearMap hP) e := rfl

theorem complement_mul_liftInverse (P : V →L[ℝ] V) (hP : P * P = P)
    (e : LinearMap.ker P.toLinearMap ≃ₗ[ℝ] LinearMap.ker P.toLinearMap) :
    (1 - P) * liftInverse P hP e = liftInverse P hP e := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun
    (NuclearComplementaryResolvent.complement_mul_liftInverse P.toLinearMap
      (congrArg ContinuousLinearMap.toLinearMap hP) e) v

theorem liftInverse_mul_complement (P : V →L[ℝ] V) (hP : P * P = P)
    (e : LinearMap.ker P.toLinearMap ≃ₗ[ℝ] LinearMap.ker P.toLinearMap) :
    liftInverse P hP e * (1 - P) = liftInverse P hP e := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun
    (NuclearComplementaryResolvent.liftInverse_mul_complement P.toLinearMap
      (congrArg ContinuousLinearMap.toLinearMap hP) e) v

theorem denominator_mul_liftInverse (P H : V →L[ℝ] V) (E : ℝ) (hP : P * P = P)
    (e : LinearMap.ker P.toLinearMap ≃ₗ[ℝ] LinearMap.ker P.toLinearMap)
    (he : e.toLinearMap = NuclearComplementaryResolvent.complementShift
      P.toLinearMap (congrArg ContinuousLinearMap.toLinearMap hP) H.toLinearMap E) :
    NuclearRealKreinFeshbach.denominator P H E * liftInverse P hP e = 1 - P := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun
    (NuclearComplementaryResolvent.denominator_mul_liftInverse
      P.toLinearMap H.toLinearMap E
      (congrArg ContinuousLinearMap.toLinearMap hP) e he) v

theorem liftInverse_mul_denominator (P H : V →L[ℝ] V) (E : ℝ) (hP : P * P = P)
    (e : LinearMap.ker P.toLinearMap ≃ₗ[ℝ] LinearMap.ker P.toLinearMap)
    (he : e.toLinearMap = NuclearComplementaryResolvent.complementShift
      P.toLinearMap (congrArg ContinuousLinearMap.toLinearMap hP) H.toLinearMap E) :
    liftInverse P hP e * NuclearRealKreinFeshbach.denominator P H E = 1 - P := by
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun
    (NuclearComplementaryResolvent.liftInverse_mul_denominator
      P.toLinearMap H.toLinearMap E
      (congrArg ContinuousLinearMap.toLinearMap hP) e he) v

/-- The genuine finite complementary inverse has the native Krein adjoint. -/
theorem liftInverse_kreinAdjoint (P H : V →L[ℝ] V) (E : ℝ) (hPP : P * P = P)
    (e : LinearMap.ker P.toLinearMap ≃ₗ[ℝ] LinearMap.ker P.toLinearMap)
    (he : e.toLinearMap = NuclearComplementaryResolvent.complementShift
      P.toLinearMap (congrArg ContinuousLinearMap.toLinearMap hPP) H.toLinearMap E)
    (hP : KreinSpace.kreinAdjoint P = P) (hH : KreinSpace.kreinAdjoint H = H) :
    KreinSpace.kreinAdjoint (liftInverse P hPP e) = liftInverse P hPP e :=
  NuclearRealKreinFeshbach.resolvent_kreinAdjoint P H (liftInverse P hPP e) E hP hH
    (complement_mul_liftInverse P hPP e)
    (denominator_mul_liftInverse P H E hPP e he)

/-- Effective Krein self-adjointness follows from the actual native inverse,
with its precise complementary-domain hypothesis retained. -/
theorem effectiveHamiltonian_kreinSelfAdjoint_of_equiv
    (P H : V →L[ℝ] V) (E : ℝ) (hPP : P * P = P)
    (e : LinearMap.ker P.toLinearMap ≃ₗ[ℝ] LinearMap.ker P.toLinearMap)
    (he : e.toLinearMap = NuclearComplementaryResolvent.complementShift
      P.toLinearMap (congrArg ContinuousLinearMap.toLinearMap hPP) H.toLinearMap E)
    (hP : KreinSpace.kreinAdjoint P = P) (hH : KreinSpace.kreinAdjoint H = H) :
    KreinSpace.IsKreinSelfAdjoint
      (NuclearRealKreinFeshbach.effectiveHamiltonian P H (liftInverse P hPP e)) :=
  NuclearRealKreinFeshbach.effectiveHamiltonian_kreinSelfAdjoint
    P H (liftInverse P hPP e) E hP hH
    (complement_mul_liftInverse P hPP e)
    (denominator_mul_liftInverse P H E hPP e he)

end InfoGeometry.Physics.NuclearRealKreinComplementaryResolvent
