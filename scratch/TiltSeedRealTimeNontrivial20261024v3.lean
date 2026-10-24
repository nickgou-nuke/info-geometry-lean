/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FilteredGNSMatrixFaithfulness
import InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
import InfoGeometry.Canonical.ModularFlowExponentialGenerator

/-!
# A moving observable for the actual represented tilt flow

Uncompiled v3 sandbox candidate against the accepted native real-time owner.
For every inverse-temperature parameter and nonzero real tilt, some time moves
the represented switch. No claim is made about every nonzero time.
-/

noncomputable section
open scoped ComplexOrder

namespace InfoGeometry.Canonical.ModularFlowExponentialGenerator

/-- A nonzero commutator prevents the exponential conjugation orbit being constant. -/
theorem exists_complexExponentialConjugationPath_ne
    {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (G x : B) (hc : G * x - x * G ≠ 0) :
    ∃ t : ℝ, complexExponentialConjugationPath G x t ≠ x := by
  by_contra h
  push Not at h
  have heq : complexExponentialConjugationPath G x = fun _ : ℝ => x := funext h
  have hd := hasDerivAt_complexExponentialConjugationPath_zero G x
  rw [heq] at hd
  have hz : Complex.I • (G * x - x * G) = 0 :=
    hd.unique (hasDerivAt_const (0 : ℝ) x)
  exact hc ((smul_eq_zero.mp hz).resolve_left Complex.I_ne_zero)

end InfoGeometry.Canonical.ModularFlowExponentialGenerator

namespace CStarStateColimit.Native.FilteredGNSMatrixRealTime

open FilteredGNSRepresentedCStarClosure FilteredGNSBoundedGeneratorUnitaryFlow
open InfoGeometry.Canonical.ModularFlowExponentialGenerator

universe u

/-- Identify the existing action, including its positive-time sign, with the
native differentiable exponential path. -/
theorem matrixRealTimeAut_eq_complexExponentialConjugationPath
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω : Type u))
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (a : (representedCStarClosure Stage sys ω : Type u)) (t : ℝ) :
    matrixRealTimeAut Stage sys ω f H hH t a =
      complexExponentialConjugationPath (f H) a t := by
  have hs : star (f H) = f H := matrixImage_selfAdjoint Stage sys ω f H hH
  change NormedSpace.exp (Complex.I • (t • f H)) * a *
    star (NormedSpace.exp (Complex.I • (t • f H))) = _
  simp [complexExponentialConjugationPath, NormedSpace.star_exp,
    star_smul, hs, smul_comm]

end CStarStateColimit.Native.FilteredGNSMatrixRealTime

namespace InfoGeometry.Canonical.FiniteSeedRepresentedRealTime

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSHilbertColimit
open CStarStateColimit.Native.FilteredGNSGlobalStageRepresentation
open CStarStateColimit.Native.FilteredGNSAlgebraicColimitRepresentation
open CStarStateColimit.Native.FilteredGNSMatrixFaithfulness
open CStarStateColimit.Native.FilteredGNSMatrixRealTime
open CStarStateColimit.Native.FilteredGNSRepresentedCStarClosure
open CantorBernoulliCStarMatrixTraceState CuntzMatrixTowerInstantiation
open FiniteMatrixGibbsFunctional ModularFlowExponentialGenerator
open InfoGeometry.Canonical.AlgebraicKMSStateColimit
open InfoGeometry.Physics.KleinBottleSewingExact

/-- The actual seed-stage map is faithful without a faithfulness input. -/
theorem seedStageHom_injective {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    Function.Injective (seedStageHom H hH β) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  change algebraicColimitGNSRepresentation CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β)
      (FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf
        CStarMatrixStage cstarMatrixInductiveSystem k
        (CStarMatrix.ofMatrixStarAlgEquiv a)) =
    algebraicColimitGNSRepresentation CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β)
      (FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf
        CStarMatrixStage cstarMatrixInductiveSystem k
        (CStarMatrix.ofMatrixStarAlgEquiv b)) at h
  rw [algebraicColimitGNSRepresentation_of, algebraicColimitGNSRepresentation_of] at h
  exact CStarMatrix.ofMatrixStarAlgEquiv.injective
    (globalStageRepresentation_injective CStarMatrixStage cstarMatrixInductiveSystem
      (finiteSeedCompatibleStageStates H hH β) k h)

/-- The 01 entry of the finite tilt/switch commutator detects every nonzero tilt. -/
theorem tilt_switch_commutator_ne_zero (h : ℝ) (hh : h ≠ 0) :
    (h • tilt2) * switch2 - switch2 * (h • tilt2) ≠ 0 := by
  intro hz
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hz
  have hc : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  have he' : (2 : ℂ) * (h : ℂ) = 0 := by
    simpa [tilt2, switch2, Matrix.mul_apply, Fin.sum_univ_two,
      RCLike.real_smul_eq_coe_mul, two_mul] using he
  exact (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hc) he'

/-- The finite nonzero commutator remains nonzero in the actual represented closure. -/
theorem tiltSeed_represented_commutator_ne_zero (h β : ℝ) (hh : h ≠ 0) :
    let J := seedStageHom (k := 1) (h • tilt2) (tiltHamiltonian_isHermitian h) β
    J (h • tilt2) * J switch2 - J switch2 * J (h • tilt2) ≠ 0 := by
  dsimp only
  intro hz
  apply tilt_switch_commutator_ne_zero h hh
  apply seedStageHom_injective (k := 1) (h • tilt2) (tiltHamiltonian_isHermitian h) β
  simpa only [map_sub, map_mul, map_zero] using hz

/-- Every nonzero tilt has a moving represented switch, for every β. -/
theorem tiltSeed_exists_realTime_move (h β : ℝ) (hh : h ≠ 0) :
    let J := seedStageHom (k := 1) (h • tilt2) (tiltHamiltonian_isHermitian h) β
    ∃ t : ℝ, seedRealTimeAut (k := 1) (h • tilt2)
      (tiltHamiltonian_isHermitian h) β t (J switch2) ≠ J switch2 := by
  dsimp only
  let J := seedStageHom (k := 1) (h • tilt2) (tiltHamiltonian_isHermitian h) β
  obtain ⟨t, ht⟩ := exists_complexExponentialConjugationPath_ne
    (J (h • tilt2)) (J switch2) (tiltSeed_represented_commutator_ne_zero h β hh)
  refine ⟨t, ?_⟩
  change matrixRealTimeAut CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates (k := 1) (h • tilt2)
      (tiltHamiltonian_isHermitian h) β) J (h • tilt2)
      (tiltHamiltonian_isHermitian h) t (J switch2) ≠ J switch2
  rw [matrixRealTimeAut_eq_complexExponentialConjugationPath]
  exact ht

end InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
