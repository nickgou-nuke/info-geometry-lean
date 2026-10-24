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

Uncompiled v4 sandbox candidate against the accepted native real-time owner.
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

namespace InfoGeometry.OperatorAlgebra

open InfoGeometry.Canonical.ModularFlowExponentialGenerator

/-- Normalize native exponential-unitary conjugation on an abstract C⋆ algebra,
before instantiating a dependent represented closure. -/
theorem expUnitary_conjugation_eq_complexPath {A : Type*} [CStarAlgebra A]
    (G : selfAdjoint A) (a : A) (t : ℝ) :
    Unitary.conjStarAlgAut (S := ℂ) (R := A)
        (selfAdjoint.expUnitary (t • G)) a =
      complexExponentialConjugationPath (G : A) a t := by
  have hs : star (G : A) = (G : A) := G.property
  change NormedSpace.exp (Complex.I • (t • (G : A))) * a *
    star (NormedSpace.exp (Complex.I • (t • (G : A)))) = _
  simp [complexExponentialConjugationPath, NormedSpace.star_exp,
    star_smul, hs, smul_comm]

end InfoGeometry.OperatorAlgebra

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
  exact InfoGeometry.OperatorAlgebra.expUnitary_conjugation_eq_complexPath
    (A := (representedCStarClosure Stage sys ω : Type u))
    (matrixGenerator Stage sys ω f H hH) a t


/-- Faithfulness readback across a stage equivalence, proved before specializing
the compatible states or their dependent GNS Hilbert space. -/
theorem representedMatrixStageMap_equiv_injective
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    [∀ i, IsSimpleRing (Stage i)]
    {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
    (i : I) (e : Matrix n n ℂ ≃⋆ₐ[ℂ] Stage i) :
    Function.Injective (representedMatrixStageMap Stage sys ω i e.toStarAlgHom) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  change FilteredGNSAlgebraicColimitRepresentation.algebraicColimitGNSRepresentation
      Stage sys ω (FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i (e a)) =
    FilteredGNSAlgebraicColimitRepresentation.algebraicColimitGNSRepresentation
      Stage sys ω (FilteredStarAlgebraDirectLimit.algebraicStarDirectLimitOf Stage sys i (e b)) at h
  rw [FilteredGNSAlgebraicColimitRepresentation.algebraicColimitGNSRepresentation_of,
    FilteredGNSAlgebraicColimitRepresentation.algebraicColimitGNSRepresentation_of] at h
  exact e.injective (FilteredGNSMatrixFaithfulness.globalStageRepresentation_injective
    Stage sys ω i h)

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

private abbrev motionMatrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun n => (inferInstance : CStarAlgebra (CStarMatrixStage n))
private abbrev motionMatrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun n => (inferInstance : PartialOrder (CStarMatrixStage n))
private abbrev motionMatrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun n => (inferInstance : StarOrderedRing (CStarMatrixStage n))
attribute [local instance] motionMatrixStageCStarFamily motionMatrixStageOrderFamily
  motionMatrixStageStarOrderFamily

private abbrev motionClosureCStar
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
      CStarMatrixStage cstarMatrixInductiveSystem) :
    CStarAlgebra (representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem ω) :=
  representedCStarClosureCStarAlgebra CStarMatrixStage cstarMatrixInductiveSystem ω
private abbrev motionClosureRing
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily
      CStarMatrixStage cstarMatrixInductiveSystem) :
    Ring (representedCStarClosure CStarMatrixStage cstarMatrixInductiveSystem ω) :=
  (motionClosureCStar ω).toNormedRing.toRing
attribute [local instance] motionClosureCStar motionClosureRing

/-- The actual seed-stage map is faithful without a faithfulness input. -/
theorem seedStageHom_injective {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ) :
    Function.Injective (seedStageHom H hH β) := by
  exact representedMatrixStageMap_equiv_injective CStarMatrixStage cstarMatrixInductiveSystem
    (finiteSeedCompatibleStageStates H hH β) k
    (CStarMatrix.ofMatrixStarAlgEquiv : MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k)

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
