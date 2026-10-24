/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteSeedRepresentationFaithfulness
import InfoGeometry.Canonical.ModularFlowExponentialGenerator

/-! Actual represented tilt motion, v11 uncompiled sandbox.
Uses native direct seed faithfulness; no composite readback or transparency changes.
The native faithfulness dependency is awaiting parent final QA. -/
noncomputable section
open scoped ComplexOrder
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000

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
    star (NormedSpace.exp (Complex.I • (t • (G : A)))) =
      NormedSpace.exp (t • (Complex.I • (G : A))) * a *
        NormedSpace.exp (-(t • (Complex.I • (G : A))))
  rw [smul_comm Complex.I t (G : A)]
  simp only [NormedSpace.star_exp, star_smul, Complex.star_def, Complex.conj_I,
    star_trivial, hs, neg_smul, smul_neg]

/-- Map the finite commutator before using multiplication in an abstract target. -/
theorem exists_complexPath_move_of_mapped_commutator
    {A : Type*} [Ring A] [Algebra ℂ A]
    {B : Type*} [CStarAlgebra B] (f : A →ₐ[ℂ] B) (H x : A)
    (hc : f (H * x - x * H) ≠ 0) :
    ∃ t : ℝ, complexExponentialConjugationPath (f H) (f x) t ≠ f x := by
  apply exists_complexExponentialConjugationPath_ne
  simpa only [map_sub, map_mul] using hc

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


/-- Nonzero mapped commutator moves an observable under the existing native action. -/
theorem matrixRealTimeAut_exists_move
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω : Type u))
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (x : Matrix n n ℂ)
    (hc : f (H * x - x * H) ≠ 0) :
    ∃ t : ℝ, matrixRealTimeAut Stage sys ω f H hH t (f x) ≠ f x := by
  obtain ⟨t, ht⟩ :=
    InfoGeometry.OperatorAlgebra.exists_complexPath_move_of_mapped_commutator
      f.toAlgHom H x hc
  refine ⟨t, ?_⟩
  rw [matrixRealTimeAut_eq_complexExponentialConjugationPath]
  exact ht

/-- Resolve injectivity and the zero-map law before specializing the seed state. -/
theorem matrixRealTimeAut_exists_move_of_injective
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
    (Stage : I → Type u) [∀ i, CStarAlgebra (Stage i)]
    [∀ i, PartialOrder (Stage i)] [∀ i, StarOrderedRing (Stage i)]
    (sys : ContinuousStarInductiveSystem Stage)
    (ω : ContinuousStarInductiveSystem.CompatibleStateFamily Stage sys)
    {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ →⋆ₐ[ℂ] (representedCStarClosure Stage sys ω : Type u))
    (hf : Function.Injective f) (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (x : Matrix n n ℂ) (hc : H * x - x * H ≠ 0) :
    ∃ t : ℝ, matrixRealTimeAut Stage sys ω f H hH t (f x) ≠ f x := by
  apply matrixRealTimeAut_exists_move Stage sys ω f H hH x
  intro hz
  apply hc
  exact hf (hz.trans (map_zero f).symm)

end CStarStateColimit.Native.FilteredGNSMatrixRealTime

namespace InfoGeometry.Canonical.FiniteSeedRepresentedRealTime

open CStarStateColimit.Native
open CStarStateColimit.Native.FilteredGNSMatrixRealTime
open CantorBernoulliCStarMatrixTraceState CuntzMatrixTowerInstantiation
open FiniteMatrixGibbsFunctional AlgebraicKMSStateColimit
open InfoGeometry.Physics.KleinBottleSewingExact

private abbrev motionMatrixStageCStarFamily : ∀ n, CStarAlgebra (CStarMatrixStage n) :=
  fun _n => inferInstance
private abbrev motionMatrixStageOrderFamily : ∀ n, PartialOrder (CStarMatrixStage n) :=
  fun _n => inferInstance
private abbrev motionMatrixStageStarOrderFamily : ∀ n, StarOrderedRing (CStarMatrixStage n) :=
  fun _n => inferInstance
attribute [local instance] motionMatrixStageCStarFamily motionMatrixStageOrderFamily
  motionMatrixStageStarOrderFamily

/-- Actual seed flow moves every finite seed observable with nonzero commutator. -/
theorem seedRealTimeAut_exists_move {k : ℕ}
    (H : MatrixStage k) (hH : H.IsHermitian) (β : ℝ)
    (x : MatrixStage k) (hc : H * x - x * H ≠ 0) :
    ∃ t : ℝ, seedRealTimeAut H hH β t (seedStageHom H hH β x) ≠
      seedStageHom H hH β x := by
  exact matrixRealTimeAut_exists_move_of_injective CStarMatrixStage
    cstarMatrixInductiveSystem (finiteSeedCompatibleStageStates H hH β)
    (seedStageHom H hH β)
    (FiniteSeedRepresentationFaithfulness.seedStageHom_injective H hH β)
    H hH x hc

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

/-- Every nonzero tilt has a moving actual represented switch, for every beta. -/
theorem tiltSeed_exists_realTime_move (h β : ℝ) (hh : h ≠ 0) :
    let J := seedStageHom (k := 1) (h • tilt2) (tiltHamiltonian_isHermitian h) β
    ∃ t : ℝ, seedRealTimeAut (k := 1) (h • tilt2)
      (tiltHamiltonian_isHermitian h) β t (J switch2) ≠ J switch2 := by
  exact seedRealTimeAut_exists_move (k := 1) (h • tilt2)
    (tiltHamiltonian_isHermitian h) β switch2 (tilt_switch_commutator_ne_zero h hh)

end InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
