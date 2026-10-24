/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.FiniteSeedRepresentedRealTime
import InfoGeometry.Canonical.ModularFlowExponentialGenerator
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Generic naturality and motion on the existing finite CStarMatrix carrier. -/
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

end InfoGeometry.OperatorAlgebra

namespace InfoGeometry.Canonical.FiniteExponentialMotion

open ModularFlowExponentialGenerator
open CantorBernoulliCStarMatrixTraceState CuntzMatrixTowerInstantiation

/-- Naturality of the existing exponential conjugation path, with continuity explicit. -/
theorem map_complexPath {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    (f : A →ₐ[ℂ] B) (hf : Continuous f) (H x : A) (t : ℝ) :
    f (complexExponentialConjugationPath H x t) =
      complexExponentialConjugationPath (f H) (f x) t := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  let : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℂ B
  have hr (r : ℝ) (z : A) : f (r • z) = r • f z :=
    (f.restrictScalars ℝ).toLinearMap.map_smul r z
  simp only [complexExponentialConjugationPath, map_mul,
    NormedSpace.map_exp f hf, map_neg, hr, map_smul]

variable {k : ℕ}
local notation "E" => (CStarMatrix.ofMatrixStarAlgEquiv :
  MatrixStage k ≃⋆ₐ[ℂ] CStarMatrixStage k)

/-- Finite dimensionality of the native type-copy is transported, not postulated. -/
theorem finiteStage_finiteDimensional : FiniteDimensional ℂ (CStarMatrixStage k) :=
  FiniteDimensional.of_injective (E).symm.toAlgEquiv.toLinearEquiv.toLinearMap (E).symm.injective

/-- Any actual matrix hom, expressed on the native normed finite stage, is continuous. -/
theorem matrixHom_stage_continuous {B : Type*} [CStarAlgebra B]
    (f : MatrixStage k →⋆ₐ[ℂ] B) :
    Continuous (f.comp (E).symm.toStarAlgHom) := by
  let : FiniteDimensional ℂ (CStarMatrixStage k) := finiteStage_finiteDimensional
  exact (f.comp (E).symm.toStarAlgHom).toAlgHom.toLinearMap.continuous_of_finiteDimensional

/-- A finite witness in the existing CStarMatrixStage, independent of any seed state. -/
theorem finiteStage_exists_path_move (H x : MatrixStage k)
    (hc : H*x-x*H ≠ 0) :
    ∃ t : ℝ, complexExponentialConjugationPath (E H) (E x) t ≠ E x := by
  apply exists_complexExponentialConjugationPath_ne
  intro hz
  apply hc
  have hmap : E (H*x-x*H) = E (0 : MatrixStage k) := by
    rw [map_sub, map_mul, map_mul, map_zero]
    exact hz
  have hback := congrArg (fun z : CStarMatrixStage k => (E).symm z) hmap
  simpa only [StarAlgEquiv.symm_apply_apply] using hback

/-- Finite path readback through a hom into any actual CStar algebra. -/
theorem finitePath_map {B : Type*} [CStarAlgebra B]
    (f : MatrixStage k →⋆ₐ[ℂ] B) (H x : MatrixStage k) (t : ℝ) :
    f ((E).symm (complexExponentialConjugationPath (E H) (E x) t)) =
      complexExponentialConjugationPath (f H) (f x) t := by
  have h := map_complexPath (f.comp (E).symm.toStarAlgHom).toAlgHom
    (matrixHom_stage_continuous f) (E H) (E x) t
  change f ((E).symm (complexExponentialConjugationPath (E H) (E x) t)) =
    complexExponentialConjugationPath (f ((E).symm (E H))) (f ((E).symm (E x))) t at h
  simpa only [StarAlgEquiv.symm_apply_apply] using h

end InfoGeometry.Canonical.FiniteExponentialMotion
