/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.Cl11TraceGNSHilbertColimitBridge
import InfoGeometry.Canonical.RealDoubledBlockOperator
import InfoGeometry.Krein.DoubledSpace

/-!
# Real doubled coordinates for the finite Cl(1,1) GNS standard form

The stage-one Hilbert--Schmidt carrier is `M₂(ℂ)`.  Its underlying real
carrier is identified with two copies of `M₂(ℝ)` by taking entrywise real and
imaginary parts.  The theorems below identify the transported complex
structure and Tomita adjunction on that doubled carrier.  The doubled
Hilbert pairing remains positive; no identification with the indefinite
Krein pairing is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11GNSRealDoubledKreinBridge

open InfoGeometry.Canonical.Cl11TraceGNSHilbertColimitBridge
open InfoGeometry.Canonical.CantorBernoulliCStarMatrixTraceState
open FiniteHestenesHilbertSchmidtStandardForm
open FiniteHestenesTomitaBridge
open InfoGeometry.Krein
open InfoGeometry.Canonical.RealDoubledBlockOperator
open scoped ComplexOrder InnerProductSpace NNReal

local instance cstarMatrixStageRealCFC (n : ℕ) :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrixStage n) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance cstarMatrixStageNonnegSpectrum (n : ℕ) :
    NonnegSpectrumClass ℝ (CStarMatrixStage n) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- Realify a finite Hilbert--Schmidt matrix into its two real matrix
components on the repository's native doubled Hilbert carrier. -/
def realDoubledReadout (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    DoubledSpace (EuclideanSpace ℝ (Fin 2 × Fin 2)) :=
  to_doubled
    ((EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).symm
      (fun ij => (A ij.1 ij.2).re))
    ((EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).symm
      (fun ij => (A ij.1 ij.2).im))

/-- Read the transpose of the real and imaginary matrix components as a
doubled real vector. -/
def realDoubledTranspose (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    DoubledSpace (EuclideanSpace ℝ (Fin 2 × Fin 2)) :=
  to_doubled
    ((EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).symm
      (fun ij => (A ij.2 ij.1).re))
    ((EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).symm
      (fun ij => (A ij.2 ij.1).im))

local notation "RealHS" => EuclideanSpace ℝ (Fin 2 × Fin 2)

private def matrixE01 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

private def matrixE10 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- The concrete real matrix carrier used to represent the GNS coordinates is
noncommutative: the two off-diagonal matrix units multiply in opposite orders
to distinct diagonal projections. -/
theorem realMatrixCarrier_noncommutative :
    matrixE01 * matrixE10 ≠ matrixE10 * matrixE01 := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 0) h
  norm_num [matrixE01, matrixE10, Matrix.mul_apply, Fin.sum_univ_two] at h00

private def realHSCoordinatesMatrix (x : Fin 2 × Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => x (i, j)

private def realHSMatrixEquiv :
    RealHS ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun x i j := x.ofLp (i, j)
  invFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  left_inv x := by
    ext ij
    rfl
  right_inv A := by
    ext i j
    rfl
  map_add' x y := by
    ext i j
    rfl
  map_smul' c x := by
    ext i j
    rfl

/-- Entrywise real part of a finite complex Hilbert--Schmidt matrix. -/
private def realPartMatrix
    (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => (A i j).re

/-- Entrywise imaginary part of a finite complex Hilbert--Schmidt matrix. -/
private def imagPartMatrix
    (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => (A i j).im

/-- The entrywise real part of a matrix product is the difference of the two
real matrix products. Real-part transport through the finite sum uses
Mathlib's continuous linear map `Complex.reCLM`. -/
private theorem realPartMatrix_mul
    (A B : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    realPartMatrix (A * B) =
      realPartMatrix A * realPartMatrix B - imagPartMatrix A * imagPartMatrix B := by
  ext i j
  change Complex.re ((A * B) i j) = _
  rw [Matrix.mul_apply]
  change Complex.re (∑ k, A i k * B k j) = _
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply, Complex.mul_re, Matrix.mul_apply,
    Matrix.sub_apply]
  rw [Finset.sum_sub_distrib]
  simp only [Fin.sum_univ_two]
  simp only [realPartMatrix, imagPartMatrix]

/-- The entrywise imaginary part of a matrix product is the sum of the two
cross real matrix products. Imaginary-part transport through the finite sum
uses Mathlib's continuous linear map `Complex.imCLM`. -/
private theorem imagPartMatrix_mul
    (A B : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    imagPartMatrix (A * B) =
      realPartMatrix A * imagPartMatrix B + imagPartMatrix A * realPartMatrix B := by
  ext i j
  change Complex.im ((A * B) i j) = _
  rw [Matrix.mul_apply]
  change Complex.im (∑ k, A i k * B k j) = _
  rw [← Complex.imCLM_apply, map_sum]
  simp only [Complex.imCLM_apply, Complex.mul_im, Matrix.mul_apply,
    Matrix.add_apply]
  simp only [Fin.sum_univ_two]
  simp only [realPartMatrix, imagPartMatrix]
  abel

/-- Readout in the matrix coordinates induced by `realHSMatrixEquiv`. -/
private theorem realDoubledReadout_components
    (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    realDoubledReadout A =
      to_doubled (realHSMatrixEquiv.symm (realPartMatrix A))
        (realHSMatrixEquiv.symm (imagPartMatrix A)) := by
  apply DoubledSpace.ext
  · apply (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).injective
    funext ij
    simp [realDoubledReadout, realPartMatrix, realHSMatrixEquiv,
      to_doubled, EuclideanSpace.equiv]
  · apply (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).injective
    funext ij
    simp [realDoubledReadout, imagPartMatrix, realHSMatrixEquiv,
      to_doubled, EuclideanSpace.equiv]

/-- The real matrix acting on the real coordinates of the Hilbert--Schmidt
carrier by left multiplication. -/
def realMatrixLeftAction (A : Matrix (Fin 2) (Fin 2) ℝ) :
    RealHS →L[ℝ] RealHS :=
  LinearMap.toContinuousLinearMap
    (realHSMatrixEquiv.symm.toLinearMap.comp
      ((LinearMap.mulLeft ℝ A).comp realHSMatrixEquiv.toLinearMap))

/-- The real matrix acting on the real coordinates of the Hilbert--Schmidt
carrier by right multiplication. -/
def realMatrixRightAction (A : Matrix (Fin 2) (Fin 2) ℝ) :
    RealHS →L[ℝ] RealHS :=
  LinearMap.toContinuousLinearMap
    (realHSMatrixEquiv.symm.toLinearMap.comp
      ((LinearMap.mulRight ℝ A).comp realHSMatrixEquiv.toLinearMap))

/-- The operator-valued real block action induced by complex left
multiplication on the Hilbert--Schmidt matrices. -/
def realDoubledLeftAction
    (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    DoubledSpace RealHS →L[ℝ] DoubledSpace RealHS :=
  realDoubledBlockOperator
    (realMatrixLeftAction (realPartMatrix A))
    (-(realMatrixLeftAction (imagPartMatrix A)))
    (realMatrixLeftAction (imagPartMatrix A))
    (realMatrixLeftAction (realPartMatrix A))

/-- The operator-valued real block action induced by complex right
multiplication on the Hilbert--Schmidt matrices. -/
def realDoubledRightAction
    (B : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    DoubledSpace RealHS →L[ℝ] DoubledSpace RealHS :=
  realDoubledBlockOperator
    (realMatrixRightAction (realPartMatrix B))
    (-(realMatrixRightAction (imagPartMatrix B)))
    (realMatrixRightAction (imagPartMatrix B))
    (realMatrixRightAction (realPartMatrix B))

@[simp] theorem realMatrixLeftAction_apply
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : RealHS) :
    realMatrixLeftAction A x = realHSMatrixEquiv.symm
      (A * realHSMatrixEquiv x) := by
  rfl

@[simp] theorem realMatrixRightAction_apply
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : RealHS) :
    realMatrixRightAction A x = realHSMatrixEquiv.symm
      (realHSMatrixEquiv x * A) := by
  rfl

private theorem realMatrixLeftAction_readout
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : RealHS) :
    realHSMatrixEquiv (realMatrixLeftAction A x) =
      A * realHSMatrixEquiv x := by
  rw [realMatrixLeftAction_apply]
  exact realHSMatrixEquiv.apply_symm_apply _

private theorem realMatrixRightAction_readout
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : RealHS) :
    realHSMatrixEquiv (realMatrixRightAction A x) =
      realHSMatrixEquiv x * A := by
  rw [realMatrixRightAction_apply]
  exact realHSMatrixEquiv.apply_symm_apply _

private theorem realMatrixLeftAction_neg_readout
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : RealHS) :
    realHSMatrixEquiv ((-realMatrixLeftAction A) x) =
      -(A * realHSMatrixEquiv x) := by
  simp

private theorem realMatrixRightAction_neg_readout
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : RealHS) :
    realHSMatrixEquiv ((-realMatrixRightAction A) x) =
      -(realHSMatrixEquiv x * A) := by
  simp

@[simp] private theorem realHSMatrixEquiv_toLp
    (x : Fin 2 × Fin 2 → ℝ) :
    realHSMatrixEquiv (WithLp.toLp 2 x) = fun i j => x (i, j) := by
  ext i j
  rfl

@[simp] private theorem realHSMatrixEquiv_symm_entry
    (A : Matrix (Fin 2) (Fin 2) ℝ) (ij : Fin 2 × Fin 2) :
    (realHSMatrixEquiv.symm A).ofLp ij = A ij.1 ij.2 := rfl

@[simp] private theorem realMatrixLeftAction_entry
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : RealHS) (ij : Fin 2 × Fin 2) :
    (realMatrixLeftAction A x).ofLp ij =
      (A * realHSMatrixEquiv x) ij.1 ij.2 := by
  rw [realMatrixLeftAction_apply]
  rfl

@[simp] private theorem realMatrixRightAction_entry
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : RealHS) (ij : Fin 2 × Fin 2) :
    (realMatrixRightAction A x).ofLp ij =
      (realHSMatrixEquiv x * A) ij.1 ij.2 := by
  rw [realMatrixRightAction_apply]
  rfl

@[simp] private theorem realMatrixLeftAction_toLp_entry
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 × Fin 2 → ℝ)
    (ij : Fin 2 × Fin 2) :
    (realMatrixLeftAction A (WithLp.toLp 2 x)).ofLp ij =
      (A * realHSCoordinatesMatrix x) ij.1 ij.2 := by
  rw [realMatrixLeftAction_entry]
  rfl

@[simp] private theorem neg_realMatrixLeftAction_toLp_entry
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 × Fin 2 → ℝ)
    (ij : Fin 2 × Fin 2) :
    ((-realMatrixLeftAction A) (WithLp.toLp 2 x)).ofLp ij =
      -((A * realHSCoordinatesMatrix x) ij.1 ij.2) := by
  simp only [neg_apply, WithLp.ofLp_neg, Pi.neg_apply,
    realMatrixLeftAction_toLp_entry]

@[simp] private theorem realMatrixRightAction_toLp_entry
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 × Fin 2 → ℝ)
    (ij : Fin 2 × Fin 2) :
    (realMatrixRightAction A (WithLp.toLp 2 x)).ofLp ij =
      (realHSCoordinatesMatrix x * A) ij.1 ij.2 := by
  rw [realMatrixRightAction_entry]
  rfl

@[simp] private theorem neg_realMatrixRightAction_toLp_entry
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 × Fin 2 → ℝ)
    (ij : Fin 2 × Fin 2) :
    ((-realMatrixRightAction A) (WithLp.toLp 2 x)).ofLp ij =
      -((realHSCoordinatesMatrix x * A) ij.1 ij.2) := by
  simp only [neg_apply, WithLp.ofLp_neg, Pi.neg_apply,
    realMatrixRightAction_toLp_entry]

theorem realDoubledReadout_add
    (A B : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    realDoubledReadout (A + B) =
      realDoubledReadout A + realDoubledReadout B := by
  apply DoubledSpace.ext <;>
    apply (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).injective <;>
    funext ij <;> simp [realDoubledReadout, to_doubled, Complex.add_re,
      Complex.add_im, EuclideanSpace.equiv]

theorem realDoubledReadout_real_smul (r : ℝ)
    (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    realDoubledReadout ((r : ℂ) • A) =
      r • realDoubledReadout A := by
  apply DoubledSpace.ext <;>
    apply (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).injective <;>
    funext ij <;> simp [realDoubledReadout, to_doubled, Matrix.smul_apply,
      Complex.mul_re, Complex.mul_im, EuclideanSpace.equiv]

/-- Multiplication by `Complex.I` on the Hilbert--Schmidt carrier is the
canonical quarter-turn on its real doubled coordinates. -/
theorem realDoubledReadout_complexI
    (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    realDoubledReadout ((Complex.I : ℂ) • A) =
      complex_i (realDoubledReadout A) := by
  apply DoubledSpace.ext <;>
    apply (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).injective <;>
    funext ij <;> simp [realDoubledReadout, complex_i, modular_j,
      spectral_epsilon, to_doubled, Matrix.smul_apply, Complex.I_mul,
      EuclideanSpace.equiv]

/-- The real doubled readout is injective. -/
theorem realDoubledReadout_injective :
    Function.Injective realDoubledReadout := by
  intro A B h
  have hre := congrArg WithLp.fst h
  have him := congrArg WithLp.snd h
  ext i j
  apply Complex.ext
  ·
    have hcoord := congrArg (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ) hre
    have he := congrFun hcoord (i, j)
    simpa [realDoubledReadout, to_doubled, EuclideanSpace.equiv] using he
  ·
    have hcoord := congrArg (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ) him
    have he := congrFun hcoord (i, j)
    simpa [realDoubledReadout, to_doubled, EuclideanSpace.equiv] using he

/-- Every pair of real stage-one coordinate vectors is the realification of
a complex Hilbert--Schmidt matrix. -/
theorem realDoubledReadout_surjective :
    Function.Surjective realDoubledReadout := by
  intro u
  refine ⟨fun i j =>
    ⟨(EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ (WithLp.fst u)) (i, j),
      (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ (WithLp.snd u)) (i, j)⟩, ?_⟩
  apply DoubledSpace.ext <;>
    apply (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).injective <;>
    funext ij <;> simp [realDoubledReadout, to_doubled, EuclideanSpace.equiv]

/-- The real and imaginary parts of matrix Tomita adjunction are respectively
the transposes of the real part and the negative transpose of the imaginary
part.  The minus sign is exactly the negative Krein sheet sign `ε`. -/
theorem realDoubledReadout_matrixTomita
    (A : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    realDoubledReadout (matrixTomita A) =
      spectral_epsilon (realDoubledTranspose A) := by
  apply DoubledSpace.ext <;>
    apply (EuclideanSpace.equiv (Fin 2 × Fin 2) ℝ).injective <;>
    funext ij <;>
    simp [realDoubledReadout, realDoubledTranspose, matrixTomita,
      Matrix.conjTranspose_apply, spectral_epsilon, to_doubled,
      Complex.conj_re, Complex.conj_im, EuclideanSpace.equiv]

/-- The real Hilbert--Schmidt inner product is exactly the positive doubled
Hilbert pairing on real and imaginary coordinates.  This does not identify it
with the distinct indefinite pairing defined by the native `KreinSpace`
fundamental symmetry. -/
theorem realPart_hilbertSchmidtInner_eq_doubledHilbertBilin
    (A B : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    (hilbertSchmidtInner A B).re =
      doubledHilbertBilin (realDoubledReadout A) (realDoubledReadout B) := by
  simp [hilbertSchmidtInner, realDoubledReadout, doubledHilbertBilin,
    to_doubled, EuclideanSpace.equiv, PiLp.inner_apply, WithLp.prod_inner_apply,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp_rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- The finite pre-GNS inner product, after taking its real part, is exactly
the positive Hilbert pairing of the two realified standard-form vectors. -/
theorem preGNS_realPart_inner_eq_doubledHilbertBilin
    (x y : (cstarMatrixTraceState 1).functional.PreGNS) :
    (inner ℂ x y).re =
      doubledHilbertBilin
        (realDoubledReadout (stageOnePreGNSHilbertSchmidtReadout x))
        (realDoubledReadout (stageOnePreGNSHilbertSchmidtReadout y)) := by
  rw [← stageOnePreGNSHilbertSchmidtReadout_inner]
  exact realPart_hilbertSchmidtInner_eq_doubledHilbertBilin
    (stageOnePreGNSHilbertSchmidtReadout x)
    (stageOnePreGNSHilbertSchmidtReadout y)

/-- On the actual stage-one pre-GNS core, the doubled realification of
matrix Tomita agrees with realification of the star-transformed GNS vector. -/
theorem realDoubledReadout_preGNS_tomita
    (x : (cstarMatrixTraceState 1).functional.PreGNS) :
    realDoubledReadout
        (matrixTomita (stageOnePreGNSHilbertSchmidtReadout x)) =
      realDoubledReadout
        (stageOnePreGNSHilbertSchmidtReadout
          ((cstarMatrixTraceState 1).functional.toPreGNS
            (star ((cstarMatrixTraceState 1).functional.ofPreGNS x)))) := by
  rw [stageOnePreGNSHilbertSchmidtReadout_tomita]
  rfl

/-- The actual finite glide/Tomita commutation theorem transported to the
native real doubled carrier.  This is still a stage-one algebraic-core result;
it does not identify the affine base translation with a fibre operator. -/
theorem realDoubledReadout_preGNS_tomita_glide
    (A : CStarMatrixStage 1) :
    realDoubledReadout
        (matrixTomita
          (stageOnePreGNSHilbertSchmidtReadout
            ((cstarMatrixTraceState 1).functional.toPreGNS
              (cl11GlideImplementer * A * cl11GlideImplementer)))) =
      realDoubledReadout
        (stageOnePreGNSHilbertSchmidtReadout
          ((cstarMatrixTraceState 1).functional.toPreGNS
            (cl11GlideImplementer * star A * cl11GlideImplementer))) := by
  exact congrArg realDoubledReadout
    (stageOnePreGNSHilbertSchmidtReadout_tomita_glide A)

/-- The real operator-block action on the doubled carrier is exactly the
realification of the Hilbert--Schmidt left regular action. -/
theorem realDoubledLeftAction_readout
    (A X : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    realDoubledLeftAction A (realDoubledReadout X) =
      realDoubledReadout (leftActionLinear A X) := by
  rw [realDoubledReadout_components, realDoubledReadout_components]
  simp only [realDoubledLeftAction, realDoubledBlockOperator_apply]
  apply DoubledSpace.ext
  · apply realHSMatrixEquiv.injective
    simp only [fst_to_doubled, map_add, realHSMatrixEquiv.apply_symm_apply,
      realMatrixLeftAction_readout, realMatrixLeftAction_neg_readout,
      leftActionLinear_apply]
    exact (realPartMatrix_mul A X).symm
  · apply realHSMatrixEquiv.injective
    simp only [snd_to_doubled, map_add, realHSMatrixEquiv.apply_symm_apply,
      realMatrixLeftAction_readout, leftActionLinear_apply]
    rw [imagPartMatrix_mul]
    abel

/-- The real operator-block action on the doubled carrier is exactly the
realification of the Hilbert--Schmidt right regular action. -/
theorem realDoubledRightAction_readout
    (B X : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    realDoubledRightAction B (realDoubledReadout X) =
      realDoubledReadout (rightActionLinear B X) := by
  rw [realDoubledReadout_components, realDoubledReadout_components]
  simp only [realDoubledRightAction, realDoubledBlockOperator_apply]
  apply DoubledSpace.ext
  · apply realHSMatrixEquiv.injective
    simp only [fst_to_doubled, map_add, realHSMatrixEquiv.apply_symm_apply,
      realMatrixRightAction_readout, realMatrixRightAction_neg_readout,
      rightActionLinear_apply]
    exact (realPartMatrix_mul X B).symm
  · apply realHSMatrixEquiv.injective
    simp only [snd_to_doubled, map_add, realHSMatrixEquiv.apply_symm_apply,
      realMatrixRightAction_readout, rightActionLinear_apply]
    rw [imagPartMatrix_mul]

/-- The doubled real action of the standard-form left/right pair commutes,
because it is conjugate to the commuting Hilbert--Schmidt regular actions. -/
theorem realDoubledLeftRightAction_commute
    (A B : FiniteHestenesHilbertSchmidtStandardForm.HS2) :
    (realDoubledLeftAction A).comp (realDoubledRightAction B) =
      (realDoubledRightAction B).comp (realDoubledLeftAction A) := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨X, rfl⟩ := realDoubledReadout_surjective x
  rw [ContinuousLinearMap.comp_apply, realDoubledRightAction_readout,
    realDoubledLeftAction_readout, ContinuousLinearMap.comp_apply,
    realDoubledLeftAction_readout, realDoubledRightAction_readout]
  simp [leftActionLinear_apply, rightActionLinear_apply, Matrix.mul_assoc]

/-- The finite `Cl(1,1)` glide acts on the real doubled GNS core through the
operator-valued left/right regular actions.  This is an intertwining theorem
for the actual doubled-carrier operators, not only an equality of readouts. -/
theorem realDoubledReadout_preGNS_glide_left_right
    (a : CliffordAlgebra InfoGeometry.Clifford.Cl11Matrix.q11) :
    realDoubledLeftAction
        ((CStarMatrix.ofMatrixStarAlgEquiv).symm cl11GlideImplementer)
        (realDoubledRightAction
          ((CStarMatrix.ofMatrixStarAlgEquiv).symm cl11GlideImplementer)
          (realDoubledReadout
            (stageOnePreGNSHilbertSchmidtReadout
              ((cstarMatrixTraceState 1).functional.toPreGNS
                (cl11FiberToCStarStageOne a))))) =
      realDoubledReadout
        (stageOnePreGNSHilbertSchmidtReadout
          ((cstarMatrixTraceState 1).functional.toPreGNS
            (cl11FiberToCStarStageOne
              (InfoGeometry.Clifford.Cl11Matrix.splitReflectionCliffordAuto a)))) := by
  rw [realDoubledRightAction_readout, realDoubledLeftAction_readout]
  exact (congrArg realDoubledReadout
    (stageOnePreGNSHilbertSchmidtReadout_glide a)).symm

/-- On the real doubled coordinates of the finite stage-one GNS core, the
Krein sheet sign applied to the transpose of the glide-transformed vector is
the realification of the Tomita-transformed glide vector.  This makes the
finite glide, left/right standard-form action, and Tomita sheet-sign
compatibility explicit on the same carrier. -/
theorem realDoubledReadout_preGNS_glide_tomita_sheet_sign
    (A : CStarMatrixStage 1) :
    spectral_epsilon
        (realDoubledTranspose
          (stageOnePreGNSHilbertSchmidtReadout
            ((cstarMatrixTraceState 1).functional.toPreGNS
              (cl11GlideImplementer * A * cl11GlideImplementer)))) =
      realDoubledReadout
        (stageOnePreGNSHilbertSchmidtReadout
          ((cstarMatrixTraceState 1).functional.toPreGNS
            (cl11GlideImplementer * star A * cl11GlideImplementer))) := by
  rw [← realDoubledReadout_matrixTomita]
  exact congrArg realDoubledReadout
    (stageOnePreGNSHilbertSchmidtReadout_tomita_glide A)

end InfoGeometry.Canonical.Cl11GNSRealDoubledKreinBridge

end noncomputable section
