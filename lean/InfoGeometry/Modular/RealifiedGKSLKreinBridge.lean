/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.KreinFlowConservation
import InfoGeometry.Modular.RealifiedSchrodingerGKSL
import InfoGeometry.Modular.SchrodingerGKSLFlowBridge
import InfoGeometry.Modular.CommutantInvariantGKSLFlow
import InfoGeometry.Modular.NESSCommutantPotentialLeaves
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Hilbert-coordinate realization of the finite matrix GKSL operator on a Krein double

The full complex matrix algebra is represented by its entries in Mathlib's
finite-dimensional complex Euclidean Hilbert space. An explicit linear
isomorphism retains the matrix-algebra action; the Krein pairing is the signed
inner product on the two real sheets.
-/

noncomputable section

namespace InfoGeometry.Modular.RealifiedGKSLKreinBridge

open Matrix
open Filter Topology
open scoped InnerProductSpace Matrix.Norms.L2Operator
open InfoGeometry.Krein
open InfoGeometry.Modular.SchrodingerGKSLFlowBridge
open InfoGeometry.Modular.RealifiedSchrodingerGKSL
open InfoGeometry.Quantum.Realification

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

local notation "CMat" => Matrix n n ℂ
local notation "RMat" => Matrix (n ⊕ n) (n ⊕ n) ℝ
local notation "OpHilbert" => EuclideanSpace ℂ (n × n)
local notation "DOp" => DoubledSpace OpHilbert

/-- Encode a full complex matrix as its entry vector in the Euclidean space. -/
def matrixToOperatorHilbert (A : CMat) : OpHilbert :=
  WithLp.toLp 2 (fun ij : n × n => A ij.1 ij.2)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixToOperatorHilbert_add (A B : CMat) :
    matrixToOperatorHilbert (A + B) =
      matrixToOperatorHilbert A + matrixToOperatorHilbert B := by
  apply WithLp.ofLp_injective
  funext ij
  rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixToOperatorHilbert_sub (A B : CMat) :
    matrixToOperatorHilbert (A - B) =
      matrixToOperatorHilbert A - matrixToOperatorHilbert B := by
  apply WithLp.ofLp_injective
  funext ij
  rfl

omit [Fintype n] [DecidableEq n] in
theorem matrixToOperatorHilbert_sum (f : ι → CMat) :
    matrixToOperatorHilbert (∑ k, f k) = ∑ k, matrixToOperatorHilbert (f k) := by
  apply WithLp.ofLp_injective
  funext ij
  simp [matrixToOperatorHilbert, Matrix.sum_apply]

/-- Read the full matrix represented by an entry vector. -/
def operatorHilbertToMatrix (X : OpHilbert) : CMat :=
  fun i j => WithLp.ofLp X (i, j)

def matrixOperatorEquiv : CMat ≃ₗ[ℂ] OpHilbert where
  toFun := matrixToOperatorHilbert
  invFun := operatorHilbertToMatrix
  left_inv A := by ext i j; rfl
  right_inv X := by
    apply WithLp.ofLp_injective
    funext ij
    rfl
  map_add' A B := by
    apply WithLp.ofLp_injective
    funext ij
    rfl
  map_smul' c A := by
    apply WithLp.ofLp_injective
    funext ij
    rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem operatorHilbertToMatrix_matrixToOperatorHilbert (A : CMat) :
    operatorHilbertToMatrix (matrixToOperatorHilbert A) = A := by
  ext i j
  rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem matrixToOperatorHilbert_operatorHilbertToMatrix (X : OpHilbert) :
    matrixToOperatorHilbert (operatorHilbertToMatrix X) = X := by
  apply WithLp.ofLp_injective
  funext ij
  rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem operatorHilbertToMatrix_add (X Y : OpHilbert) :
    operatorHilbertToMatrix (X + Y) =
      operatorHilbertToMatrix X + operatorHilbertToMatrix Y := by
  ext i j
  rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem operatorHilbertToMatrix_smul (r : ℝ) (X : OpHilbert) :
    operatorHilbertToMatrix (r • X) =
      r • operatorHilbertToMatrix X := by
  ext i j
  rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem operatorHilbertToMatrix_sub (X Y : OpHilbert) :
    operatorHilbertToMatrix (X - Y) =
      operatorHilbertToMatrix X - operatorHilbertToMatrix Y := by
  ext i j
  rfl

/-- The matrix GKSL generator transported to the Euclidean operator carrier.
Only the carrier changes; the ordered products in generatorCLM are retained. -/
def schrodingerOperatorLinear (H : CMat) (V : ι → CMat) :
    OpHilbert →ₗ[ℝ] OpHilbert :=
  (matrixOperatorEquiv.toLinearMap.restrictScalars ℝ).comp
    (((generatorCLM H V).toLinearMap.restrictScalars ℝ).comp
      (matrixOperatorEquiv.symm.toLinearMap.restrictScalars ℝ))

/-- The transported GKSL operator is continuous on the finite-dimensional
real Hilbert space of matrix entries. -/
def schrodingerOperatorCLM (H : CMat) (V : ι → CMat) :
    OpHilbert →L[ℝ] OpHilbert where
  toLinearMap := schrodingerOperatorLinear H V
  cont := LinearMap.continuous_of_finiteDimensional _

/-- Heisenberg dual of the Hamiltonian commutator, with no self-adjointness
assumption on the generator. -/
def heisenbergHamiltonianTerm (H A : CMat) : CMat :=
  Complex.I • (star H * A - A * star H)

/-- Heisenberg dual of one Schrödinger jump dissipator. -/
def heisenbergDissipatorTerm (V A : CMat) : CMat :=
  star V * A * V -
    (1 / 2 : ℂ) • (star V * V * A + A * star V * V)

/-- Heisenberg-picture dual of the repository's Schrödinger GKSL generator.
The Hamiltonian is not assumed self-adjoint, so its adjoint appears explicitly.
All products retain their matrix order. -/
def heisenbergLindbladian (H : CMat) (V : ι → CMat) (A : CMat) : CMat :=
  heisenbergHamiltonianTerm H A +
    ∑ k, heisenbergDissipatorTerm (V k) A

/-- The full matrix Heisenberg GKSL generator annihilates the identity.
This is the matrix-level unitality consequence for an arbitrary finite jump
family, complementing the specialized two-dimensional thermal identities. -/
@[simp] theorem heisenbergLindbladian_one (H : CMat) (V : ι → CMat) :
    heisenbergLindbladian H V 1 = 0 := by
  have hterm (W : CMat) : heisenbergDissipatorTerm W 1 = 0 := by
    ext i j
    simp [heisenbergDissipatorTerm, Matrix.mul_apply, smul_eq_mul]
    ring
  simp [heisenbergLindbladian, heisenbergHamiltonianTerm, hterm]

/-- Complex-linear realization of the Heisenberg dual, assembled from actual
left and right multiplication operators on the matrix algebra. -/
def heisenbergGeneratorCLM (H : CMat) (V : ι → CMat) : CMat →L[ℂ] CMat :=
  Complex.I • (leftMul (star H) - rightMul (star H)) +
    ∑ k, ((leftMul (star (V k))).comp (rightMul (V k)) -
      (1 / 2 : ℂ) •
        (leftMul (star (V k) * V k) + rightMul (star (V k) * V k)))

@[simp] theorem heisenbergGeneratorCLM_apply (H A : CMat) (V : ι → CMat) :
    heisenbergGeneratorCLM H V A = heisenbergLindbladian H V A := by
  simp [heisenbergGeneratorCLM, heisenbergLindbladian, leftMul, rightMul,
    heisenbergHamiltonianTerm, heisenbergDissipatorTerm,
    ContinuousLinearMap.comp_apply, mul_assoc]

@[simp] theorem operatorHilbertToMatrix_generator (H : CMat) (V : ι → CMat)
    (X : OpHilbert) :
    operatorHilbertToMatrix (schrodingerOperatorCLM H V X) =
      InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V
        (operatorHilbertToMatrix X) := by
  simp [schrodingerOperatorCLM, schrodingerOperatorLinear,
    matrixOperatorEquiv, generatorCLM_apply]

@[simp] theorem matrixToOperatorHilbert_generator (H : CMat) (V : ι → CMat)
    (X : CMat) :
    schrodingerOperatorCLM H V (matrixToOperatorHilbert X) =
      matrixToOperatorHilbert
        (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V X) := by
  rw [← matrixToOperatorHilbert_operatorHilbertToMatrix
    (schrodingerOperatorCLM H V (matrixToOperatorHilbert X))]
  simpa only [operatorHilbertToMatrix_matrixToOperatorHilbert] using
    congrArg matrixToOperatorHilbert
      (operatorHilbertToMatrix_generator H V (matrixToOperatorHilbert X))

/-- Realification as a continuous real-linear map, for transporting the
matrix GKSL orbit derivative to the phase-double matrix carrier. -/
def realifyCLM : CMat →L[ℝ] RMat where
  toLinearMap := realifyLinearMap
  cont := LinearMap.continuous_of_finiteDimensional _

/-- The real phase-double matrix obtained from the finite-matrix GKSL orbit
satisfies the phase-double Schrödinger equation. The matrix products and
Hamiltonian/jump terms are inherited from the existing complex GKSL owner. -/
theorem realified_gkslFlow_orbit (H : CMat) (V : ι → CMat)
    (X : CMat) (t : ℝ) :
    HasDerivAt (fun s : ℝ => realify (gkslFlow H V s X))
      (realifiedSchrodingerLindbladian H V (gkslFlow H V t X)) t := by
  have hflow := hasDerivAt_gkslFlow_orbit H V X t
  have hcomp := (realifyCLM (n := n)).hasFDerivAt.comp_hasDerivAt t hflow
  simpa [Function.comp_def, realifyCLM, realifyLinearMap,
    realify_schrodingerLindbladian] using hcomp

/-- The matrix-to-operator encoding as a continuous real-linear map. -/
def matrixToOperatorCLM : CMat →L[ℝ] OpHilbert where
  toLinearMap := matrixOperatorEquiv.toLinearMap.restrictScalars ℝ
  cont := LinearMap.continuous_of_finiteDimensional _

/-- The inverse operator-to-matrix encoding as a continuous real-linear map. -/
def operatorToMatrixCLM : OpHilbert →L[ℝ] CMat where
  toLinearMap := matrixOperatorEquiv.symm.toLinearMap.restrictScalars ℝ
  cont := LinearMap.continuous_of_finiteDimensional _

/-- Heisenberg generator on the full matrix-entry real Hilbert space, obtained
by transporting its matrix-algebra realization through the existing linear
equivalence. -/
def heisenbergOperatorCLM (H : CMat) (V : ι → CMat) :
    OpHilbert →L[ℝ] OpHilbert :=
  (matrixToOperatorCLM (n := n)).comp
    ((heisenbergGeneratorCLM H V).restrictScalars ℝ |>.comp
      (operatorToMatrixCLM (n := n)))

@[simp] theorem operatorHilbertToMatrix_heisenbergGenerator (H : CMat)
    (V : ι → CMat) (X : OpHilbert) :
    operatorHilbertToMatrix (heisenbergOperatorCLM H V X) =
      heisenbergLindbladian H V (operatorHilbertToMatrix X) := by
  simp [heisenbergOperatorCLM, matrixToOperatorCLM, operatorToMatrixCLM,
    matrixOperatorEquiv, heisenbergGeneratorCLM_apply]

@[simp] theorem matrixToOperatorHilbert_heisenbergGenerator (H : CMat)
    (V : ι → CMat) (X : CMat) :
    heisenbergOperatorCLM H V (matrixToOperatorHilbert X) =
      matrixToOperatorHilbert (heisenbergLindbladian H V X) := by
  rw [← matrixToOperatorHilbert_operatorHilbertToMatrix
    (heisenbergOperatorCLM H V (matrixToOperatorHilbert X))]
  simpa only [operatorHilbertToMatrix_matrixToOperatorHilbert] using
    congrArg matrixToOperatorHilbert
      (operatorHilbertToMatrix_heisenbergGenerator H V (matrixToOperatorHilbert X))

/-- The transported Heisenberg generator is unital on the full operator
matrix space. -/
@[simp] theorem heisenbergOperatorCLM_one (H : CMat) (V : ι → CMat) :
    heisenbergOperatorCLM H V (matrixToOperatorHilbert (1 : CMat)) = 0 := by
  rw [matrixToOperatorHilbert_heisenbergGenerator, heisenbergLindbladian_one]
  exact map_zero matrixOperatorEquiv.toLinearMap

/-- Left multiplication by a matrix, transported to the full matrix-entry
Hilbert space. The action remains multiplication in `Matrix n n ℂ`; only its
carrier is represented by Euclidean coordinates. -/
def matrixLeftActionLinear (A : CMat) : OpHilbert →ₗ[ℝ] OpHilbert :=
  (matrixOperatorEquiv.toLinearMap.restrictScalars ℝ).comp
    (((LinearMap.mulLeft ℂ A).restrictScalars ℝ).comp
      (matrixOperatorEquiv.symm.toLinearMap.restrictScalars ℝ))

/-- The finite-dimensional matrix left action is continuous on the
realified entry-Hilbert carrier. -/
def matrixLeftActionCLM (A : CMat) : OpHilbert →L[ℝ] OpHilbert where
  toLinearMap := matrixLeftActionLinear A
  cont := LinearMap.continuous_of_finiteDimensional _

/-- Right multiplication by a matrix, transported to the same full matrix-entry
Hilbert space. -/
def matrixRightActionCLM (A : CMat) : OpHilbert →L[ℝ] OpHilbert where
  toLinearMap := (matrixOperatorEquiv.toLinearMap.restrictScalars ℝ).comp
    (((LinearMap.mulRight ℂ A).restrictScalars ℝ).comp
      (matrixOperatorEquiv.symm.toLinearMap.restrictScalars ℝ))
  cont := LinearMap.continuous_of_finiteDimensional _

@[simp] theorem matrixLeftActionCLM_apply (A : CMat) (X : OpHilbert) :
    matrixLeftActionCLM A X = matrixToOperatorHilbert (A * operatorHilbertToMatrix X) := by
  simp [matrixLeftActionCLM, matrixLeftActionLinear, matrixOperatorEquiv]

@[simp] theorem matrixRightActionCLM_apply (A : CMat) (X : OpHilbert) :
    matrixRightActionCLM A X = matrixToOperatorHilbert (operatorHilbertToMatrix X * A) := by
  simp [matrixRightActionCLM, matrixOperatorEquiv]

/-- Riesz representative, on the full matrix-entry Hilbert space, of the
existing real commutant readout `Re Tr(QX)`. This uses the established NESS
readout CLM rather than introducing a second trace functional. -/
def commutantReadoutRieszVector (Q : CMat) : OpHilbert :=
  ContinuousLinearMap.adjoint
    ((InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q).comp
      (operatorToMatrixCLM (n := n))) 1

/-- Hilbert-space Riesz representation of the existing full-matrix NESS
readout after the matrix/operator-coordinate equivalence. -/
theorem commutantReadoutRieszVector_pairing (Q X : CMat) :
    inner ℝ (commutantReadoutRieszVector Q) (matrixToOperatorHilbert X) =
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q X := by
  rw [commutantReadoutRieszVector, ContinuousLinearMap.adjoint_inner_left]
  simp [operatorToMatrixCLM, matrixOperatorEquiv,
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM_apply]

/-- The full-entry real Hilbert pairing against the encoded adjoint observable
is the existing real matrix-trace readout. This pins the Riesz vector to the
noncommutative matrix adjoint, with the repository's trace-order convention. -/
theorem matrixToOperatorHilbert_star_pairing (Q X : CMat) :
    inner ℝ (matrixToOperatorHilbert (star Q)) (matrixToOperatorHilbert X) =
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q X := by
  rw [PiLp.inner_apply]
  simp only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply,
    matrixToOperatorHilbert, WithLp.ofLp_toLp, Matrix.star_apply,
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply]
  change (∑ p : n × n, Complex.re
      (X p.1 p.2 * star (star (Q p.2 p.1)))) =
    (∑ i : n, ∑ j : n, Q i j * X j i).re
  simp only [star_star]
  have hsum :
      (∑ p : n × n, X p.1 p.2 * Q p.2 p.1) =
        ∑ i : n, ∑ j : n, Q i j * X j i := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∑ p : n × n, Complex.re (X p.1 p.2 * Q p.2 p.1)) =
        Complex.re (∑ p : n × n, X p.1 p.2 * Q p.2 p.1) := by
      rw [← Complex.re_sum]
    _ = Complex.re (∑ i : n, ∑ j : n, Q i j * X j i) := by rw [hsum]
    _ = (∑ i : n, ∑ j : n, Q i j * X j i).re := by
      rw [Complex.re_sum]

/-- The entry-Hilbert pairing is the real part of the full matrix
Hilbert--Schmidt trace pairing, with the first argument adjointed. -/
theorem matrixToOperatorHilbert_inner_eq_trace (X Y : CMat) :
    inner ℝ (matrixToOperatorHilbert X) (matrixToOperatorHilbert Y) =
      (Matrix.trace (star X * Y)).re := by
  simpa only [star_star,
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM_apply] using
    matrixToOperatorHilbert_star_pairing (star X) Y

/-- The Hamiltonian commutator's Hilbert adjoint is its Heisenberg dual.
The equality is on the full complex matrix algebra, viewed with its real
Hilbert--Schmidt pairing. -/
theorem hamiltonianTerm_heisenberg_pairing (H X Y : CMat) :
    inner ℝ
      (matrixToOperatorHilbert
        (InfoGeometry.Modular.SchrodingerGKSL.hamiltonianTerm H X))
      (matrixToOperatorHilbert Y) =
    inner ℝ (matrixToOperatorHilbert X)
      (matrixToOperatorHilbert (heisenbergHamiltonianTerm H Y)) := by
  rw [matrixToOperatorHilbert_inner_eq_trace, matrixToOperatorHilbert_inner_eq_trace]
  simp only [InfoGeometry.Modular.SchrodingerGKSL.hamiltonianTerm,
    heisenbergHamiltonianTerm, star_smul, star_neg, star_sub, star_mul,
    smul_mul_assoc, mul_smul_comm, Matrix.trace_smul]
  simp only [sub_mul, mul_sub, Matrix.trace_sub, mul_assoc]
  have hcyc : Matrix.trace (star H * (star X * Y)) =
      Matrix.trace (star X * Y * star H) := by
    exact Matrix.trace_mul_comm (star H) (star X * Y)
  have hI : star (Complex.I : ℂ) = -Complex.I := by norm_num
  rw [hI]
  apply congrArg Complex.re
  rw [hcyc, ← mul_assoc (star X) Y (star H)]
  ring

/-- The full-matrix real Hilbert adjoint of one Schrödinger jump term is its
Heisenberg dissipator, with all operator products kept in order. -/
theorem schrodingerDissipatorTerm_heisenberg_pairing (V X Y : CMat) :
    inner ℝ
      (matrixToOperatorHilbert
        (InfoGeometry.Modular.SchrodingerGKSL.schrodingerDissipatorTerm V X))
      (matrixToOperatorHilbert Y) =
    inner ℝ (matrixToOperatorHilbert X)
      (matrixToOperatorHilbert (heisenbergDissipatorTerm V Y)) := by
  rw [matrixToOperatorHilbert_inner_eq_trace, matrixToOperatorHilbert_inner_eq_trace]
  simp only [InfoGeometry.Modular.SchrodingerGKSL.schrodingerDissipatorTerm,
    heisenbergDissipatorTerm, star_sub, star_smul, star_add, star_mul, star_star,
    sub_mul, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_smul, mul_assoc]
  apply congrArg Complex.re
  have hjump : Matrix.trace (V * (star X * (star V * Y))) =
      Matrix.trace (star X * (star V * (Y * V))) := by
    calc
      Matrix.trace (V * (star X * (star V * Y))) =
          Matrix.trace ((star X * (star V * Y)) * V) :=
        Matrix.trace_mul_comm V (star X * (star V * Y))
      _ = Matrix.trace (star X * (star V * (Y * V))) := by simp [mul_assoc]
  have hanti : Matrix.trace (star V * (V * (star X * Y))) =
      Matrix.trace (star X * (Y * (star V * V))) := by
    simpa [mul_assoc] using
      (Matrix.trace_mul_comm (star V * V) (star X * Y))
  rw [hjump, hanti]
  simp only [mul_add, Matrix.trace_add]
  have hhalf : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf]

/-- Summing the single-jump pairing proves the duality for an arbitrary
finite family of jump operators. -/
theorem schrodingerDissipator_heisenberg_pairing (V : ι → CMat) (X Y : CMat) :
    inner ℝ
      (matrixToOperatorHilbert
        (InfoGeometry.Modular.SchrodingerGKSL.schrodingerDissipator V X))
      (matrixToOperatorHilbert Y) =
    inner ℝ (matrixToOperatorHilbert X)
      (matrixToOperatorHilbert (∑ k, heisenbergDissipatorTerm (V k) Y)) := by
  rw [InfoGeometry.Modular.SchrodingerGKSL.schrodingerDissipator]
  rw [matrixToOperatorHilbert_sum]
  rw [matrixToOperatorHilbert_sum]
  rw [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact schrodingerDissipatorTerm_heisenberg_pairing (V k) X Y

/-- The full finite-matrix Schrödinger GKSL generator and the stated
Heisenberg generator are adjoints for the real Hilbert--Schmidt pairing. -/
theorem schrodinger_heisenberg_pairing (H X Y : CMat) (V : ι → CMat) :
    inner ℝ
      (matrixToOperatorHilbert
        (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V X))
      (matrixToOperatorHilbert Y) =
    inner ℝ (matrixToOperatorHilbert X)
      (matrixToOperatorHilbert (heisenbergLindbladian H V Y)) := by
  rw [InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian,
    heisenbergLindbladian]
  rw [matrixToOperatorHilbert_add]
  rw [matrixToOperatorHilbert_add]
  rw [inner_add_left, inner_add_right]
  rw [hamiltonianTerm_heisenberg_pairing, schrodingerDissipator_heisenberg_pairing]

/-- The Heisenberg operator is the genuine Hilbert adjoint of the full
Schrödinger GKSL operator on the matrix-entry real Hilbert space. -/
theorem schrodingerOperatorCLM_adjoint (H : CMat) (V : ι → CMat) :
    (schrodingerOperatorCLM H V).adjoint = heisenbergOperatorCLM H V := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (heisenbergOperatorCLM H V) (schrodingerOperatorCLM H V)).2
  intro X Y
  rw [← matrixToOperatorHilbert_operatorHilbertToMatrix X,
    ← matrixToOperatorHilbert_operatorHilbertToMatrix Y]
  rw [matrixToOperatorHilbert_generator,
    matrixToOperatorHilbert_heisenbergGenerator]
  simpa only [real_inner_comm] using
    (schrodinger_heisenberg_pairing H
      (operatorHilbertToMatrix Y) (operatorHilbertToMatrix X) V).symm


/-- The transported left action has the matrix adjoint dictated by the
Hilbert--Schmidt pairing: left multiplication by `A` is adjoint to left
multiplication by `Aᴴ`. This is proved on the full operator matrix space. -/
theorem matrixLeftActionCLM_adjoint (A : CMat) :
    (matrixLeftActionCLM A).adjoint = matrixLeftActionCLM (star A) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (matrixLeftActionCLM (star A)) (matrixLeftActionCLM A)).2
  intro X Y
  rw [matrixLeftActionCLM_apply, matrixLeftActionCLM_apply]
  have hleft := matrixToOperatorHilbert_star_pairing
    (star (operatorHilbertToMatrix X) * A) (operatorHilbertToMatrix Y)
  have hright := matrixToOperatorHilbert_star_pairing
    (star (operatorHilbertToMatrix X))
    (A * operatorHilbertToMatrix Y)
  have hleft' : inner ℝ
      (matrixToOperatorHilbert (star A * operatorHilbertToMatrix X)) Y =
        InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
          (star (operatorHilbertToMatrix X) * A) (operatorHilbertToMatrix Y) := by
    simpa [star_mul] using hleft
  have hright' : InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
      (star (operatorHilbertToMatrix X)) (A * operatorHilbertToMatrix Y) =
        inner ℝ X (matrixToOperatorHilbert (A * operatorHilbertToMatrix Y)) := by
    simpa using hright.symm
  calc
    _ = InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
        (star (operatorHilbertToMatrix X) * A) (operatorHilbertToMatrix Y) := hleft'
    _ = InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
        (star (operatorHilbertToMatrix X)) (A * operatorHilbertToMatrix Y) := by
          simp [InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM_apply,
            Matrix.mul_assoc]
    _ = _ := hright'

/-- The full-entry Hilbert adjoint of right multiplication is right
multiplication by the matrix adjoint. -/
theorem matrixRightActionCLM_adjoint (A : CMat) :
    (matrixRightActionCLM A).adjoint = matrixRightActionCLM (star A) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (matrixRightActionCLM (star A)) (matrixRightActionCLM A)).2
  intro X Y
  rw [matrixRightActionCLM_apply, matrixRightActionCLM_apply]
  rw [← matrixToOperatorHilbert_operatorHilbertToMatrix X,
    ← matrixToOperatorHilbert_operatorHilbertToMatrix Y]
  rw [matrixToOperatorHilbert_inner_eq_trace, matrixToOperatorHilbert_inner_eq_trace]
  apply congrArg Complex.re
  simp only [operatorHilbertToMatrix_matrixToOperatorHilbert, star_mul, star_star]
  rw [mul_assoc]
  rw [Matrix.trace_mul_comm A (star (operatorHilbertToMatrix X) *
    operatorHilbertToMatrix Y)]
  simp only [mul_assoc]

/-- Explicit matrix realization of the Riesz vector of `Re Tr(QX)`. -/
theorem commutantReadoutRieszVector_eq_star (Q : CMat) :
    commutantReadoutRieszVector Q = matrixToOperatorHilbert (star Q) := by
  apply ext_inner_right ℝ
  intro X
  simpa only [matrixToOperatorHilbert_operatorHilbertToMatrix] using
    (commutantReadoutRieszVector_pairing Q (operatorHilbertToMatrix X)).trans
      (matrixToOperatorHilbert_star_pairing Q (operatorHilbertToMatrix X)).symm

/-- The NESS readout's Riesz vector is the Hilbert adjoint of the represented
left action, applied to the identity operator. This identifies the trace
functional with the adjoint of the actual noncommutative matrix action. -/
theorem commutantReadoutRieszVector_eq_leftActionAdjoint_unit (Q : CMat) :
    commutantReadoutRieszVector Q =
      (matrixLeftActionCLM Q).adjoint (matrixToOperatorHilbert (1 : CMat)) := by
  rw [matrixLeftActionCLM_adjoint, commutantReadoutRieszVector_eq_star]
  simp [matrixLeftActionCLM_apply]

/-- Transport the existing finite-matrix Schrödinger GKSL flow to the
real-linear Hilbert carrier of matrix entries. -/
def schrodingerOperatorFlow (H : CMat) (V : ι → CMat) (t : ℝ) :
    OpHilbert →L[ℝ] OpHilbert :=
  matrixToOperatorCLM.comp ((gkslFlow H V t).comp operatorToMatrixCLM)

omit [DecidableEq n] in
@[simp] theorem operatorToMatrixCLM_apply (X : OpHilbert) :
    operatorToMatrixCLM X = operatorHilbertToMatrix X := rfl

omit [DecidableEq n] in
@[simp] theorem matrixToOperatorCLM_apply (X : CMat) :
    matrixToOperatorCLM X = matrixToOperatorHilbert X := rfl

@[simp] theorem operatorToMatrix_schrodingerOperatorFlow (H : CMat)
    (V : ι → CMat) (t : ℝ) (X : OpHilbert) :
    operatorHilbertToMatrix (schrodingerOperatorFlow H V t X) =
      gkslFlow H V t (operatorHilbertToMatrix X) := by
  simp [schrodingerOperatorFlow, matrixToOperatorCLM, operatorToMatrixCLM,
    matrixOperatorEquiv]

@[simp] theorem schrodingerOperatorFlow_matrixToOperator (H : CMat)
    (V : ι → CMat) (t : ℝ) (X : CMat) :
    schrodingerOperatorFlow H V t (matrixToOperatorHilbert X) =
      matrixToOperatorHilbert (gkslFlow H V t X) := by
  rw [← matrixToOperatorHilbert_operatorHilbertToMatrix
    (schrodingerOperatorFlow H V t (matrixToOperatorHilbert X))]
  simpa only [operatorHilbertToMatrix_matrixToOperatorHilbert] using
    congrArg matrixToOperatorHilbert
      (operatorToMatrix_schrodingerOperatorFlow H V t
        (matrixToOperatorHilbert X))

/-- Each full operator-space orbit has derivative given by the transported
Schrödinger GKSL generator. -/
theorem hasDerivAt_schrodingerOperatorFlow (H : CMat) (V : ι → CMat)
    (X : OpHilbert) (t : ℝ) :
    HasDerivAt (fun s : ℝ => schrodingerOperatorFlow H V s X)
      (schrodingerOperatorCLM H V (schrodingerOperatorFlow H V t X)) t := by
  have hflow := hasDerivAt_gkslFlow_orbit H V
    (operatorHilbertToMatrix X) t
  have hcomp := (matrixToOperatorCLM (n := n)).hasFDerivAt.comp_hasDerivAt t hflow
  convert hcomp using 1
  · funext s
    simp [schrodingerOperatorFlow, matrixToOperatorCLM,
      operatorToMatrixCLM, matrixOperatorEquiv]
  · calc
      schrodingerOperatorCLM H V (schrodingerOperatorFlow H V t X) =
          schrodingerOperatorCLM H V
            (schrodingerOperatorFlow H V t
              (matrixToOperatorHilbert (operatorHilbertToMatrix X))) := by
                rw [matrixToOperatorHilbert_operatorHilbertToMatrix]
      _ = schrodingerOperatorCLM H V
            (matrixToOperatorHilbert
              (gkslFlow H V t (operatorHilbertToMatrix X))) := by
                rw [schrodingerOperatorFlow_matrixToOperator]
      _ = matrixToOperatorHilbert
            (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V
              (gkslFlow H V t (operatorHilbertToMatrix X))) :=
                matrixToOperatorHilbert_generator H V _
      _ = matrixToOperatorCLM
            (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V
              (gkslFlow H V t (operatorHilbertToMatrix X))) := rfl

/-- The lifted finite-matrix evolution obeys the same one-parameter
semigroup composition law on the complete operator space. -/
theorem schrodingerOperatorFlow_add (H : CMat) (V : ι → CMat)
    (s t : ℝ) (X : OpHilbert) :
    schrodingerOperatorFlow H V (s + t) X =
      schrodingerOperatorFlow H V s (schrodingerOperatorFlow H V t X) := by
  apply matrixOperatorEquiv.symm.injective
  change operatorHilbertToMatrix (schrodingerOperatorFlow H V (s + t) X) =
    operatorHilbertToMatrix
      (schrodingerOperatorFlow H V s (schrodingerOperatorFlow H V t X))
  rw [operatorToMatrix_schrodingerOperatorFlow,
    operatorToMatrix_schrodingerOperatorFlow,
    operatorToMatrix_schrodingerOperatorFlow]
  have h := congrArg (fun F : CMat →L[ℝ] CMat => F (operatorHilbertToMatrix X))
    (gkslFlow_add H V s t)
  simpa using h

/-- The matrix-transported Schrödinger flow is the exponential flow of its
operator-space generator. The equality is proved from the orbit ODE and
uniqueness, so it does not assume that transporting an exponential commutes
with the coordinate equivalence. -/
theorem schrodingerOperatorFlow_eq_generatorFlow (H : CMat) (V : ι → CMat)
    (t : ℝ) :
    schrodingerOperatorFlow H V t =
      InfoGeometry.Modular.SchrodingerFlow.flow
        (schrodingerOperatorCLM H V) t := by
  apply ContinuousLinearMap.ext
  intro X
  let A := schrodingerOperatorCLM H V
  let f : ℝ → OpHilbert := fun s => schrodingerOperatorFlow H V s X
  let g : ℝ → OpHilbert := fun s =>
    InfoGeometry.Modular.SchrodingerFlow.flow A s X
  let v : ℝ → OpHilbert → OpHilbert := fun _ Y => A Y
  have hv : ∀ s, LipschitzOnWith ‖A‖₊ (v s) Set.univ := by
    intro s
    simpa [v] using (lipschitzOnWith_univ.mpr A.lipschitzWith)
  have hf : ∀ s, HasDerivAt f (v s (f s)) s ∧ f s ∈ Set.univ := by
    intro s
    constructor
    · simpa [f, v, A] using hasDerivAt_schrodingerOperatorFlow H V X s
    · exact Set.mem_univ _
  have hg : ∀ s, HasDerivAt g (v s (g s)) s ∧ g s ∈ Set.univ := by
    intro s
    constructor
    · simpa [g, v, A] using
        InfoGeometry.Modular.SchrodingerFlow.hasDerivAt_orbit A X s
    · exact Set.mem_univ _
  have h0 : f 0 = g 0 := by
    apply matrixOperatorEquiv.symm.injective
    change operatorHilbertToMatrix (schrodingerOperatorFlow H V 0 X) =
      operatorHilbertToMatrix
        (InfoGeometry.Modular.SchrodingerFlow.flow A 0 X)
    rw [operatorToMatrix_schrodingerOperatorFlow]
    simp [gkslFlow, InfoGeometry.Modular.SchrodingerFlow.flow]
  have hfg := ODE_solution_unique_univ hv hf hg h0
  exact congrFun hfg t

/-- Exponential Heisenberg flow on the full real operator-Hilbert carrier. -/
noncomputable def heisenbergOperatorFlow (H : CMat) (V : ι → CMat) (t : ℝ) :
    OpHilbert →L[ℝ] OpHilbert :=
  InfoGeometry.Modular.SchrodingerFlow.flow (heisenbergOperatorCLM H V) t

omit [DecidableEq n] in
/-- A zero mode of a bounded generator is fixed by its exponential flow. -/
lemma operatorFlow_fixes_of_generator_zero
    (A : OpHilbert →L[ℝ] OpHilbert) (x : OpHilbert) (hA : A x = 0) (t : ℝ) :
    InfoGeometry.Modular.SchrodingerFlow.flow A t x = x := by
  let f : ℝ → OpHilbert := fun s =>
    InfoGeometry.Modular.SchrodingerFlow.flow A s x
  let g : ℝ → OpHilbert := fun _ => x
  let v : ℝ → OpHilbert → OpHilbert := fun _ y => A y
  have hv : ∀ s, LipschitzOnWith ‖A‖₊ (v s) Set.univ := by
    intro s
    simpa [v] using (lipschitzOnWith_univ.mpr A.lipschitzWith)
  have hf : ∀ s, HasDerivAt f (v s (f s)) s ∧ f s ∈ Set.univ := by
    intro s
    exact ⟨by simpa [f, v] using
      InfoGeometry.Modular.SchrodingerFlow.hasDerivAt_orbit A x s,
      Set.mem_univ _⟩
  have hg : ∀ s, HasDerivAt g (v s (g s)) s ∧ g s ∈ Set.univ := by
    intro s
    constructor
    · simpa [g, v, hA] using (hasDerivAt_const s x)
    · exact Set.mem_univ _
  have h0 : f 0 = g 0 := by simp [f, g]
  have hfg := ODE_solution_unique_univ hv hf hg h0
  exact congrFun hfg t

/-- The Heisenberg exponential semigroup fixes the identity operator because
its full matrix generator annihilates identity. -/
@[simp] theorem heisenbergOperatorFlow_one
    (H : CMat) (V : ι → CMat) (t : ℝ) :
    heisenbergOperatorFlow H V t (matrixToOperatorHilbert (1 : CMat)) =
      matrixToOperatorHilbert 1 := by
  exact operatorFlow_fixes_of_generator_zero
    (heisenbergOperatorCLM H V) (matrixToOperatorHilbert 1)
    (heisenbergOperatorCLM_one H V) t

/-- The Heisenberg semigroup is the genuine Hilbert adjoint of the
Schrödinger semigroup at every real time. This uses the full matrix generator
adjoint, not a positivity or diagonalization surrogate. -/
theorem schrodingerOperatorFlow_adjoint (H : CMat) (V : ι → CMat) (t : ℝ) :
    (schrodingerOperatorFlow H V t).adjoint = heisenbergOperatorFlow H V t := by
  rw [schrodingerOperatorFlow_eq_generatorFlow]
  simp only [heisenbergOperatorFlow, InfoGeometry.Modular.SchrodingerFlow.flow]
  change star (NormedSpace.exp (t • schrodingerOperatorCLM H V)) =
    NormedSpace.exp (t • heisenbergOperatorCLM H V)
  rw [NormedSpace.star_exp, star_smul, star_trivial,
    ContinuousLinearMap.star_eq_adjoint, schrodingerOperatorCLM_adjoint]

/-- The complex trace of the full Schrödinger GKSL matrix flow is conserved.
The imported flow bridge records only its real part; this strengthens that
readout by applying the same generator-annihilation argument to both real
coordinates of the complex trace. -/
theorem complexTrace_schrodingerOperatorFlow (H : CMat) (V : ι → CMat)
    (X : CMat) (t : ℝ) :
    Matrix.trace (gkslFlow H V t X) = Matrix.trace X := by
  apply Complex.ext
  · exact realTrace_gkslFlow H V X t
  · apply InfoGeometry.Modular.SchrodingerFlow.trace_flow_preservation
      (generatorEnd H V)
      (Complex.imCLM.comp
        (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap)
      ?_ X t
    intro Y
    change (Matrix.trace (generatorCLM H V Y)).im = 0
    rw [generatorCLM_apply,
      InfoGeometry.Modular.SchrodingerGKSL.trace_schrodingerLindbladian_zero]
    rfl

/-- Apply one continuous real operator independently to both Krein sheets. -/
def sheetDiagonalLift (T : OpHilbert →L[ℝ] OpHilbert) : DOp →L[ℝ] DOp where
  toFun u := to_doubled (T (WithLp.fst u)) (T (WithLp.snd u))
  map_add' u v := by
    apply DoubledSpace.ext <;> simp [WithLp.add_fst, WithLp.add_snd]
  map_smul' r u := by
    apply DoubledSpace.ext <;> simp [WithLp.smul_fst, WithLp.smul_snd]
  cont := by
    let f : DOp →L[ℝ] OpHilbert := T.comp (fst_L (E := OpHilbert))
    let g : DOp →L[ℝ] OpHilbert := T.comp (snd_L (E := OpHilbert))
    change Continuous (fun u : DOp => to_doubled (f u) (g u))
    exact (WithLp.prod_continuous_toLp (p := (2 : ENNReal))
      (α := OpHilbert) (β := OpHilbert)).comp (f.continuous.prodMk g.continuous)

/-- The continuous linear map assembling two operator coordinates into the
canonical double-real Hilbert carrier. -/
def pairToDoubledCLM : OpHilbert × OpHilbert →L[ℝ] DOp where
  toFun p := to_doubled p.1 p.2
  map_add' p q := by
    simp [← WithLp.toLp_add]
    exact Prod.ext rfl rfl
  map_smul' r p := by
    simp [← WithLp.toLp_smul]
    exact Prod.ext rfl rfl
  cont := WithLp.prod_continuous_toLp
    (p := (2 : ENNReal)) (α := OpHilbert) (β := OpHilbert)

omit [DecidableEq n] in
@[simp] theorem sheetDiagonalLift_apply (T : OpHilbert →L[ℝ] OpHilbert)
    (X Y : OpHilbert) :
    sheetDiagonalLift T (to_doubled X Y) = to_doubled (T X) (T Y) := rfl

/-- On the double-real carrier, the Heisenberg flow fixes the pair of
identity operators sheetwise. -/
@[simp] theorem sheetHeisenbergOperatorFlow_identity
    (H : CMat) (V : ι → CMat) (t : ℝ) :
    sheetDiagonalLift (heisenbergOperatorFlow H V t)
        (to_doubled (matrixToOperatorHilbert (1 : CMat))
          (matrixToOperatorHilbert (1 : CMat))) =
      to_doubled (matrixToOperatorHilbert (1 : CMat))
        (matrixToOperatorHilbert (1 : CMat)) := by
  simp [sheetDiagonalLift_apply]

/-- The matrix GKSL flow, lifted on both sheets, is differentiable on the
canonical doubled-real carrier, with the generator acting on each sheet. -/
theorem hasDerivAt_doubledSchrodingerOperatorFlow
    (H : CMat) (V : ι → CMat) (X Y : OpHilbert) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => sheetDiagonalLift (schrodingerOperatorFlow H V s)
        (to_doubled X Y))
      (sheetDiagonalLift (schrodingerOperatorCLM H V)
        (to_doubled
          (schrodingerOperatorFlow H V t X)
          (schrodingerOperatorFlow H V t Y))) t := by
  have hpair := HasDerivAt.prodMk
    (hasDerivAt_schrodingerOperatorFlow H V X t)
    (hasDerivAt_schrodingerOperatorFlow H V Y t)
  have hcomp := (pairToDoubledCLM (n := n)).hasFDerivAt.comp_hasDerivAt t hpair
  simpa [Function.comp_def, pairToDoubledCLM, sheetDiagonalLift_apply] using hcomp

/-- The Krein pairing of two doubled-real matrix GKSL orbits differentiates
by applying the generator in each slot. The pairing is the one induced by the
fundamental symmetry, not the positive ambient product. -/
theorem hasDerivAt_doubledKreinPairing_gkslFlow
    (H : CMat) (V : ι → CMat) (X Y U W : OpHilbert) (t : ℝ) :
    HasDerivAt
      (fun s => KreinSpace.kreinInner
        (sheetDiagonalLift (schrodingerOperatorFlow H V s) (to_doubled X Y))
        (sheetDiagonalLift (schrodingerOperatorFlow H V s) (to_doubled U W)))
      (KreinSpace.kreinInner
        (sheetDiagonalLift (schrodingerOperatorCLM H V)
          (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled X Y)))
        (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled U W)) +
       KreinSpace.kreinInner
        (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled X Y))
        (sheetDiagonalLift (schrodingerOperatorCLM H V)
          (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled U W)))) t := by
  let A := sheetDiagonalLift (schrodingerOperatorCLM H V)
  let leftOrbit := fun s : ℝ =>
    sheetDiagonalLift (schrodingerOperatorFlow H V s) (to_doubled X Y)
  let rightOrbit := fun s : ℝ =>
    sheetDiagonalLift (schrodingerOperatorFlow H V s) (to_doubled U W)
  have hleft : HasDerivAt leftOrbit (A (leftOrbit t)) t := by
    simpa [leftOrbit, A, sheetDiagonalLift_apply] using
      hasDerivAt_doubledSchrodingerOperatorFlow H V X Y t
  have hright : HasDerivAt rightOrbit (A (rightOrbit t)) t := by
    simpa [rightOrbit, A, sheetDiagonalLift_apply] using
      hasDerivAt_doubledSchrodingerOperatorFlow H V U W t
  simpa only [leftOrbit, rightOrbit, A] using
    InfoGeometry.Canonical.KreinFlowConservation.hasDerivAt_krein_pairing
      hleft hright

/-- Along the lifted GKSL orbit, the Dirac/Krein quadratic form changes by
the Krein-symmetric part of the generator. This identifies the exact
obstruction to conservation without assuming that the dissipative flow is
Krein-isometric. -/
theorem hasDerivAt_doubledKreinQuadratic_gkslFlow
    (H : CMat) (V : ι → CMat) (X Y : OpHilbert) (t : ℝ) :
    HasDerivAt
      (fun s => KreinSpace.kreinInner
        (sheetDiagonalLift (schrodingerOperatorFlow H V s) (to_doubled X Y))
        (sheetDiagonalLift (schrodingerOperatorFlow H V s) (to_doubled X Y)))
      (KreinSpace.kreinInner
        (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled X Y))
        ((KreinSpace.kreinAdjoint (sheetDiagonalLift (schrodingerOperatorCLM H V)) +
          sheetDiagonalLift (schrodingerOperatorCLM H V))
          (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled X Y)))) t := by
  let A := sheetDiagonalLift (schrodingerOperatorCLM H V)
  let orbit := fun s : ℝ =>
    sheetDiagonalLift (schrodingerOperatorFlow H V s) (to_doubled X Y)
  have hpair := hasDerivAt_doubledKreinPairing_gkslFlow H V X Y X Y t
  change HasDerivAt (fun s => KreinSpace.kreinInner (orbit s) (orbit s))
    (KreinSpace.kreinInner (A (orbit t)) (orbit t) +
      KreinSpace.kreinInner (orbit t) (A (orbit t))) t at hpair
  have hmetric :
      KreinSpace.kreinInner (A (orbit t)) (orbit t) +
          KreinSpace.kreinInner (orbit t) (A (orbit t)) =
        KreinSpace.kreinInner (orbit t)
          ((KreinSpace.kreinAdjoint A + A) (orbit t)) := by
    rw [KreinSpace.kreinInner_kreinAdjoint,
      _root_.add_apply, KreinSpace.kreinInner_add_right]
  rw [hmetric] at hpair
  simpa only [orbit, A] using hpair

/-- The doubled-real Schrödinger GKSL flow preserves the Dirac/Krein
quadratic form on every full matrix-space vector exactly when its lifted
generator is Krein-skew-adjoint. The converse follows by differentiating at
time zero, so this criterion does not infer conservation from stationarity. -/
theorem schrodingerOperatorFlow_kreinQuadratic_preserved_iff_generator_skew
    (H : CMat) (V : ι → CMat) :
    KreinSpace.IsKreinSkewAdjoint (sheetDiagonalLift (schrodingerOperatorCLM H V)) ↔
      ∀ (X Y : OpHilbert) (t : ℝ),
        KreinSpace.kreinInner
          (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled X Y))
          (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled X Y)) =
        KreinSpace.kreinInner (to_doubled X Y) (to_doubled X Y) := by
  let A := sheetDiagonalLift (schrodingerOperatorCLM H V)
  constructor
  · intro hA X Y t
    let orbit : ℝ → DOp := fun s =>
      sheetDiagonalLift (schrodingerOperatorFlow H V s) (to_doubled X Y)
    have horbit : ∀ s, HasDerivAt orbit (A (orbit s)) s := by
      intro s
      simpa [orbit, A, sheetDiagonalLift_apply] using
        hasDerivAt_doubledSchrodingerOperatorFlow H V X Y s
    have hconst := InfoGeometry.Canonical.KreinFlowConservation.krein_square_conserved
      (A := fun _ : ℝ => A) horbit (fun _ => hA) t 0
    simpa [orbit, A, schrodingerOperatorFlow, gkslFlow,
      InfoGeometry.Modular.SchrodingerFlow.flow_zero,
      sheetDiagonalLift_apply] using hconst
  · intro hpres
    apply (InfoGeometry.Canonical.KreinFlowConservation.isKreinSkewAdjoint_iff_quadratic_derivative_zero A).2
    intro z
    let X := WithLp.fst z
    let Y := WithLp.snd z
    have hz : z = to_doubled X Y := by
      apply DoubledSpace.ext <;> rfl
    have hquad := hasDerivAt_doubledKreinQuadratic_gkslFlow H V X Y 0
    have hconst : HasDerivAt
        (fun s : ℝ => KreinSpace.kreinInner
          (sheetDiagonalLift (schrodingerOperatorFlow H V s) z)
          (sheetDiagonalLift (schrodingerOperatorFlow H V s) z))
        0 0 := by
      have heq : (fun s : ℝ => KreinSpace.kreinInner
          (sheetDiagonalLift (schrodingerOperatorFlow H V s) z)
          (sheetDiagonalLift (schrodingerOperatorFlow H V s) z)) =
          fun _ => KreinSpace.kreinInner z z := by
        funext s
        rw [hz]
        exact hpres X Y s
      rw [heq]
      exact hasDerivAt_const 0 (KreinSpace.kreinInner z z)
    have hderiv0 :
        KreinSpace.kreinInner z ((KreinSpace.kreinAdjoint A + A) z) = 0 := by
      simpa [A, schrodingerOperatorFlow, gkslFlow,
        InfoGeometry.Modular.SchrodingerFlow.flow_zero, hz,
        sheetDiagonalLift_apply] using hquad.unique hconst
    have hmetric :
        KreinSpace.kreinInner z ((KreinSpace.kreinAdjoint A + A) z) =
          KreinSpace.kreinInner (A z) z + KreinSpace.kreinInner z (A z) := by
      calc
        KreinSpace.kreinInner z ((KreinSpace.kreinAdjoint A + A) z) =
            KreinSpace.kreinInner z (KreinSpace.kreinAdjoint A z) +
              KreinSpace.kreinInner z (A z) := by
                rw [_root_.add_apply, KreinSpace.kreinInner_add_right]
        _ = KreinSpace.kreinInner (A z) z + KreinSpace.kreinInner z (A z) := by
              rw [KreinSpace.kreinInner_kreinAdjoint]
    rw [← hmetric]
    exact hderiv0

/-- The matrix GKSL semigroup acts sheetwise on the canonical double-real
Krein carrier, with composition inherited from the existing matrix flow. -/
theorem sheetDiagonalLift_schrodingerOperatorFlow_add
    (H : CMat) (V : ι → CMat) (s t : ℝ) (X Y : OpHilbert) :
    sheetDiagonalLift (schrodingerOperatorFlow H V (s + t)) (to_doubled X Y) =
      sheetDiagonalLift (schrodingerOperatorFlow H V s)
        (sheetDiagonalLift (schrodingerOperatorFlow H V t) (to_doubled X Y)) := by
  simp only [sheetDiagonalLift_apply]
  rw [schrodingerOperatorFlow_add H V s t X,
    schrodingerOperatorFlow_add H V s t Y]

omit [DecidableEq n] in
/-- The doubled operator carrier uses the canonical Dirac/Krein pairing:
the Hilbert product on the first matrix-operator sheet minus that on the
second sheet. The inner products are those of the full entry-Hilbert space,
not a diagonal or scalar restriction of the matrix algebra. -/
theorem operatorSheets_krein_pairing (A B C D : CMat) :
    KreinSpace.kreinInner
        (to_doubled (matrixToOperatorHilbert A) (matrixToOperatorHilbert B))
        (to_doubled (matrixToOperatorHilbert C) (matrixToOperatorHilbert D)) =
      inner ℝ (matrixToOperatorHilbert A) (matrixToOperatorHilbert C) -
        inner ℝ (matrixToOperatorHilbert B) (matrixToOperatorHilbert D) := by
  exact krein_inner_prod_l2 _ _

/-- The NESS commutant readout is exactly the Dirac/Krein pairing against the
Riesz vector in the positive sheet. The Krein pairing here is the repository's
fundamental-symmetry-conjugated product, not an unmodified auxiliary Hilbert
product. -/
theorem commutantReadout_eq_doubledKrein_pairing (Q X : CMat) :
    KreinSpace.kreinInner
        (to_doubled (commutantReadoutRieszVector Q) 0)
        (to_doubled (matrixToOperatorHilbert X) 0) =
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q X := by
  have hvec : commutantReadoutRieszVector Q =
      matrixToOperatorHilbert (operatorHilbertToMatrix (commutantReadoutRieszVector Q)) :=
    (matrixToOperatorHilbert_operatorHilbertToMatrix _).symm
  rw [hvec]
  change KreinSpace.kreinInner
      (to_doubled
        (matrixToOperatorHilbert (operatorHilbertToMatrix (commutantReadoutRieszVector Q)))
        (matrixToOperatorHilbert (0 : CMat)))
      (to_doubled (matrixToOperatorHilbert X) (matrixToOperatorHilbert (0 : CMat))) = _
  rw [operatorSheets_krein_pairing]
  calc
    inner ℝ (matrixToOperatorHilbert
        (operatorHilbertToMatrix (commutantReadoutRieszVector Q)))
        (matrixToOperatorHilbert X) -
      inner ℝ (matrixToOperatorHilbert (0 : CMat))
        (matrixToOperatorHilbert (0 : CMat)) =
        inner ℝ (commutantReadoutRieszVector Q) (matrixToOperatorHilbert X) := by
          rw [← hvec]
          simp [matrixToOperatorHilbert]
          funext ij
          rfl
    _ = InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q X :=
      commutantReadoutRieszVector_pairing Q X

/-- The Dirac/Krein pairing reads two full-matrix commutant observables with
the signature of the real double: the first-sheet readout minus the
second-sheet readout. This is the genuinely two-sheet form of the NESS
readout bridge. -/
theorem twoSheetCommutantReadout_eq_doubledKrein_pairing
    (Qp Qm Xp Xm : CMat) :
    KreinSpace.kreinInner
        (to_doubled (commutantReadoutRieszVector Qp)
          (commutantReadoutRieszVector Qm))
        (to_doubled (matrixToOperatorHilbert Xp)
          (matrixToOperatorHilbert Xm)) =
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Qp Xp -
        InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Qm Xm := by
  rw [krein_inner_prod_l2, commutantReadoutRieszVector_pairing,
    commutantReadoutRieszVector_pairing]

/-- With the Riesz representatives made explicit, the two-sheet Dirac/Krein
pairing is precisely the difference of the two noncommutative real trace
readouts. -/
theorem twoSheetTraceReadout_eq_doubledKrein_pairing
    (Qp Qm Xp Xm : CMat) :
    KreinSpace.kreinInner
        (to_doubled (matrixToOperatorHilbert (star Qp))
          (matrixToOperatorHilbert (star Qm)))
        (to_doubled (matrixToOperatorHilbert Xp)
          (matrixToOperatorHilbert Xm)) =
      (Matrix.trace (Qp * Xp)).re - (Matrix.trace (Qm * Xm)).re := by
  rw [← commutantReadoutRieszVector_eq_star Qp,
    ← commutantReadoutRieszVector_eq_star Qm]
  simpa [InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM_apply]
    using twoSheetCommutantReadout_eq_doubledKrein_pairing Qp Qm Xp Xm

private theorem imaginaryTrace_observableReadout (X : CMat) :
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
        ((-Complex.I) • (1 : CMat)) X = (Matrix.trace X).im := by
  change (Matrix.trace (((-Complex.I) • (1 : CMat)) * X)).re = _
  have hmul : ((-Complex.I) • (1 : CMat)) * X = (-Complex.I) • X := by
    simp
  rw [hmul, Matrix.trace_smul]
  simp [Complex.mul_re]

/-- The imaginary part of the full matrix trace difference on the two sheets
is represented by the Dirac/Krein product against the `-iI` Riesz observables.
The product is the canonical `KreinSpace.kreinInner`, so the second sheet is
weighted by the fundamental symmetry rather than by an auxiliary positive
pairing. -/
theorem twoSheetImaginaryTraceReadout_eq_doubledKrein_pairing
    (Xp Xm : CMat) :
    KreinSpace.kreinInner
        (to_doubled
          (matrixToOperatorHilbert (star ((-Complex.I) • (1 : CMat))))
          (matrixToOperatorHilbert (star ((-Complex.I) • (1 : CMat)))))
        (to_doubled (matrixToOperatorHilbert Xp) (matrixToOperatorHilbert Xm)) =
      (Matrix.trace Xp).im - (Matrix.trace Xm).im := by
  rw [twoSheetTraceReadout_eq_doubledKrein_pairing]
  change InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
      ((-Complex.I) • (1 : CMat)) Xp -
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
      ((-Complex.I) • (1 : CMat)) Xm = _
  rw [imaginaryTrace_observableReadout, imaginaryTrace_observableReadout]

/-- The `-iI` two-sheet Krein readout of the imaginary trace coordinate is
conserved by the full matrix GKSL flow on both sheets. -/
theorem twoSheetImaginaryTraceReadout_gkslFlow_invariant
    (H Xp Xm : CMat) (V : ι → CMat) (t : ℝ) :
    KreinSpace.kreinInner
        (to_doubled
          (matrixToOperatorHilbert (star ((-Complex.I) • (1 : CMat))))
          (matrixToOperatorHilbert (star ((-Complex.I) • (1 : CMat)))))
        (to_doubled
          (matrixToOperatorHilbert (gkslFlow H V t Xp))
          (matrixToOperatorHilbert (gkslFlow H V t Xm))) =
      KreinSpace.kreinInner
        (to_doubled
          (matrixToOperatorHilbert (star ((-Complex.I) • (1 : CMat))))
          (matrixToOperatorHilbert (star ((-Complex.I) • (1 : CMat)))))
        (to_doubled (matrixToOperatorHilbert Xp) (matrixToOperatorHilbert Xm)) := by
  rw [twoSheetImaginaryTraceReadout_eq_doubledKrein_pairing,
    twoSheetImaginaryTraceReadout_eq_doubledKrein_pairing,
    complexTrace_schrodingerOperatorFlow H V Xp t,
    complexTrace_schrodingerOperatorFlow H V Xm t]

/-- The signed two-sheet trace readout is the Dirac/Krein pairing against the
adjoint left actions of the two observables, each applied to the identity.
Both matrix sheets remain full and noncommutative. -/
theorem twoSheetTraceReadout_eq_leftActionAdjointKrein_pairing
    (Qp Qm Xp Xm : CMat) :
    KreinSpace.kreinInner
        (to_doubled
          ((matrixLeftActionCLM Qp).adjoint (matrixToOperatorHilbert (1 : CMat)))
          ((matrixLeftActionCLM Qm).adjoint (matrixToOperatorHilbert (1 : CMat))))
        (to_doubled (matrixToOperatorHilbert Xp) (matrixToOperatorHilbert Xm)) =
      (Matrix.trace (Qp * Xp)).re - (Matrix.trace (Qm * Xm)).re := by
  rw [← commutantReadoutRieszVector_eq_leftActionAdjoint_unit Qp,
    ← commutantReadoutRieszVector_eq_leftActionAdjoint_unit Qm]
  rw [commutantReadoutRieszVector_eq_star Qp,
    commutantReadoutRieszVector_eq_star Qm]
  exact twoSheetTraceReadout_eq_doubledKrein_pairing Qp Qm Xp Xm

/-- A joint-commutant NESS charge remains invariant when read as a Krein
pairing on the doubled full-matrix operator carrier. -/
theorem commutantReadout_doubledKrein_gkslFlow_invariant
    (H Q X : CMat) (V : ι → CMat)
    (hQH : Q * H = H * Q)
    (hQV : ∀ i, Q * V i = V i * Q)
    (hQstarV : ∀ i, Q * star (V i) = star (V i) * Q) (t : ℝ) :
    KreinSpace.kreinInner
        (to_doubled (commutantReadoutRieszVector Q) 0)
        (to_doubled
          (schrodingerOperatorFlow H V t (matrixToOperatorHilbert X)) 0) =
      KreinSpace.kreinInner
        (to_doubled (commutantReadoutRieszVector Q) 0)
        (to_doubled (matrixToOperatorHilbert X) 0) := by
  rw [schrodingerOperatorFlow_matrixToOperator,
    commutantReadout_eq_doubledKrein_pairing,
    commutantReadout_eq_doubledKrein_pairing]
  exact InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadout_gkslFlow_invariant
    H Q X V hQH hQV hQstarV t

/-- A proposed NESS limit with a different commutant charge under the actual
double-real Krein pairing cannot be the norm limit of the full matrix GKSL
orbit. This is the Krein-coordinate form of the existing matrix obstruction;
it assumes neither orbit convergence nor a diagonal representative. -/
theorem not_tendsto_gkslFlow_of_kreinReadout_ne
    (H Q X rhoLimit : CMat) (V : ι → CMat)
    (hQH : Q * H = H * Q)
    (hQV : ∀ i, Q * V i = V i * Q)
    (hQstarV : ∀ i, Q * star (V i) = star (V i) * Q)
    (hne :
      KreinSpace.kreinInner
          (to_doubled (commutantReadoutRieszVector Q) 0)
          (to_doubled (matrixToOperatorHilbert X) 0) ≠
        KreinSpace.kreinInner
          (to_doubled (commutantReadoutRieszVector Q) 0)
          (to_doubled (matrixToOperatorHilbert rhoLimit) 0)) :
    ¬ Tendsto (fun t : ℝ => gkslFlow H V t X) atTop (𝓝 rhoLimit) := by
  have hX := commutantReadout_eq_doubledKrein_pairing Q X
  have hLimit := commutantReadout_eq_doubledKrein_pairing Q rhoLimit
  have hreadout :
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q X ≠
        InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q rhoLimit := by
    intro heq
    apply hne
    calc
      _ = InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q X := hX
      _ = InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM Q rhoLimit := heq
      _ = _ := hLimit.symm
  have htrace : (Matrix.trace (Q * X)).re ≠
      (Matrix.trace (Q * rhoLimit)).re := by
    simpa only [InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM_apply]
      using hreadout
  exact InfoGeometry.Modular.CommutantInvariantGKSLFlow.not_tendsto_gkslFlow_of_readout_ne
    H Q X rhoLimit V hQH hQV hQstarV htrace

/-- If both sheets evolve under the same matrix GKSL flow, the signed
two-sheet commutant readout is conserved. The two commutant observables may
differ, and the claim retains the full matrix operators on each sheet. -/
theorem twoSheetCommutantReadout_gkslFlow_invariant
    (H Qp Qm Xp Xm : CMat) (V : ι → CMat)
    (hQpH : Qp * H = H * Qp)
    (hQpV : ∀ i, Qp * V i = V i * Qp)
    (hQpStarV : ∀ i, Qp * star (V i) = star (V i) * Qp)
    (hQmH : Qm * H = H * Qm)
    (hQmV : ∀ i, Qm * V i = V i * Qm)
    (hQmStarV : ∀ i, Qm * star (V i) = star (V i) * Qm) (t : ℝ) :
    KreinSpace.kreinInner
        (to_doubled (commutantReadoutRieszVector Qp)
          (commutantReadoutRieszVector Qm))
        (to_doubled
          (matrixToOperatorHilbert (gkslFlow H V t Xp))
          (matrixToOperatorHilbert (gkslFlow H V t Xm))) =
      KreinSpace.kreinInner
        (to_doubled (commutantReadoutRieszVector Qp)
          (commutantReadoutRieszVector Qm))
        (to_doubled (matrixToOperatorHilbert Xp)
          (matrixToOperatorHilbert Xm)) := by
  rw [twoSheetCommutantReadout_eq_doubledKrein_pairing,
    twoSheetCommutantReadout_eq_doubledKrein_pairing]
  change (Matrix.trace (Qp * gkslFlow H V t Xp)).re -
      (Matrix.trace (Qm * gkslFlow H V t Xm)).re =
    (Matrix.trace (Qp * Xp)).re - (Matrix.trace (Qm * Xm)).re
  rw [InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadout_gkslFlow_invariant
      H Qp Xp V hQpH hQpV hQpStarV t,
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadout_gkslFlow_invariant
      H Qm Xm V hQmH hQmV hQmStarV t]

/-- Matrix-trace form of the conserved double-sheet charge. This is the
explicit noncommutative observable statement corresponding to the Krein
pairing conservation law. -/
theorem twoSheetTraceReadout_gkslFlow_invariant
    (H Qp Qm Xp Xm : CMat) (V : ι → CMat)
    (hQpH : Qp * H = H * Qp)
    (hQpV : ∀ i, Qp * V i = V i * Qp)
    (hQpStarV : ∀ i, Qp * star (V i) = star (V i) * Qp)
    (hQmH : Qm * H = H * Qm)
    (hQmV : ∀ i, Qm * V i = V i * Qm)
    (hQmStarV : ∀ i, Qm * star (V i) = star (V i) * Qm) (t : ℝ) :
    (Matrix.trace (Qp * gkslFlow H V t Xp)).re -
        (Matrix.trace (Qm * gkslFlow H V t Xm)).re =
      (Matrix.trace (Qp * Xp)).re - (Matrix.trace (Qm * Xm)).re := by
  rw [← twoSheetTraceReadout_eq_doubledKrein_pairing,
    ← twoSheetTraceReadout_eq_doubledKrein_pairing]
  simpa only [commutantReadoutRieszVector_eq_star] using
    twoSheetCommutantReadout_gkslFlow_invariant H Qp Qm Xp Xm V
      hQpH hQpV hQpStarV hQmH hQmV hQmStarV t

/-- Joint commutant charges on the two real sheets, paired with the actual
fundamental-symmetry-conjugated Krein form. The minus sign is supplied by
`KreinSpace.kreinInner` on the second sheet. -/
def twoSheetKreinReadoutProfile {κ : Type*}
    (Qp Qm : κ → CMat) (Xp Xm : CMat) : κ → ℝ :=
  fun i => KreinSpace.kreinInner
    (to_doubled (commutantReadoutRieszVector (Qp i))
      (commutantReadoutRieszVector (Qm i)))
    (to_doubled (matrixToOperatorHilbert Xp) (matrixToOperatorHilbert Xm))

/-- In trace coordinates, the signed two-sheet Krein profile is the difference
of the two full-matrix commutant readout profiles. -/
theorem twoSheetKreinReadoutProfile_eq_traceDifference {κ : Type*}
    (Qp Qm : κ → CMat) (Xp Xm : CMat) :
    twoSheetKreinReadoutProfile Qp Qm Xp Xm =
      fun i => (Matrix.trace (Qp i * Xp)).re -
        (Matrix.trace (Qm i * Xm)).re := by
  funext i
  change KreinSpace.kreinInner
      (to_doubled (commutantReadoutRieszVector (Qp i))
        (commutantReadoutRieszVector (Qm i)))
      (to_doubled (matrixToOperatorHilbert Xp) (matrixToOperatorHilbert Xm)) = _
  rw [commutantReadoutRieszVector_eq_star,
    commutantReadoutRieszVector_eq_star]
  exact twoSheetTraceReadout_eq_doubledKrein_pairing
    (Qp i) (Qm i) Xp Xm

/-- The complete signed joint-commutant profile is conserved when both
Krein sheets evolve under the same GKSL flow. This is the profile-valued
extension of the scalar two-sheet readout invariant and keeps each charge as
a full matrix trace on its own sheet. -/
theorem twoSheetKreinReadoutProfile_gkslFlow_invariant {κ : Type*}
    (H Xp Xm : CMat) (V : ι → CMat) (Qp Qm : κ → CMat)
    (hQpH : ∀ i, Qp i * H = H * Qp i)
    (hQpV : ∀ i j, Qp i * V j = V j * Qp i)
    (hQpStarV : ∀ i j, Qp i * star (V j) = star (V j) * Qp i)
    (hQmH : ∀ i, Qm i * H = H * Qm i)
    (hQmV : ∀ i j, Qm i * V j = V j * Qm i)
    (hQmStarV : ∀ i j, Qm i * star (V j) = star (V j) * Qm i)
    (t : ℝ) :
    twoSheetKreinReadoutProfile Qp Qm
        (gkslFlow H V t Xp) (gkslFlow H V t Xm) =
      twoSheetKreinReadoutProfile Qp Qm Xp Xm := by
  rw [twoSheetKreinReadoutProfile_eq_traceDifference,
    twoSheetKreinReadoutProfile_eq_traceDifference]
  funext i
  exact twoSheetTraceReadout_gkslFlow_invariant H (Qp i) (Qm i) Xp Xm V
    (hQpH i) (hQpV i) (hQpStarV i) (hQmH i) (hQmV i) (hQmStarV i) t

/-- Any Souriau entropy and Weyl-scale potentials of the signed two-sheet
Krein profile are conserved along the paired flow. Thus the existing
potential-level leaf construction applies directly to the full doubled
profile, with no additional leaf or symplectic structure introduced here. -/
theorem twoSheetKreinProfile_preserves_souriauPotentials {κ : Type*}
    (H Xp Xm : CMat) (V : ι → CMat) (Qp Qm : κ → CMat)
    (hQpH : ∀ i, Qp i * H = H * Qp i)
    (hQpV : ∀ i j, Qp i * V j = V j * Qp i)
    (hQpStarV : ∀ i j, Qp i * star (V j) = star (V j) * Qp i)
    (hQmH : ∀ i, Qm i * H = H * Qm i)
    (hQmV : ∀ i j, Qm i * V j = V j * Qm i)
    (hQmStarV : ∀ i j, Qm i * star (V j) = star (V j) * Qm i)
    (entropyPotential weylPotential : (κ → ℝ) → ℝ) (t : ℝ) :
    entropyPotential (twoSheetKreinReadoutProfile Qp Qm
      (gkslFlow H V t Xp) (gkslFlow H V t Xm)) =
        entropyPotential (twoSheetKreinReadoutProfile Qp Qm Xp Xm) ∧
    weylPotential (twoSheetKreinReadoutProfile Qp Qm
      (gkslFlow H V t Xp) (gkslFlow H V t Xm)) =
        weylPotential (twoSheetKreinReadoutProfile Qp Qm Xp Xm) := by
  have hprofile := twoSheetKreinReadoutProfile_gkslFlow_invariant
    H Xp Xm V Qp Qm hQpH hQpV hQpStarV hQmH hQmV hQmStarV t
  exact ⟨congrArg entropyPotential hprofile,
    congrArg weylPotential hprofile⟩

/-- If both matrix-sheet trajectories have limits, the signed Krein profile
of any family of joint-commutant charges is preserved at those limits. Each
coordinate remains a full noncommutative matrix trace readout; the signature
between sheets comes from the native Krein pairing. -/
theorem twoSheetKreinReadoutProfile_preserved_at_limits
    {κ : Type*} [Fintype κ]
    (H Xp Xm rhoLimitp rhoLimitm : CMat) (V : ι → CMat)
    (Qp Qm : κ → CMat)
    (hQpH : ∀ i, Qp i * H = H * Qp i)
    (hQpV : ∀ i j, Qp i * V j = V j * Qp i)
    (hQpStarV : ∀ i j, Qp i * star (V j) = star (V j) * Qp i)
    (hQmH : ∀ i, Qm i * H = H * Qm i)
    (hQmV : ∀ i j, Qm i * V j = V j * Qm i)
    (hQmStarV : ∀ i j, Qm i * star (V j) = star (V j) * Qm i)
    (hlimp : Tendsto (fun t : ℝ => gkslFlow H V t Xp) atTop (𝓝 rhoLimitp))
    (hlimm : Tendsto (fun t : ℝ => gkslFlow H V t Xm) atTop (𝓝 rhoLimitm)) :
    twoSheetKreinReadoutProfile Qp Qm rhoLimitp rhoLimitm =
      twoSheetKreinReadoutProfile Qp Qm Xp Xm := by
  have hp :=
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.tendsto_limit_mem_jointCommutantReadoutLeaf
      H Xp rhoLimitp V Qp hQpH hQpV hQpStarV hlimp
  have hm :=
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.tendsto_limit_mem_jointCommutantReadoutLeaf
      H Xm rhoLimitm V Qm hQmH hQmV hQmStarV hlimm
  change InfoGeometry.Modular.CommutantInvariantGKSLFlow.commutantReadoutProfile
      Qp rhoLimitp =
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.commutantReadoutProfile Qp Xp at hp
  change InfoGeometry.Modular.CommutantInvariantGKSLFlow.commutantReadoutProfile
      Qm rhoLimitm =
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.commutantReadoutProfile Qm Xm at hm
  have hp_i (i : κ) : (Matrix.trace (Qp i * rhoLimitp)).re =
      (Matrix.trace (Qp i * Xp)).re := by
    have h := congrFun hp i
    change InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
      (Qp i) rhoLimitp =
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
        (Qp i) Xp at h
    simpa only [InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM_apply]
      using h
  have hm_i (i : κ) : (Matrix.trace (Qm i * rhoLimitm)).re =
      (Matrix.trace (Qm i * Xm)).re := by
    have h := congrFun hm i
    change InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
      (Qm i) rhoLimitm =
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM
        (Qm i) Xm at h
    simpa only [InfoGeometry.Modular.CommutantInvariantGKSLFlow.observableReadoutCLM_apply]
      using h
  rw [twoSheetKreinReadoutProfile_eq_traceDifference,
    twoSheetKreinReadoutProfile_eq_traceDifference]
  funext i
  rw [hp_i, hm_i]

/-- A projection jump on each full matrix sheet converges on the canonical
double-real carrier to the pair of Peirce pinchings. The `DOp` limit uses its
actual `WithLp 2` topology; no scalar or diagonal model replaces either
matrix sheet. -/
theorem twoSheetProjectionJump_kreinDefect_eq_exponential
    (P Xp Xm : CMat)
    (hP : P * P = P) (hPs : star P = P) (t : ℝ) :
    KreinSpace.kreinInner
        (to_doubled
          (matrixToOperatorHilbert
            (gkslFlow 0 (fun _ : Unit => P) t Xp -
              InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp))
          (matrixToOperatorHilbert
            (gkslFlow 0 (fun _ : Unit => P) t Xm -
              InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm)))
        (to_doubled
          (matrixToOperatorHilbert
            (gkslFlow 0 (fun _ : Unit => P) t Xp -
              InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp))
          (matrixToOperatorHilbert
            (gkslFlow 0 (fun _ : Unit => P) t Xm -
              InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm))) =
      Real.exp (-t) *
        (inner ℝ (matrixToOperatorHilbert
            (Xp - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp))
            (matrixToOperatorHilbert
              (Xp - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp)) -
         inner ℝ (matrixToOperatorHilbert
            (Xm - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm))
            (matrixToOperatorHilbert
              (Xm - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm))) := by
  have hp : gkslFlow 0 (fun _ : Unit => P) t Xp -
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp =
      (Real.exp (-t / 2) : ℝ) •
        (Xp - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp) := by
    rw [InfoGeometry.Modular.CommutantInvariantGKSLFlow.projection_jump_gkslFlow_eq_peirce_relaxation
      P Xp hP hPs t]
    module
  have hm : gkslFlow 0 (fun _ : Unit => P) t Xm -
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm =
      (Real.exp (-t / 2) : ℝ) •
        (Xm - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm) := by
    rw [InfoGeometry.Modular.CommutantInvariantGKSLFlow.projection_jump_gkslFlow_eq_peirce_relaxation
      P Xm hP hPs t]
    module
  have hmap (X : CMat) :
      matrixToOperatorHilbert ((Real.exp (-t / 2) : ℝ) • X) =
        (Real.exp (-t / 2) : ℝ) • matrixToOperatorHilbert X := by
    exact (matrixToOperatorCLM (n := n)).map_smul (Real.exp (-t / 2)) X
  rw [operatorSheets_krein_pairing, hp, hm, hmap, hmap]
  simp only [real_inner_smul_left, real_inner_smul_right]
  have he : (Real.exp (-t / 2) : ℝ) * Real.exp (-t / 2) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-t / 2) * Real.exp (-t / 2)) *
          inner ℝ (matrixToOperatorHilbert
            (Xp - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp))
            (matrixToOperatorHilbert
              (Xp - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp)) -
        (Real.exp (-t / 2) * Real.exp (-t / 2)) *
          inner ℝ (matrixToOperatorHilbert
            (Xm - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm))
            (matrixToOperatorHilbert
              (Xm - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm)) := by ring
    _ = _ := by rw [he]; ring

theorem twoSheetProjectionJump_gkslFlow_tendsto_peircePinching
    (P Xp Xm : CMat)
    (hP : P * P = P) (hPs : star P = P) :
    Tendsto
      (fun t : ℝ => to_doubled
        (matrixToOperatorHilbert
          (gkslFlow 0 (fun _ : Unit => P) t Xp))
        (matrixToOperatorHilbert
          (gkslFlow 0 (fun _ : Unit => P) t Xm)))
      atTop
      (𝓝 (to_doubled
        (matrixToOperatorHilbert
          (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp))
        (matrixToOperatorHilbert
          (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm)))) := by
  have hp := InfoGeometry.Modular.CommutantInvariantGKSLFlow.projection_jump_gkslFlow_tendsto_peircePinching
    P Xp hP hPs
  have hm := InfoGeometry.Modular.CommutantInvariantGKSLFlow.projection_jump_gkslFlow_tendsto_peircePinching
    P Xm hP hPs
  have hp' := ((matrixToOperatorCLM (n := n)).continuous.tendsto
      (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp)).comp hp
  have hm' := ((matrixToOperatorCLM (n := n)).continuous.tendsto
      (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm)).comp hm
  have hpair := hp'.prodMk_nhds hm'
  have hdouble := ((pairToDoubledCLM (n := n)).continuous.tendsto
      (matrixToOperatorHilbert
          (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp),
        matrixToOperatorHilbert
          (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm))).comp hpair
  simpa [Function.comp_def, pairToDoubledCLM] using hdouble

/-- The two full-matrix projection-jump trajectories represented on the
canonical double-real carrier. -/
def twoSheetProjectionJumpOrbit (P Xp Xm : CMat) : ℝ → DOp :=
  fun t => to_doubled
    (matrixToOperatorHilbert (gkslFlow 0 (fun _ : Unit => P) t Xp))
    (matrixToOperatorHilbert (gkslFlow 0 (fun _ : Unit => P) t Xm))

/-- The two-sheet double-real state obtained from the full-matrix Peirce
pinchings. -/
def twoSheetProjectionJumpLimit (P Xp Xm : CMat) : DOp :=
  to_doubled
    (matrixToOperatorHilbert
      (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp))
    (matrixToOperatorHilbert
      (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm))

/-- The initial full-matrix pair on the canonical double-real carrier. -/
def twoSheetProjectionJumpInitial (Xp Xm : CMat) : DOp :=
  to_doubled (matrixToOperatorHilbert Xp) (matrixToOperatorHilbert Xm)

/-- Exact affine relaxation identity on the actual double-real state space:
the trajectory is its Peirce limit plus an exponentially scaled full-matrix
displacement. -/
theorem twoSheetProjectionJumpOrbit_eq_limit_add_initial_displacement
    (P Xp Xm : CMat) (hP : P * P = P) (hPs : star P = P) (t : ℝ) :
    twoSheetProjectionJumpOrbit P Xp Xm t =
      twoSheetProjectionJumpLimit P Xp Xm +
        (Real.exp (-t / 2) : ℝ) •
          (twoSheetProjectionJumpInitial Xp Xm -
            twoSheetProjectionJumpLimit P Xp Xm) := by
  apply DoubledSpace.ext
  · change matrixToOperatorHilbert (gkslFlow 0 (fun _ : Unit => P) t Xp) = _
    rw [InfoGeometry.Modular.CommutantInvariantGKSLFlow.projection_jump_gkslFlow_eq_peirce_relaxation
      P Xp hP hPs t]
    simp only [twoSheetProjectionJumpLimit, twoSheetProjectionJumpInitial,
      WithLp.add_fst, WithLp.smul_fst, WithLp.sub_fst, fst_to_doubled]
    have hsmul : matrixToOperatorHilbert
        ((Real.exp (-t / 2) : ℝ) • (Xp -
          InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp)) =
        (Real.exp (-t / 2) : ℝ) • matrixToOperatorHilbert
          (Xp - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp) :=
      (matrixToOperatorCLM (n := n)).map_smul _ _
    rw [matrixToOperatorHilbert_add, hsmul, matrixToOperatorHilbert_sub]
  · change matrixToOperatorHilbert (gkslFlow 0 (fun _ : Unit => P) t Xm) = _
    rw [InfoGeometry.Modular.CommutantInvariantGKSLFlow.projection_jump_gkslFlow_eq_peirce_relaxation
      P Xm hP hPs t]
    simp only [twoSheetProjectionJumpLimit, twoSheetProjectionJumpInitial,
      WithLp.add_snd, WithLp.smul_snd, WithLp.sub_snd, snd_to_doubled]
    have hsmul : matrixToOperatorHilbert
        ((Real.exp (-t / 2) : ℝ) • (Xm -
          InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm)) =
        (Real.exp (-t / 2) : ℝ) • matrixToOperatorHilbert
          (Xm - InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm) :=
      (matrixToOperatorCLM (n := n)).map_smul _ _
    rw [matrixToOperatorHilbert_add, hsmul, matrixToOperatorHilbert_sub]

/-- The doubled-real Krein pairing of two full-matrix projection-jump
trajectories converges to the pairing of their sheetwise Peirce limits. The
pairing is defined by the fundamental symmetry, retaining the negative-sheet
sign. -/
theorem twoSheetProjectionJump_kreinPairing_tendsto_peircePinching
    (P Xp Xm Yp Ym : CMat) (hP : P * P = P) (hPs : star P = P) :
    Tendsto
      (fun t => KreinSpace.kreinInner
        (twoSheetProjectionJumpOrbit P Xp Xm t)
        (twoSheetProjectionJumpOrbit P Yp Ym t))
      atTop
      (𝓝 (KreinSpace.kreinInner
        (twoSheetProjectionJumpLimit P Xp Xm)
        (twoSheetProjectionJumpLimit P Yp Ym))) := by
  have hleft := twoSheetProjectionJump_gkslFlow_tendsto_peircePinching
    P Xp Xm hP hPs
  have hright := twoSheetProjectionJump_gkslFlow_tendsto_peircePinching
    P Yp Ym hP hPs
  exact KreinSpace.tendsto_kreinInner_of_tendsto hleft hright

/-- Exact finite-time expansion of the double-real Krein pairing. The two
first-order cross terms and the quadratic displacement term show precisely
how the pairing approaches its value on the Peirce limits. -/
theorem twoSheetProjectionJump_kreinPairing_eq_affine_expansion
    (P Xp Xm Yp Ym : CMat) (hP : P * P = P) (hPs : star P = P) (t : ℝ) :
    KreinSpace.kreinInner
        (twoSheetProjectionJumpOrbit P Xp Xm t)
        (twoSheetProjectionJumpOrbit P Yp Ym t) =
      KreinSpace.kreinInner
          (twoSheetProjectionJumpLimit P Xp Xm)
          (twoSheetProjectionJumpLimit P Yp Ym) +
        Real.exp (-t / 2) *
          KreinSpace.kreinInner
            (twoSheetProjectionJumpInitial Xp Xm -
              twoSheetProjectionJumpLimit P Xp Xm)
            (twoSheetProjectionJumpLimit P Yp Ym) +
        Real.exp (-t / 2) *
          KreinSpace.kreinInner
            (twoSheetProjectionJumpLimit P Xp Xm)
            (twoSheetProjectionJumpInitial Yp Ym -
              twoSheetProjectionJumpLimit P Yp Ym) +
        Real.exp (-t) *
          KreinSpace.kreinInner
            (twoSheetProjectionJumpInitial Xp Xm -
              twoSheetProjectionJumpLimit P Xp Xm)
            (twoSheetProjectionJumpInitial Yp Ym -
              twoSheetProjectionJumpLimit P Yp Ym) := by
  rw [twoSheetProjectionJumpOrbit_eq_limit_add_initial_displacement
      P Xp Xm hP hPs t,
    twoSheetProjectionJumpOrbit_eq_limit_add_initial_displacement
      P Yp Ym hP hPs t]
  simp only [KreinSpace.kreinInner_add_left, KreinSpace.kreinInner_add_right,
    KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right]
  have h_exp : (Real.exp (-t / 2)) ^ 2 = Real.exp (-t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [← h_exp]
  ring

/-- Quantitative convergence of the full two-sheet Krein pairing. Its error is
controlled by the Hilbert norms of the initial displacements and Peirce
limits, with the cross terms decaying at rate `exp (-t / 2)` and the quadratic
term at rate `exp (-t)`. -/
theorem abs_twoSheetProjectionJump_kreinPairing_sub_limit_le
    (P Xp Xm Yp Ym : CMat) (hP : P * P = P) (hPs : star P = P)
    (t : ℝ) :
    |KreinSpace.kreinInner
        (twoSheetProjectionJumpOrbit P Xp Xm t)
        (twoSheetProjectionJumpOrbit P Yp Ym t) -
      KreinSpace.kreinInner
        (twoSheetProjectionJumpLimit P Xp Xm)
        (twoSheetProjectionJumpLimit P Yp Ym)| ≤
      Real.exp (-t / 2) *
          (‖twoSheetProjectionJumpInitial Xp Xm -
              twoSheetProjectionJumpLimit P Xp Xm‖ *
            ‖twoSheetProjectionJumpLimit P Yp Ym‖ +
           ‖twoSheetProjectionJumpLimit P Xp Xm‖ *
            ‖twoSheetProjectionJumpInitial Yp Ym -
              twoSheetProjectionJumpLimit P Yp Ym‖) +
        Real.exp (-t) *
          (‖twoSheetProjectionJumpInitial Xp Xm -
              twoSheetProjectionJumpLimit P Xp Xm‖ *
            ‖twoSheetProjectionJumpInitial Yp Ym -
              twoSheetProjectionJumpLimit P Yp Ym‖) := by
  let x₀ := twoSheetProjectionJumpLimit P Xp Xm
  let y₀ := twoSheetProjectionJumpLimit P Yp Ym
  let dx := twoSheetProjectionJumpInitial Xp Xm - x₀
  let dy := twoSheetProjectionJumpInitial Yp Ym - y₀
  let a := Real.exp (-t / 2)
  let b := Real.exp (-t)
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have hb : 0 ≤ b := (Real.exp_pos _).le
  have hexp := twoSheetProjectionJump_kreinPairing_eq_affine_expansion
    P Xp Xm Yp Ym hP hPs t
  have hdiff :
      KreinSpace.kreinInner (twoSheetProjectionJumpOrbit P Xp Xm t)
          (twoSheetProjectionJumpOrbit P Yp Ym t) -
        KreinSpace.kreinInner x₀ y₀ =
      a * KreinSpace.kreinInner dx y₀ +
        a * KreinSpace.kreinInner x₀ dy +
        b * KreinSpace.kreinInner dx dy := by
    rw [hexp]
    dsimp [a, b, dx, dy, x₀, y₀]
    ring
  rw [hdiff]
  calc
    |a * KreinSpace.kreinInner dx y₀ +
        a * KreinSpace.kreinInner x₀ dy +
        b * KreinSpace.kreinInner dx dy| ≤
      |a * KreinSpace.kreinInner dx y₀| +
        |a * KreinSpace.kreinInner x₀ dy| +
        |b * KreinSpace.kreinInner dx dy| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = a * |KreinSpace.kreinInner dx y₀| +
        a * |KreinSpace.kreinInner x₀ dy| +
        b * |KreinSpace.kreinInner dx dy| := by
          rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg ha,
            abs_mul, abs_of_nonneg hb]
    _ ≤ a * (‖dx‖ * ‖y₀‖ + ‖x₀‖ * ‖dy‖) +
        b * (‖dx‖ * ‖dy‖) := by
          have h₁ := KreinSpace.abs_kreinInner_le_norm dx y₀
          have h₂ := KreinSpace.abs_kreinInner_le_norm x₀ dy
          have h₃ := KreinSpace.abs_kreinInner_le_norm dx dy
          have hcross := add_le_add
            (mul_le_mul_of_nonneg_left h₁ ha)
            (mul_le_mul_of_nonneg_left h₂ ha)
          have hquad := mul_le_mul_of_nonneg_left h₃ hb
          dsimp [a, b] at *
          nlinarith

/-- The full-matrix Peirce pinching transported to the real Hilbert carrier
of matrix entries. The pinching still acts by its ordered two-sided matrix
products; this definition only changes the carrier. -/
def projectionJumpPeircePinchingOperatorCLM (P : CMat) :
    OpHilbert →L[ℝ] OpHilbert :=
  (matrixToOperatorCLM (n := n)).comp
    ((InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinchingCLM
      P).comp (operatorToMatrixCLM (n := n)))

@[simp] theorem projectionJumpPeircePinchingOperatorCLM_apply
    (P : CMat) (X : OpHilbert) :
    projectionJumpPeircePinchingOperatorCLM P X =
      matrixToOperatorHilbert
        (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching
          P (operatorHilbertToMatrix X)) := by
  simp [projectionJumpPeircePinchingOperatorCLM]

/-- The matrix-entry realization of the projection-jump flow has the exact
operator-valued relaxation formula inherited from the full noncommutative
matrix owner. -/
theorem schrodingerOperatorFlow_projectionJump_relaxation
    (P : CMat) (hP : P * P = P) (hPs : star P = P) (t : ℝ) :
    schrodingerOperatorFlow 0 (fun _ : Unit => P) t =
      projectionJumpPeircePinchingOperatorCLM P +
        (Real.exp (-t / 2) : ℝ) •
          ((ContinuousLinearMap.id ℝ OpHilbert) -
            projectionJumpPeircePinchingOperatorCLM P) := by
  apply ContinuousLinearMap.ext
  intro X
  apply matrixOperatorEquiv.symm.injective
  change operatorHilbertToMatrix
      (schrodingerOperatorFlow 0 (fun _ : Unit => P) t X) = _
  rw [operatorToMatrix_schrodingerOperatorFlow,
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.projection_jump_gkslFlow_eq_peirce_relaxation P
      (operatorHilbertToMatrix X) hP hPs t]
  simp [projectionJumpPeircePinchingOperatorCLM_apply,
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching,
    matrixOperatorEquiv]

/-- Apply the matrix-entry projection-jump flow to both operator coordinates
of the canonical double-real carrier. -/
def doubledProjectionJumpOperatorFlowCLM (P : CMat) (t : ℝ) :
    DOp →L[ℝ] DOp :=
  sheetDiagonalLift (schrodingerOperatorFlow 0 (fun _ : Unit => P) t)

/-- The two-sheet Peirce pinching on the canonical double-real operator
carrier. Its two full matrix coordinates are independently pinched. -/
def doubledProjectionJumpPeircePinchingCLM (P : CMat) :
    DOp →L[ℝ] DOp :=
  sheetDiagonalLift (projectionJumpPeircePinchingOperatorCLM P)

/-- The matrix-defined paired orbit is exactly the doubled continuous-linear
operator flow applied to its full-matrix initial state. This identifies the
pointwise and operator-map constructions without changing either sheet. -/
theorem twoSheetProjectionJumpOrbit_eq_operatorFlow_apply
    (P Xp Xm : CMat) (t : ℝ) :
    twoSheetProjectionJumpOrbit P Xp Xm t =
      doubledProjectionJumpOperatorFlowCLM P t
        (twoSheetProjectionJumpInitial Xp Xm) := by
  simp [twoSheetProjectionJumpOrbit, twoSheetProjectionJumpInitial,
    doubledProjectionJumpOperatorFlowCLM, sheetDiagonalLift_apply,
    schrodingerOperatorFlow_matrixToOperator]

omit [DecidableEq n] in
@[simp] theorem sheetDiagonalLift_add (T S : OpHilbert →L[ℝ] OpHilbert) :
    sheetDiagonalLift (T + S) = sheetDiagonalLift T + sheetDiagonalLift S := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> rfl
  rw [hu]
  simp only [sheetDiagonalLift_apply, _root_.add_apply]
  rw [← WithLp.toLp_add (p := (2 : ENNReal))]
  rfl

omit [DecidableEq n] in
@[simp] theorem sheetDiagonalLift_smul (r : ℝ) (T : OpHilbert →L[ℝ] OpHilbert) :
    sheetDiagonalLift (r • T) = r • sheetDiagonalLift T := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> rfl
  rw [hu]
  simp only [sheetDiagonalLift_apply, _root_.smul_apply]
  rw [← WithLp.toLp_smul (p := (2 : ENNReal))]
  rfl

omit [DecidableEq n] in
@[simp] theorem sheetDiagonalLift_id :
    sheetDiagonalLift (ContinuousLinearMap.id ℝ OpHilbert) =
      (ContinuousLinearMap.id ℝ DOp) := by
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> rfl
  rw [hu]
  simp [sheetDiagonalLift_apply]

omit [DecidableEq n] in
theorem sheetDiagonalLift_sub (T S : OpHilbert →L[ℝ] OpHilbert) :
    sheetDiagonalLift (T - S) = sheetDiagonalLift T - sheetDiagonalLift S := by
  rw [sub_eq_add_neg, sheetDiagonalLift_add, ← neg_one_smul ℝ S,
    sheetDiagonalLift_smul]
  module

/-- Exact operator-norm decay of the full doubled projection-jump semigroup
toward its Peirce pinching. This is an equality on the complete continuous-
linear-map space, not merely pointwise convergence on selected matrices. -/
theorem norm_doubledProjectionJumpOperatorFlow_sub_peircePinching
    (P : CMat) (hP : P * P = P) (hPs : star P = P) (t : ℝ) :
    ‖doubledProjectionJumpOperatorFlowCLM P t -
        doubledProjectionJumpPeircePinchingCLM P‖ =
      Real.exp (-t / 2) *
        ‖(ContinuousLinearMap.id ℝ DOp) -
          doubledProjectionJumpPeircePinchingCLM P‖ := by
  have hformula : doubledProjectionJumpOperatorFlowCLM P t =
      doubledProjectionJumpPeircePinchingCLM P +
        (Real.exp (-t / 2) : ℝ) •
          ((ContinuousLinearMap.id ℝ DOp) -
            doubledProjectionJumpPeircePinchingCLM P) := by
    rw [doubledProjectionJumpOperatorFlowCLM,
      schrodingerOperatorFlow_projectionJump_relaxation P hP hPs t,
      doubledProjectionJumpPeircePinchingCLM,
      sheetDiagonalLift_add, sheetDiagonalLift_smul,
      sheetDiagonalLift_sub, sheetDiagonalLift_id]
  rw [hformula, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The projection-jump flow converges in operator norm on the complete
double-real matrix-operator carrier. The limit map is the sheetwise Peirce
pinching, not a scalar or diagonal restriction. The topology is the Hilbert
operator norm underlying `DOp`; the associated indefinite pairing remains
`KreinSpace.kreinInner`, defined through the fundamental symmetry. -/
theorem twoSheetProjectionJumpOperatorFlow_tendsto_peircePinchingCLM
    (P : CMat) (hP : P * P = P) (hPs : star P = P) :
    Tendsto (fun t : ℝ => doubledProjectionJumpOperatorFlowCLM P t) atTop
      (𝓝 (doubledProjectionJumpPeircePinchingCLM P)) := by
  have hformula : ∀ t : ℝ,
      doubledProjectionJumpOperatorFlowCLM P t =
        doubledProjectionJumpPeircePinchingCLM P +
          (Real.exp (-t / 2) : ℝ) •
            ((ContinuousLinearMap.id ℝ DOp) -
              doubledProjectionJumpPeircePinchingCLM P) := by
    intro t
    rw [doubledProjectionJumpOperatorFlowCLM,
      schrodingerOperatorFlow_projectionJump_relaxation P hP hPs t,
      doubledProjectionJumpPeircePinchingCLM,
      sheetDiagonalLift_add, sheetDiagonalLift_smul,
      sheetDiagonalLift_sub, sheetDiagonalLift_id]
  have hlin : Tendsto (fun t : ℝ => -t / 2) atTop atBot := by
    simpa using ((tendsto_neg_atTop_atBot.comp tendsto_id).atBot_div_const
      (by norm_num : (0 : ℝ) < 2))
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hsmul : Tendsto
      (fun t : ℝ => (Real.exp (-t / 2) : ℝ) •
        ((ContinuousLinearMap.id ℝ DOp) -
          doubledProjectionJumpPeircePinchingCLM P)) atTop (𝓝 0) := by
    have h := hexp.smul_const
      ((ContinuousLinearMap.id ℝ DOp) -
        doubledProjectionJumpPeircePinchingCLM P)
    rw [zero_smul ℝ
      ((ContinuousLinearMap.id ℝ DOp) -
        doubledProjectionJumpPeircePinchingCLM P)] at h
    exact h
  have hfun : (fun t : ℝ => doubledProjectionJumpOperatorFlowCLM P t) =
      (fun t => doubledProjectionJumpPeircePinchingCLM P +
        (Real.exp (-t / 2) : ℝ) •
          ((ContinuousLinearMap.id ℝ DOp) -
            doubledProjectionJumpPeircePinchingCLM P)) := by
    funext t
    exact hformula t
  rw [hfun]
  simpa using (tendsto_const_nhds.add hsmul)

/-- A limit in the canonical double-real topology induces the corresponding
matrix limits on both sheets. This uses the continuous product projections
and the matrix-entry linear equivalence, without changing the carrier or its
Krein metric. -/
theorem doubledGKSL_tendsto_implies_sheet_limits
    (H Xp Xm rhoLimitp rhoLimitm : CMat) (V : ι → CMat)
    (hlim : Tendsto
      (fun t : ℝ => to_doubled
        (matrixToOperatorHilbert (gkslFlow H V t Xp))
        (matrixToOperatorHilbert (gkslFlow H V t Xm)))
      atTop
      (𝓝 (to_doubled (matrixToOperatorHilbert rhoLimitp)
        (matrixToOperatorHilbert rhoLimitm)))) :
    Tendsto (fun t : ℝ => gkslFlow H V t Xp) atTop (𝓝 rhoLimitp) ∧
    Tendsto (fun t : ℝ => gkslFlow H V t Xm) atTop (𝓝 rhoLimitm) := by
  constructor
  · have h := ((operatorToMatrixCLM (n := n)).continuous.comp
        (WithLp.continuous_fst (p := (2 : ENNReal))
          (α := OpHilbert) (β := OpHilbert))).tendsto
          (to_doubled (matrixToOperatorHilbert rhoLimitp)
            (matrixToOperatorHilbert rhoLimitm)) |>.comp hlim
    simpa [Function.comp_def, operatorToMatrixCLM, matrixOperatorEquiv] using h
  · have h := ((operatorToMatrixCLM (n := n)).continuous.comp
        (WithLp.continuous_snd (p := (2 : ENNReal))
          (α := OpHilbert) (β := OpHilbert))).tendsto
          (to_doubled (matrixToOperatorHilbert rhoLimitp)
            (matrixToOperatorHilbert rhoLimitm)) |>.comp hlim
    simpa [Function.comp_def, operatorToMatrixCLM, matrixOperatorEquiv] using h

/-- A paired GKSL orbit limit in the doubled topology preserves every
coordinate of the signed two-sheet Krein charge profile. -/
theorem twoSheetKreinReadoutProfile_preserved_at_doubled_limit
    {κ : Type*} [Fintype κ]
    (H Xp Xm rhoLimitp rhoLimitm : CMat) (V : ι → CMat)
    (Qp Qm : κ → CMat)
    (hQpH : ∀ i, Qp i * H = H * Qp i)
    (hQpV : ∀ i j, Qp i * V j = V j * Qp i)
    (hQpStarV : ∀ i j, Qp i * star (V j) = star (V j) * Qp i)
    (hQmH : ∀ i, Qm i * H = H * Qm i)
    (hQmV : ∀ i j, Qm i * V j = V j * Qm i)
    (hQmStarV : ∀ i j, Qm i * star (V j) = star (V j) * Qm i)
    (hlim : Tendsto
      (fun t : ℝ => to_doubled
        (matrixToOperatorHilbert (gkslFlow H V t Xp))
        (matrixToOperatorHilbert (gkslFlow H V t Xm)))
      atTop
      (𝓝 (to_doubled (matrixToOperatorHilbert rhoLimitp)
        (matrixToOperatorHilbert rhoLimitm)))) :
    twoSheetKreinReadoutProfile Qp Qm rhoLimitp rhoLimitm =
      twoSheetKreinReadoutProfile Qp Qm Xp Xm := by
  rcases doubledGKSL_tendsto_implies_sheet_limits
      H Xp Xm rhoLimitp rhoLimitm V hlim with ⟨hlimp, hlimm⟩
  exact twoSheetKreinReadoutProfile_preserved_at_limits
    H Xp Xm rhoLimitp rhoLimitm V Qp Qm hQpH hQpV hQpStarV
    hQmH hQmV hQmStarV hlimp hlimm

/-- The two-sheet Peirce limit retains the complete signed joint-commutant
profile. This uses the `KreinSpace.kreinInner` pairing, including its
fundamental-symmetry minus sign on the second sheet. -/
theorem twoSheetProjectionJump_peircePinching_preserves_kreinProfile
    {κ : Type*} [Fintype κ]
    (P Xp Xm : CMat) (Qp Qm : κ → CMat)
    (hP : P * P = P) (hPs : star P = P)
    (hQp : ∀ i, Qp i * P = P * Qp i)
    (hQm : ∀ i, Qm i * P = P * Qm i) :
    twoSheetKreinReadoutProfile Qp Qm
        (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp)
        (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm) =
      twoSheetKreinReadoutProfile Qp Qm Xp Xm := by
  apply twoSheetKreinReadoutProfile_preserved_at_doubled_limit
    (ι := Unit) (H := (0 : CMat)) (Xp := Xp) (Xm := Xm)
    (rhoLimitp := InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp)
    (rhoLimitm := InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm)
    (V := fun _ : Unit => P) (Qp := Qp) (Qm := Qm)
    (hQpH := by intro i; simp)
    (hQpV := by intro i j; exact hQp i)
    (hQpStarV := by intro i j; rw [hPs]; exact hQp i)
    (hQmH := by intro i; simp)
    (hQmV := by intro i j; exact hQm i)
    (hQmStarV := by intro i j; rw [hPs]; exact hQm i)
    (twoSheetProjectionJump_gkslFlow_tendsto_peircePinching
      P Xp Xm hP hPs)

/-- Every scalar entropy and Weyl potential of the signed Krein charge profile
has the same value at the explicit two-sheet Peirce limit as at the initial
pair. The profile uses the fundamental-symmetry-conjugated pairing on the
canonical doubled real carrier. -/
theorem twoSheetProjectionJump_peircePinching_preserves_potentials
    {κ : Type*} [Fintype κ]
    (P Xp Xm : CMat) (Qp Qm : κ → CMat)
    (hP : P * P = P) (hPs : star P = P)
    (hQp : ∀ i, Qp i * P = P * Qp i)
    (hQm : ∀ i, Qm i * P = P * Qm i)
    (entropyPotential weylPotential : (κ → ℝ) → ℝ) :
    entropyPotential (twoSheetKreinReadoutProfile Qp Qm
      (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp)
      (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm)) =
        entropyPotential (twoSheetKreinReadoutProfile Qp Qm Xp Xm) ∧
    weylPotential (twoSheetKreinReadoutProfile Qp Qm
      (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xp)
      (InfoGeometry.Modular.CommutantInvariantGKSLFlow.projectionJumpPeircePinching P Xm)) =
        weylPotential (twoSheetKreinReadoutProfile Qp Qm Xp Xm) := by
  have hprofile := twoSheetProjectionJump_peircePinching_preserves_kreinProfile
    P Xp Xm Qp Qm hP hPs hQp hQm
  exact ⟨congrArg entropyPotential hprofile,
    congrArg weylPotential hprofile⟩

/-- Every paired orbit limit in the doubled Krein topology satisfies the
entropy/Weyl potential levels selected by the initial pair. The potentials
act on the signed profile formed with `KreinSpace.kreinInner`, retaining the
fundamental-symmetry sign on the second sheet. -/
theorem doubledGKSL_limit_satisfies_souriauPotential_levels
    {κ : Type*} [Fintype κ]
    (H Xp Xm rhoLimitp rhoLimitm : CMat) (V : ι → CMat)
    (Qp Qm : κ → CMat)
    (hQpH : ∀ i, Qp i * H = H * Qp i)
    (hQpV : ∀ i j, Qp i * V j = V j * Qp i)
    (hQpStarV : ∀ i j, Qp i * star (V j) = star (V j) * Qp i)
    (hQmH : ∀ i, Qm i * H = H * Qm i)
    (hQmV : ∀ i j, Qm i * V j = V j * Qm i)
    (hQmStarV : ∀ i j, Qm i * star (V j) = star (V j) * Qm i)
    (entropyPotential weylPotential : (κ → ℝ) → ℝ)
    (hlim : Tendsto
      (fun t : ℝ => to_doubled
        (matrixToOperatorHilbert (gkslFlow H V t Xp))
        (matrixToOperatorHilbert (gkslFlow H V t Xm)))
      atTop
      (𝓝 (to_doubled (matrixToOperatorHilbert rhoLimitp)
        (matrixToOperatorHilbert rhoLimitm)))) :
    entropyPotential (twoSheetKreinReadoutProfile Qp Qm rhoLimitp rhoLimitm) =
      entropyPotential (twoSheetKreinReadoutProfile Qp Qm Xp Xm) ∧
    weylPotential (twoSheetKreinReadoutProfile Qp Qm rhoLimitp rhoLimitm) =
      weylPotential (twoSheetKreinReadoutProfile Qp Qm Xp Xm) := by
  have hprofile := twoSheetKreinReadoutProfile_preserved_at_doubled_limit
    H Xp Xm rhoLimitp rhoLimitm V Qp Qm hQpH hQpV hQpStarV
    hQmH hQmV hQmStarV hlim
  exact ⟨congrArg entropyPotential hprofile,
    congrArg weylPotential hprofile⟩

/-- A mismatch in the signed joint-commutant profile rules out convergence of
the paired orbit in the canonical doubled real Hilbert topology. The two
matrix components are recovered by the continuous projections of the double
and the inverse matrix-entry equivalence. -/
theorem not_tendsto_twoSheetGKSL_of_kreinProfile_ne
    {κ : Type*} [Fintype κ]
    (H Xp Xm rhoLimitp rhoLimitm : CMat) (V : ι → CMat)
    (Qp Qm : κ → CMat)
    (hQpH : ∀ i, Qp i * H = H * Qp i)
    (hQpV : ∀ i j, Qp i * V j = V j * Qp i)
    (hQpStarV : ∀ i j, Qp i * star (V j) = star (V j) * Qp i)
    (hQmH : ∀ i, Qm i * H = H * Qm i)
    (hQmV : ∀ i j, Qm i * V j = V j * Qm i)
    (hQmStarV : ∀ i j, Qm i * star (V j) = star (V j) * Qm i)
    (hne : twoSheetKreinReadoutProfile Qp Qm rhoLimitp rhoLimitm ≠
      twoSheetKreinReadoutProfile Qp Qm Xp Xm) :
    ¬ Tendsto
      (fun t : ℝ => to_doubled
        (matrixToOperatorHilbert (gkslFlow H V t Xp))
        (matrixToOperatorHilbert (gkslFlow H V t Xm)))
      atTop
      (𝓝 (to_doubled (matrixToOperatorHilbert rhoLimitp)
        (matrixToOperatorHilbert rhoLimitm))) := by
  intro hlim
  have hprof := twoSheetKreinReadoutProfile_preserved_at_doubled_limit
    H Xp Xm rhoLimitp rhoLimitm V Qp Qm hQpH hQpV hQpStarV
    hQmH hQmV hQmStarV hlim
  exact hne hprof

/-- The joint commutant charge profile expressed entirely through the
fundamental-symmetry-conjugated pairing on the doubled real Krein carrier. -/
def commutantKreinReadoutProfile {κ : Type*}
    (Q : κ → CMat) (X : CMat) : κ → ℝ :=
  fun i => KreinSpace.kreinInner
    (to_doubled (commutantReadoutRieszVector (Q i)) 0)
    (to_doubled (matrixToOperatorHilbert X) 0)

/-- The Krein-coordinate charge profile is exactly the existing NESS
commutant profile, coordinate by coordinate. -/
theorem commutantKreinReadoutProfile_eq_commutantReadoutProfile
    {κ : Type*} (Q : κ → CMat) (X : CMat) :
    commutantKreinReadoutProfile Q X =
      InfoGeometry.Modular.CommutantInvariantGKSLFlow.commutantReadoutProfile Q X := by
  funext i
  exact commutantReadout_eq_doubledKrein_pairing (Q i) X

/-- A mismatch in the complete Krein-paired joint-commutant profile excludes
the proposed limit of the full-matrix GKSL orbit. The family may encode
several operator charges; each charge need only commute with the generator's
Hamiltonian and jumps. -/
theorem not_tendsto_gkslFlow_of_kreinProfile_ne
    {κ : Type*} [Fintype κ]
    (H X rhoLimit : CMat) (V : ι → CMat) (Q : κ → CMat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (hne : commutantKreinReadoutProfile Q X ≠
      commutantKreinReadoutProfile Q rhoLimit) :
    ¬ Tendsto (fun t : ℝ => gkslFlow H V t X) atTop (𝓝 rhoLimit) := by
  intro hlim
  have hmatrix :=
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.tendsto_limit_mem_jointCommutantReadoutLeaf
      H X rhoLimit V Q hQH hQV hQstarV hlim
  have hprofile : commutantKreinReadoutProfile Q rhoLimit =
      commutantKreinReadoutProfile Q X := by
    rw [commutantKreinReadoutProfile_eq_commutantReadoutProfile,
      commutantKreinReadoutProfile_eq_commutantReadoutProfile]
    exact hmatrix
  exact hne hprofile.symm

/-- Any scalar potential of the joint commutant profile can be evaluated
equivalently using the doubled Krein pairing. -/
theorem nessPotentialReadout_eq_kreinProfile {κ : Type*}
    (Q : κ → CMat) (potential : (κ → ℝ) → ℝ) (X : CMat) :
    InfoGeometry.Modular.NESSCommutantPotentialLeaves.potentialReadout
        Q potential X = potential (commutantKreinReadoutProfile Q X) := by
  unfold InfoGeometry.Modular.NESSCommutantPotentialLeaves.potentialReadout
  rw [commutantKreinReadoutProfile_eq_commutantReadoutProfile]

/-- The existing Souriau entropy/Weyl leaf has an exact description in terms
of its two Krein-paired conserved profiles. This identifies the established
leaf rather than defining a second geometric leaf. -/
theorem mem_souriauLeaf_iff_kreinProfiles {κ : Type*}
    (Q : κ → CMat) (entropyPotential weylPotential : (κ → ℝ) → ℝ)
    (X Y : CMat) :
    Y ∈ (InfoGeometry.Modular.NESSCommutantPotentialLeaves.souriauLeafOfCommutantPotentials
      Q entropyPotential weylPotential X).carrier ↔
      (entropyPotential (commutantKreinReadoutProfile Q Y) =
        entropyPotential (commutantKreinReadoutProfile Q X) ∧
       weylPotential (commutantKreinReadoutProfile Q Y) =
        weylPotential (commutantKreinReadoutProfile Q X)) := by
  unfold InfoGeometry.Modular.NESSCommutantPotentialLeaves.souriauLeafOfCommutantPotentials
  simp only [Set.mem_ofPred_eq]
  rw [nessPotentialReadout_eq_kreinProfile,
    nessPotentialReadout_eq_kreinProfile,
    nessPotentialReadout_eq_kreinProfile,
    nessPotentialReadout_eq_kreinProfile]

/-- Any norm limit of a full-matrix GKSL orbit lies in the existing Souriau
leaf when that leaf is read through the double-real Krein charge profile.
The only dynamical input is the already established matrix commutant-limit
theorem; this bridge changes its coordinates using the fundamental-symmetry
pairing and asserts no additional symplectic or convergence property. -/
theorem tendsto_limit_mem_souriauLeaf_viaKreinProfiles {κ : Type*}
    (H X rhoLimit : CMat) (V : ι → CMat) (Q : κ → CMat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (entropyPotential weylPotential : (κ → ℝ) → ℝ)
    (hlim : Tendsto (fun t : ℝ => gkslFlow H V t X) atTop (𝓝 rhoLimit)) :
    rhoLimit ∈
        (InfoGeometry.Modular.NESSCommutantPotentialLeaves.souriauLeafOfCommutantPotentials
          Q entropyPotential weylPotential X).carrier ∧
      entropyPotential (commutantKreinReadoutProfile Q rhoLimit) =
        entropyPotential (commutantKreinReadoutProfile Q X) ∧
      weylPotential (commutantKreinReadoutProfile Q rhoLimit) =
        weylPotential (commutantKreinReadoutProfile Q X) := by
  have hmatrix :=
    InfoGeometry.Modular.CommutantInvariantGKSLFlow.tendsto_limit_mem_jointCommutantReadoutLeaf
      H X rhoLimit V Q hQH hQV hQstarV hlim
  have hprofile : commutantKreinReadoutProfile Q rhoLimit =
      commutantKreinReadoutProfile Q X := by
    rw [commutantKreinReadoutProfile_eq_commutantReadoutProfile,
      commutantKreinReadoutProfile_eq_commutantReadoutProfile]
    exact hmatrix
  refine ⟨?_, ?_⟩
  · rw [mem_souriauLeaf_iff_kreinProfiles]
    exact ⟨congrArg entropyPotential hprofile,
      congrArg weylPotential hprofile⟩
  · exact ⟨congrArg entropyPotential hprofile,
      congrArg weylPotential hprofile⟩

/-- The already established Souriau entropy and Weyl potentials are both
constant along the GKSL orbit when evaluated on the doubled Krein charge
profile. This is the profile-level bridge to the existing Souriau leaf. -/
theorem gkslFlow_preserves_souriauPotentials_viaKreinProfiles
    {κ : Type*} (H X : CMat) (V : ι → CMat) (Q : κ → CMat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (entropyPotential weylPotential : (κ → ℝ) → ℝ) (t : ℝ) :
    entropyPotential (commutantKreinReadoutProfile Q (gkslFlow H V t X)) =
      entropyPotential (commutantKreinReadoutProfile Q X) ∧
    weylPotential (commutantKreinReadoutProfile Q (gkslFlow H V t X)) =
      weylPotential (commutantKreinReadoutProfile Q X) := by
  constructor
  · rw [← nessPotentialReadout_eq_kreinProfile Q entropyPotential
      (gkslFlow H V t X),
      ← nessPotentialReadout_eq_kreinProfile Q entropyPotential X]
    exact InfoGeometry.Modular.NESSCommutantPotentialLeaves.gkslFlow_preserves_potentialReadout
      H X V Q hQH hQV hQstarV
      entropyPotential t
  · rw [← nessPotentialReadout_eq_kreinProfile Q weylPotential
      (gkslFlow H V t X),
      ← nessPotentialReadout_eq_kreinProfile Q weylPotential X]
    exact InfoGeometry.Modular.NESSCommutantPotentialLeaves.gkslFlow_preserves_potentialReadout
      H X V Q hQH hQV hQstarV
      weylPotential t

omit [DecidableEq n] in
theorem adjoint_sheetDiagonalLift (T : OpHilbert →L[ℝ] OpHilbert) :
    ContinuousLinearMap.adjoint (sheetDiagonalLift T) =
      sheetDiagonalLift (ContinuousLinearMap.adjoint T) := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := sheetDiagonalLift (ContinuousLinearMap.adjoint T))
    (B := sheetDiagonalLift T)).2 ?_
  intro u v
  have hu : u = to_doubled (WithLp.fst u) (WithLp.snd u) := by
    apply DoubledSpace.ext <;> rfl
  have hv : v = to_doubled (WithLp.fst v) (WithLp.snd v) := by
    apply DoubledSpace.ext <;> rfl
  rw [hu, hv]
  simp only [sheetDiagonalLift_apply, WithLp.prod_inner_apply]
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]

omit [DecidableEq n] in
theorem sheetDiagonalLift_commutes_fundamentalSymmetry
    (T : OpHilbert →L[ℝ] OpHilbert) :
    (spectral_epsilon (E := OpHilbert)).comp (sheetDiagonalLift T) =
      (sheetDiagonalLift T).comp (spectral_epsilon (E := OpHilbert)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply DoubledSpace.ext <;> simp [sheetDiagonalLift, spectral_epsilon]

omit [DecidableEq n] in
theorem kreinAdjoint_sheetDiagonalLift (T : OpHilbert →L[ℝ] OpHilbert) :
    KreinSpace.kreinAdjoint (H := DOp) (sheetDiagonalLift T) =
      sheetDiagonalLift (ContinuousLinearMap.adjoint T) := by
  rw [KreinSpace.kreinAdjoint, adjoint_sheetDiagonalLift]
  apply ContinuousLinearMap.ext
  intro u
  have hε : KreinSpace.jCLM (H := DOp) = spectral_epsilon (E := OpHilbert) := by
    apply ContinuousLinearMap.ext
    intro z
    apply DoubledSpace.ext <;> rfl
  rw [hε]
  apply DoubledSpace.ext
  · simp [sheetDiagonalLift, spectral_epsilon]
  · simp [sheetDiagonalLift, spectral_epsilon]

/-- The adjoint of the doubled Peirce limit is computed using the actual
fundamental-symmetry Krein adjoint on `DOp`. Since the lift acts identically on
both sheets, this adjoint is the sheet lift of the Hilbert adjoint of the
full-matrix pinching map. -/
theorem kreinAdjoint_doubledProjectionJumpPeircePinchingCLM (P : CMat) :
    KreinSpace.kreinAdjoint (H := DOp)
        (doubledProjectionJumpPeircePinchingCLM P) =
      sheetDiagonalLift
        (ContinuousLinearMap.adjoint (projectionJumpPeircePinchingOperatorCLM P)) := by
  rw [doubledProjectionJumpPeircePinchingCLM,
    kreinAdjoint_sheetDiagonalLift]

/-- On the full matrix-operator carrier, the double-real Krein adjoint of
left multiplication by `A` is left multiplication by `Aᴴ` on each sheet.
The adjoint is taken with respect to the repository's fundamental-symmetry
conjugated product on `DOp`. -/
theorem kreinAdjoint_sheetMatrixLeftAction (A : CMat) :
    KreinSpace.kreinAdjoint (H := DOp)
        (sheetDiagonalLift (matrixLeftActionCLM A)) =
      sheetDiagonalLift (matrixLeftActionCLM (star A)) := by
  rw [kreinAdjoint_sheetDiagonalLift, matrixLeftActionCLM_adjoint]

/-- The double-real Dirac/Krein adjoint of the full Schrödinger GKSL
generator is the sheetwise lift of its matrix Heisenberg dual. -/
theorem kreinAdjoint_sheetSchrodingerGenerator (H : CMat) (V : ι → CMat) :
    KreinSpace.kreinAdjoint (H := DOp)
        (sheetDiagonalLift (schrodingerOperatorCLM H V)) =
      sheetDiagonalLift (heisenbergOperatorCLM H V) := by
  rw [kreinAdjoint_sheetDiagonalLift, schrodingerOperatorCLM_adjoint]

/-- At every real time, the Dirac/Krein adjoint of the lifted Schrödinger
GKSL semigroup is the lifted Heisenberg semigroup. The fundamental symmetry
is retained by `KreinSpace.kreinAdjoint`. -/
theorem kreinAdjoint_sheetSchrodingerOperatorFlow
    (H : CMat) (V : ι → CMat) (t : ℝ) :
    KreinSpace.kreinAdjoint (H := DOp)
        (sheetDiagonalLift (schrodingerOperatorFlow H V t)) =
      sheetDiagonalLift (heisenbergOperatorFlow H V t) := by
  rw [kreinAdjoint_sheetDiagonalLift, schrodingerOperatorFlow_adjoint]

/-- The two-sheet GKSL flows are adjoint under the actual Krein product
induced by the metric/fundamental symmetry. -/
theorem kreinPairing_schrodingerHeisenbergOperatorFlow
    (H : CMat) (V : ι → CMat) (t : ℝ) (z w : DOp) :
    KreinSpace.kreinInner
        (sheetDiagonalLift (schrodingerOperatorFlow H V t) z) w =
      KreinSpace.kreinInner z
        (sheetDiagonalLift (heisenbergOperatorFlow H V t) w) := by
  rw [← kreinAdjoint_sheetSchrodingerOperatorFlow H V t]
  exact KreinSpace.kreinInner_kreinAdjoint
    (sheetDiagonalLift (schrodingerOperatorFlow H V t)) z w

/-- Explicit Krein-pairing duality for the doubled-real GKSL generator.
The pairing is `KreinSpace.kreinInner`, so this identity uses the conjugated
product induced by the fundamental symmetry on the two sheets. -/
theorem kreinPairing_schrodinger_heisenberg (H : CMat) (V : ι → CMat)
    (z w : DOp) :
    KreinSpace.kreinInner
        (sheetDiagonalLift (schrodingerOperatorCLM H V) z) w =
      KreinSpace.kreinInner z
        (sheetDiagonalLift (heisenbergOperatorCLM H V) w) := by
  rw [← kreinAdjoint_sheetSchrodingerGenerator H V]
  exact KreinSpace.kreinInner_kreinAdjoint
    (sheetDiagonalLift (schrodingerOperatorCLM H V)) z w

/-- Explicit matrix-trace form of the two-sheet adjoint law. Each sheet keeps
the full noncommutative Hilbert--Schmidt trace order, while the real doubled
Krein pairing subtracts the second sheet from the first. -/
theorem twoSheetSchrodingerHeisenberg_trace_pairing
    (H X Y U W : CMat) (V : ι → CMat) :
    (Matrix.trace (star
      (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V X) * U)).re -
      (Matrix.trace (star
      (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V Y) * W)).re =
    (Matrix.trace (star X * heisenbergLindbladian H V U)).re -
      (Matrix.trace (star Y * heisenbergLindbladian H V W)).re := by
  rw [← matrixToOperatorHilbert_inner_eq_trace
      (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V X) U,
    ← matrixToOperatorHilbert_inner_eq_trace
      (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V Y) W,
    ← matrixToOperatorHilbert_inner_eq_trace X
      (heisenbergLindbladian H V U),
    ← matrixToOperatorHilbert_inner_eq_trace Y
      (heisenbergLindbladian H V W)]
  rw [schrodinger_heisenberg_pairing H X U V,
    schrodinger_heisenberg_pairing H Y W V]

theorem doubledKreinSchrodingerGenerator_readout
    (H X Y : CMat) (V : ι → CMat) :
    sheetDiagonalLift (schrodingerOperatorCLM H V)
        (to_doubled (matrixToOperatorHilbert X) (matrixToOperatorHilbert Y)) =
      to_doubled
        (matrixToOperatorHilbert
          (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V X))
        (matrixToOperatorHilbert
          (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian H V Y)) ∧
    realify (operatorHilbertToMatrix
        (WithLp.fst (sheetDiagonalLift (schrodingerOperatorCLM H V)
          (to_doubled (matrixToOperatorHilbert X) (matrixToOperatorHilbert Y))))) =
      realifiedSchrodingerLindbladian H V X ∧
    realify (operatorHilbertToMatrix
        (WithLp.snd (sheetDiagonalLift (schrodingerOperatorCLM H V)
          (to_doubled (matrixToOperatorHilbert X) (matrixToOperatorHilbert Y))))) =
      realifiedSchrodingerLindbladian H V Y ∧
    KreinSpace.kreinAdjoint (H := DOp)
        (sheetDiagonalLift (schrodingerOperatorCLM H V)) =
      sheetDiagonalLift (ContinuousLinearMap.adjoint (schrodingerOperatorCLM H V)) := by
  refine ⟨?_, ?_, ?_, kreinAdjoint_sheetDiagonalLift _⟩
  · simp [sheetDiagonalLift_apply, matrixToOperatorHilbert_generator]
  · rw [sheetDiagonalLift_apply]
    change realify (operatorHilbertToMatrix
      (schrodingerOperatorCLM H V (matrixToOperatorHilbert X))) = _
    rw [operatorHilbertToMatrix_generator,
      operatorHilbertToMatrix_matrixToOperatorHilbert]
    exact realify_schrodingerLindbladian H X V
  · rw [sheetDiagonalLift_apply]
    change realify (operatorHilbertToMatrix
      (schrodingerOperatorCLM H V (matrixToOperatorHilbert Y))) = _
    rw [operatorHilbertToMatrix_generator,
      operatorHilbertToMatrix_matrixToOperatorHilbert]
    exact realify_schrodingerLindbladian H Y V

/-- A concrete noncommutative obstruction to Krein-isometric GKSL evolution.
For the spin-`1/2` raising jump on the full complex `2 × 2` matrix algebra,
the off-diagonal Pauli observable is damped. Thus the doubled-real
Schrödinger generator is not skew-adjoint for the Dirac/Krein pairing. -/
theorem raisingJump_generator_not_krein_skew :
    ¬ KreinSpace.IsKreinSkewAdjoint
      (sheetDiagonalLift
        (schrodingerOperatorCLM (0 : Matrix (Fin 2) (Fin 2) ℂ)
          (fun _ : Unit => InfoGeometry.Algebra.FiniteSpin.J_plus))) := by
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let x : EuclideanSpace ℂ (Fin 2 × Fin 2) := matrixToOperatorHilbert X
  let z : DoubledSpace (EuclideanSpace ℂ (Fin 2 × Fin 2)) := to_doubled x 0
  let A := sheetDiagonalLift
    (schrodingerOperatorCLM (0 : Matrix (Fin 2) (Fin 2) ℂ)
      (fun _ : Unit => InfoGeometry.Algebra.FiniteSpin.J_plus))
  have h_damp :
      InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian
        (0 : Matrix (Fin 2) (Fin 2) ℂ)
        (fun _ : Unit => InfoGeometry.Algebra.FiniteSpin.J_plus) X =
        (-1 / 2 : ℂ) • X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [vecHead, vecTail, Matrix.vecMul_apply_eq_sum, X,
      InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian,
      InfoGeometry.Modular.SchrodingerGKSL.hamiltonianTerm,
      InfoGeometry.Modular.SchrodingerGKSL.schrodingerDissipator,
      InfoGeometry.Modular.SchrodingerGKSL.schrodingerDissipatorTerm,
      InfoGeometry.Algebra.FiniteSpin.J_plus, Matrix.mul_apply, Matrix.vecMul_apply,
      Fin.sum_univ_two]
  have hAx : A z = (-1 / 2 : ℝ) • z := by
    have hfirst : schrodingerOperatorCLM (0 : Matrix (Fin 2) (Fin 2) ℂ)
        (fun _ : Unit => InfoGeometry.Algebra.FiniteSpin.J_plus) x =
        (-1 / 2 : ℝ) • x := by
      calc
        _ = matrixToOperatorHilbert
            (InfoGeometry.Modular.SchrodingerGKSL.schrodingerLindbladian
              (0 : Matrix (Fin 2) (Fin 2) ℂ)
              (fun _ : Unit => InfoGeometry.Algebra.FiniteSpin.J_plus) X) :=
              matrixToOperatorHilbert_generator _ _ X
        _ = (-1 / 2 : ℝ) • x := by
          rw [h_damp]
          apply WithLp.ofLp_injective (p := (2 : ENNReal))
          funext ij
          simp [x, matrixToOperatorHilbert, Complex.real_smul]
    apply DoubledSpace.ext <;> simp [A, z, sheetDiagonalLift_apply, hfirst]
  have hx_ne : x ≠ 0 := by
    intro hx
    have hfun := WithLp.toLp_injective (p := (2 : ENNReal)) hx
    have hentry := congrFun hfun (0, 1)
    norm_num [x, matrixToOperatorHilbert, X] at hentry
  have hq_pos : 0 < KreinSpace.kreinInner z z := by
    rw [krein_inner_prod_l2]
    have hpos := real_inner_self_pos.mpr hx_ne
    simpa [z] using hpos
  have hbad :
      KreinSpace.kreinInner (A z) z + KreinSpace.kreinInner z (A z) ≠ 0 := by
    rw [hAx, KreinSpace.kreinInner_smul_left, KreinSpace.kreinInner_smul_right]
    nlinarith
  intro hskew
  have hzero := (KreinSpace.isKreinSkewAdjoint_iff A).mp hskew z z
  exact hbad hzero

end InfoGeometry.Modular.RealifiedGKSLKreinBridge

namespace InfoGeometry.Modular.RealifiedGKSLKreinBridgeWitnesses

theorem mat2_complex_noncomm :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let B : Matrix (Fin 2) (Fin 2) ℂ :=
    Matrix.of fun i j => if i = 1 ∧ j = 0 then 1 else 0
  refine ⟨A, B, ?_⟩
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have hAB : (A * B) 0 0 = 1 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (1 : Fin 2)]
    · simp [A, B]
    · intro k _ hk
      simp [A, hk]
    · intro h1
      exact (h1 (Finset.mem_univ _)).elim
  have hBA : (B * A) 0 0 = 0 := by
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero (fun k _ => by simp [B])
  rw [hAB, hBA] at h00
  exact one_ne_zero h00

end InfoGeometry.Modular.RealifiedGKSLKreinBridgeWitnesses

end noncomputable section
