import Mathlib
import InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

noncomputable section

namespace SouriauOnsagerBKM

open Matrix
open scoped Interval
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix
open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.CblinfunMatrix

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 100000

/-!
This owner defines the genuine finite-dimensional Kubo--Mori pairing on the
noncommutative C*-algebra of bounded operators on a complex Hilbert space.

Unlike the separate Hilbert--Schmidt owner, the construction here contains:

* a faithful density operator represented by `IsStrictlyPositive`;
* native continuous-functional-calculus real powers `CFC.rpow ρ s`;
* the modular interpolation `ρ^s A ρ^(1-s)`;
* the interval integral over `s ∈ [0,1]`.

No diagonalization or commutativity hypothesis is imposed on observables.
-/

/-- Finite complex Hilbert space carrying the operator algebra. -/
abbrev FiniteHilbertSpace (n : ℕ) : Type :=
  FinKetSpace (Fin n)

/-- Full noncommutative C*-algebra of bounded operators on the finite Hilbert
space. -/
abbrev FiniteOperatorAlgebra (n : ℕ) : Type :=
  FiniteHilbertSpace n →L[ℂ] FiniteHilbertSpace n

/-- The ordinary finite trace transported from the canonical coordinate
matrix of an operator. -/
def finiteOperatorTrace (T : FiniteOperatorAlgebra n) : ℂ :=
  Matrix.trace (matrixOfOp T)

/-- Coordinate matrices preserve complex scalar multiplication. -/
theorem matrixOfOp_complex_smul
    (c : ℂ) (T : FiniteOperatorAlgebra n) :
    matrixOfOp (c • T) = c • matrixOfOp T := by
  unfold matrixOfOp
  exact
    (LinearMap.toMatrix
      (ketBasis (Fin n)) (ketBasis (Fin n))).map_smul
        c T.toLinearMap

/-- The finite operator trace as a complex-linear functional on the full
noncommutative operator algebra. -/
def finiteOperatorTraceLinear (n : ℕ) :
    FiniteOperatorAlgebra n →ₗ[ℂ] ℂ where
  toFun := finiteOperatorTrace
  map_add' A B := by
    unfold finiteOperatorTrace
    rw [matrixOfOp_add, Matrix.trace_add]
  map_smul' c A := by
    unfold finiteOperatorTrace
    rw [matrixOfOp_complex_smul, Matrix.trace_smul]
    rfl

@[simp] theorem finiteOperatorTraceLinear_apply
    (T : FiniteOperatorAlgebra n) :
    finiteOperatorTraceLinear n T = finiteOperatorTrace T :=
  rfl

/-- The finite operator trace intertwines the operator adjoint and complex
conjugation. -/
theorem finiteOperatorTrace_star
    (T : FiniteOperatorAlgebra n) :
    finiteOperatorTrace (star T) = star (finiteOperatorTrace T) := by
  unfold finiteOperatorTrace
  change
    Matrix.trace
        (matrixOfOp (ContinuousLinearMap.adjoint T)) =
      _
  rw [matrixOfOp_adjoint]
  exact Matrix.trace_conjTranspose _

/-- Cyclicity of the finite operator trace for two arbitrary operators.  No
commutativity hypothesis is imposed on the operator algebra. -/
theorem finiteOperatorTrace_mul_comm
    (A B : FiniteOperatorAlgebra n) :
    finiteOperatorTrace (A * B) =
      finiteOperatorTrace (B * A) := by
  unfold finiteOperatorTrace
  change
    Matrix.trace (matrixOfOp (A.comp B)) =
      Matrix.trace (matrixOfOp (B.comp A))
  rw [matrixOfOp_comp, matrixOfOp_comp]
  exact Matrix.trace_mul_comm _ _

theorem matrixOfOp_real_smul
    (r : ℝ) (T : FiniteOperatorAlgebra n) :
    matrixOfOp (r • T) = (r : ℂ) • matrixOfOp T := by
  change
    matrixOfOp ((r : ℂ) • T) =
      (r : ℂ) • matrixOfOp T
  unfold matrixOfOp
  exact
    (LinearMap.toMatrix
      (ketBasis (Fin n)) (ketBasis (Fin n))).map_smul
        (r : ℂ) T.toLinearMap

/-- A faithful finite density operator: strictly positive with trace one. -/
structure FaithfulDensityOperator (n : ℕ) where
  rho : FiniteOperatorAlgebra n
  strictlyPositive : IsStrictlyPositive rho
  trace_one : finiteOperatorTrace rho = 1

namespace FaithfulDensityOperator

/-- Real powers of a faithful density operator through Mathlib's native
continuous functional calculus. -/
def rpow (D : FaithfulDensityOperator n) (s : ℝ) :
    FiniteOperatorAlgebra n :=
  CFC.rpow D.rho s

@[simp] theorem rpow_zero (D : FaithfulDensityOperator n) :
    D.rpow 0 = 1 := by
  exact CFC.rpow_zero D.rho D.strictlyPositive.nonneg

@[simp] theorem rpow_one (D : FaithfulDensityOperator n) :
    D.rpow 1 = D.rho := by
  exact CFC.rpow_one D.rho D.strictlyPositive.nonneg

theorem rpow_add (D : FaithfulDensityOperator n) (s t : ℝ) :
    D.rpow (s + t) = D.rpow s * D.rpow t := by
  exact CFC.rpow_add D.strictlyPositive.isUnit

/-- Every real continuous-functional-calculus power of a faithful density
operator is self-adjoint. -/
@[simp] theorem star_rpow
    (D : FaithfulDensityOperator n) (s : ℝ) :
    star (D.rpow s) = D.rpow s := by
  have h : 0 ≤ D.rpow s := CFC.rpow_nonneg
  exact h.isSelfAdjoint.star_eq

/-- Kubo--Mori modular interpolation `ρ^s A ρ^(1-s)`. -/
def modularInterpolation
    (D : FaithfulDensityOperator n)
    (s : ℝ) (A : FiniteOperatorAlgebra n) :
    FiniteOperatorAlgebra n :=
  D.rpow s * A * D.rpow (1 - s)

@[simp] theorem modularInterpolation_zero
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) :
    D.modularInterpolation 0 A = A * D.rho := by
  simp [modularInterpolation]

@[simp] theorem modularInterpolation_one
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) :
    D.modularInterpolation 1 A = D.rho * A := by
  simp [modularInterpolation]

/-- Sesquilinear Kubo--Mori integrand
`Tr(ρ^s A* ρ^(1-s) B)`. -/
def kuboMoriIntegrand
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n)
    (s : ℝ) : ℂ :=
  finiteOperatorTrace
    (D.rpow s * star A * D.rpow (1 - s) * B)

/-- At a fixed Cartan/modular-flow parameter `s`, the Kubo--Mori kernel is a
complex-linear functional of the transported observable `B`.

This is the object transported contravariantly by the filtered dual inverse
system.  It is operatorial: `A` and `B` range over the full noncommutative
bounded-operator algebra. -/
def kuboMoriKernelFunctional
    (D : FaithfulDensityOperator n)
    (A : FiniteOperatorAlgebra n) (s : ℝ) :
    FiniteOperatorAlgebra n →ₗ[ℂ] ℂ where
  toFun := fun B => D.kuboMoriIntegrand A B s
  map_add' B C := by
    unfold kuboMoriIntegrand
    simp only [mul_add]
    exact map_add (finiteOperatorTraceLinear n) _ _
  map_smul' c B := by
    unfold kuboMoriIntegrand
    rw [mul_smul_comm]
    exact map_smul (finiteOperatorTraceLinear n) c _

@[simp] theorem kuboMoriKernelFunctional_apply
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n) (s : ℝ) :
    D.kuboMoriKernelFunctional A s B =
      D.kuboMoriIntegrand A B s :=
  rfl

/-- Genuine finite-dimensional Kubo--Mori pairing, defined by its native
Bochner interval integral.  This is a finite-stage scalar readout, not the
repository's filtered-colimit continuum owner.  The colimit owner transports
`kuboMoriKernelFunctional` through the dual inverse system. -/
def kuboMoriPairing
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n) : ℂ :=
  ∫ s in (0 : ℝ)..1, D.kuboMoriIntegrand A B s

theorem kuboMoriPairing_eq_integral
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n) :
    D.kuboMoriPairing A B =
      ∫ s in (0 : ℝ)..1,
        finiteOperatorTrace
          (D.rpow s * star A * D.rpow (1 - s) * B) := by
  rfl

/-- Pointwise Hermitian symmetry of the genuine Kubo--Mori integrand on the
full noncommutative operator algebra. -/
theorem kuboMoriIntegrand_conj_symm
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n) (s : ℝ) :
    star (D.kuboMoriIntegrand A B s) =
      D.kuboMoriIntegrand B A s := by
  unfold kuboMoriIntegrand
  rw [← finiteOperatorTrace_star]
  simp only [StarMul.star_mul, star_star, star_rpow]
  calc
    finiteOperatorTrace
        (star B * (D.rpow (1 - s) * (A * D.rpow s))) =
      finiteOperatorTrace
        ((star B * D.rpow (1 - s) * A) * D.rpow s) := by
          simp only [mul_assoc]
    _ =
      finiteOperatorTrace
        (D.rpow s * (star B * D.rpow (1 - s) * A)) :=
          finiteOperatorTrace_mul_comm _ _
    _ =
      finiteOperatorTrace
        (D.rpow s * star B * D.rpow (1 - s) * A) := by
          simp only [mul_assoc]

/-- Hermitian symmetry of the integrated Kubo--Mori pairing.  The analytic
obligation is stated explicitly: the relevant operator-valued trace
integrand must be interval-integrable. -/
theorem kuboMoriPairing_conj_symm
    (D : FaithfulDensityOperator n)
    (A B : FiniteOperatorAlgebra n)
    (h_integrable :
      IntervalIntegrable
        (D.kuboMoriIntegrand A B) MeasureTheory.volume 0 1) :
    star (D.kuboMoriPairing A B) =
      D.kuboMoriPairing B A := by
  unfold kuboMoriPairing
  calc
    star
        (∫ s in (0 : ℝ)..1,
          D.kuboMoriIntegrand A B s) =
      ∫ s in (0 : ℝ)..1,
        star (D.kuboMoriIntegrand A B s) := by
          symm
          exact
            ContinuousLinearMap.intervalIntegral_comp_comm
              Complex.conjCLE.toContinuousLinearMap h_integrable
    _ =
      ∫ s in (0 : ℝ)..1,
        D.kuboMoriIntegrand B A s := by
          apply intervalIntegral.integral_congr
          intro s hs
          exact D.kuboMoriIntegrand_conj_symm A B s

end FaithfulDensityOperator

/-- The normalized identity is an explicit faithful qubit density operator. -/
def maximallyMixedFaithfulDensityTwo :
    FaithfulDensityOperator 2 where
  rho :=
    (1 / 2 : ℝ) •
      (1 : FiniteOperatorAlgebra 2)
  strictlyPositive := by
    exact IsStrictlyPositive.smul
      (by norm_num : (0 : ℝ) < 1 / 2)
      isStrictlyPositive_one
  trace_one := by
    unfold finiteOperatorTrace
    rw [matrixOfOp_real_smul]
    rw [show
      matrixOfOp (1 : FiniteOperatorAlgebra 2) =
          (1 : Matrix (Fin 2) (Fin 2) ℂ) by
        change
          matrixOfOp
              (ContinuousLinearMap.id ℂ
                (FiniteHilbertSpace 2)) =
            1
        exact matrixOfOp_id]
    simp [Matrix.trace]

/-- The same canonical faithful density is available at every dyadic dimension `2 ^ n`. -/
def maximallyMixedFaithfulDensityPowTwo (n : ℕ) :
    FaithfulDensityOperator (2 ^ n) where
  rho :=
    (1 / (2 ^ n : ℝ)) •
      (1 : FiniteOperatorAlgebra (2 ^ n))
  strictlyPositive := by
    exact IsStrictlyPositive.smul
      (by positivity : (0 : ℝ) < 1 / (2 ^ n : ℝ))
      isStrictlyPositive_one
  trace_one := by
    unfold finiteOperatorTrace
    rw [matrixOfOp_real_smul]
    rw [show
      matrixOfOp (1 : FiniteOperatorAlgebra (2 ^ n)) =
          (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) by
        change
          matrixOfOp
              (ContinuousLinearMap.id ℂ
                (FiniteHilbertSpace (2 ^ n))) =
            1
        exact matrixOfOp_id]
    simp [Matrix.trace]

theorem maximallyMixed_bkm_kernel_eq_normalized_trace
    (n : ℕ) (s : ℝ) (B : FiniteOperatorAlgebra (2 ^ n)) :
    (maximallyMixedFaithfulDensityPowTwo n).kuboMoriKernelFunctional
        (1 : FiniteOperatorAlgebra (2 ^ n)) s B =
      (1 / (2 ^ n : ℂ)) * finiteOperatorTrace B := by
  rw [FaithfulDensityOperator.kuboMoriKernelFunctional_apply]
  unfold FaithfulDensityOperator.kuboMoriIntegrand
  simp only [star_one, mul_one]
  rw [← (maximallyMixedFaithfulDensityPowTwo n).rpow_add]
  have hs : s + (1 - s) = 1 := by ring
  rw [hs, (maximallyMixedFaithfulDensityPowTwo n).rpow_one]
  change finiteOperatorTrace
    (((1 / (2 ^ n : ℝ)) • (1 : FiniteOperatorAlgebra (2 ^ n))) * B) = _
  unfold finiteOperatorTrace
  change Matrix.trace (matrixOfOp
    (((1 / (2 ^ n : ℝ)) • (1 : FiniteOperatorAlgebra (2 ^ n))).comp B)) = _
  rw [matrixOfOp_comp, matrixOfOp_real_smul]
  have h_one : matrixOfOp (1 : FiniteOperatorAlgebra (2 ^ n)) =
      (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
    change matrixOfOp
        (ContinuousLinearMap.id ℂ (FiniteHilbertSpace (2 ^ n))) = 1
    exact matrixOfOp_id
  rw [h_one, Matrix.smul_mul, one_mul, Matrix.trace_smul]
  simp [smul_eq_mul]

/-- Concrete noncommutativity witness in the operator carrier used by the BKM
construction. -/
theorem exists_noncommuting_finiteOperators :
    ∃ A B : FiniteOperatorAlgebra 2, A * B ≠ B * A := by
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  refine
    ⟨CblinfunMatrix.matrixOp X,
      CblinfunMatrix.matrixOp Z, ?_⟩
  intro h
  have hm := congrArg
    (matrixOfOp :
      FiniteOperatorAlgebra 2 → Matrix (Fin 2) (Fin 2) ℂ) h
  change
    matrixOfOp
        ((CblinfunMatrix.matrixOp X).comp
          (CblinfunMatrix.matrixOp Z)) =
      matrixOfOp
        ((CblinfunMatrix.matrixOp Z).comp
          (CblinfunMatrix.matrixOp X)) at hm
  simp only [matrixOfOp_comp, matrixOfOp_matrixOp] at hm
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hm
  norm_num [X, Z, Matrix.mul_apply, Fin.sum_univ_two] at hentry

end SouriauOnsagerBKM
