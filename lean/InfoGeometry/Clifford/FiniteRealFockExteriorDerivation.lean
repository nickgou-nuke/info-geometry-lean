/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ExteriorDerivationLift
import InfoGeometry.Clifford.FiniteRealFockQuadraticAdjoint
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The quadratic real Fock operator is the exterior derivation

The two operators act on the same native exterior algebra: the Fock carrier
is definitionally `CliffordAlgebra 0`. The identification is proved on the
whole algebra by its generator induction, not only on degree one. The
commutator is the lift of the matrix commutator. The existing positive-metric
adjoint theorem therefore belongs to this same exterior derivation.
-/

noncomputable section

namespace InfoGeometry.CliffordExteriorLift

open ExteriorAlgebra

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

@[simp] theorem exteriorLift_algebraMap (T : V →ₗ[R] V) (r : R) :
    exteriorLift T (algebraMap R (ExteriorAlgebra R V) r) = 0 := by
  simp [exteriorLift, exteriorLiftAux, Matrix.algebraMap_matrix_apply]

/-- A linear map obeying the actual generator recurrence is the unique
exterior derivation of its vector-level action. -/
theorem exteriorLift_eq_of_generator_recursion (T : V →ₗ[R] V)
    (D : Module.End R (ExteriorAlgebra R V))
    (hscalar : ∀ r, D (algebraMap R (ExteriorAlgebra R V) r) = 0)
    (hrec : ∀ (v : V) (x : ExteriorAlgebra R V),
      D (ι R v * x) = ι R (T v) * x + ι R v * D x) :
    D = exteriorLift T := by
  apply LinearMap.ext
  intro x
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => rw [hscalar, exteriorLift_algebraMap]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
      rw [hrec, exteriorLift_even_derivation, exteriorLift_ι, hx]

/-- Exterior differentiation preserves the Lie bracket of endomorphisms. -/
theorem exteriorLift_commutator (T S : V →ₗ[R] V) :
    (exteriorLift T).comp (exteriorLift S) -
        (exteriorLift S).comp (exteriorLift T) =
      exteriorLift (T.comp S - S.comp T) := by
  apply exteriorLift_eq_of_generator_recursion
  · intro r
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, exteriorLift_algebraMap, map_zero,
      sub_zero]
  · intro v x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, exteriorLift_even_derivation,
      exteriorLift_ι, map_add, map_sub, sub_mul, mul_sub]
    abel

end InfoGeometry.CliffordExteriorLift

namespace InfoGeometry.Clifford.ClNNNeutralChevalleyBridge

open InfoGeometry.Clifford InfoGeometry.CliffordExteriorLift ExteriorAlgebra
open scoped BigOperators

attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

private theorem fock_mode_generator_recursion (n : ℕ) (i j : Fin n)
    (v : Vector n) (x : SpinorSpace (Vector n)) :
    fockExtActionCLM n i (fockIntActionCLM n j (ι ℝ v * x)) =
      v j • (ι ℝ ((Pi.basisFun ℝ (Fin n)) i) * x) +
        ι ℝ v * fockExtActionCLM n i (fockIntActionCLM n j x) := by
  change ι ℝ ((Pi.basisFun ℝ (Fin n)) i) *
      CliffordAlgebra.contractLeft (LinearMap.proj j) (ι ℝ v * x) = _
  rw [CliffordAlgebra.contractLeft_ι_mul]
  change ι ℝ ((Pi.basisFun ℝ (Fin n)) i) *
      (v j • x - ι ℝ v * intAction (LinearMap.proj j) x) =
    v j • (ι ℝ ((Pi.basisFun ℝ (Fin n)) i) * x) +
      ι ℝ v * (ι ℝ ((Pi.basisFun ℝ (Fin n)) i) * intAction (LinearMap.proj j) x)
  have h := congrArg (fun z : ExteriorAlgebra ℝ (Vector n) =>
      z * intAction (LinearMap.proj j) x)
    (ι_mul_ι_add_swap ((Pi.basisFun ℝ (Fin n)) i) v)
  simp only [add_mul, zero_mul, mul_assoc] at h
  rw [mul_sub, mul_smul_comm, eq_neg_of_add_eq_zero_left h, sub_neg_eq_add]

private theorem matrix_generator_sum (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Vector n) :
    (∑ i : Fin n, ∑ j : Fin n,
      (M i j * v j) • ι ℝ ((Pi.basisFun ℝ (Fin n)) i)) =
      ι ℝ (Matrix.toLin' M v) := by
  have hb : (∑ i : Fin n, (∑ j : Fin n, M i j * v j) •
      (Pi.basisFun ℝ (Fin n)) i) = Matrix.toLin' M v := by
    simpa only [Pi.basisFun_repr, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using
      (Pi.basisFun ℝ (Fin n)).sum_repr (Matrix.toLin' M v)
  have h := congrArg (ι ℝ) hb
  simpa only [map_sum, map_smul, Finset.sum_smul] using h

@[simp] theorem fockQuadraticCLM_algebraMap (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    fockQuadraticCLM n M (algebraMap ℝ (SpinorSpace (Vector n)) r) = 0 := by
  simp only [fockQuadraticCLM_apply, fockIntActionCLM_apply, intAction,
    CliffordAlgebra.contractLeft_algebraMap, map_zero, smul_zero, Finset.sum_const_zero]

/-- Creation after contraction obeys the ordinary exterior-derivation
recurrence, with the complete coefficient matrix as its action on vectors. -/
theorem fockQuadraticCLM_generator_recursion (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (v : Vector n) (x : SpinorSpace (Vector n)) :
    fockQuadraticCLM n M (ι ℝ v * x) =
      ι ℝ (Matrix.toLin' M v) * x + ι ℝ v * fockQuadraticCLM n M x := by
  rw [fockQuadraticCLM_apply, fockQuadraticCLM_apply]
  simp_rw [fock_mode_generator_recursion]
  calc
    _ = (∑ i : Fin n, ∑ j : Fin n,
          (M i j * v j) • ι ℝ ((Pi.basisFun ℝ (Fin n)) i)) * x +
        ι ℝ v * (∑ i : Fin n, ∑ j : Fin n,
          M i j • fockExtActionCLM n i (fockIntActionCLM n j x)) := by
      simp only [smul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
        smul_mul_assoc, mul_smul_comm, mul_smul]
    _ = _ := by rw [matrix_generator_sum]

/-- Equality of the actual endomorphisms on every exterior degree. -/
theorem fockQuadraticCLM_toLinearMap_eq_exteriorLift (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    (fockQuadraticCLM n M).toLinearMap = exteriorLift (Matrix.toLin' M) :=
  exteriorLift_eq_of_generator_recursion (Matrix.toLin' M)
    (fockQuadraticCLM n M).toLinearMap (fockQuadraticCLM_algebraMap n M)
    (fockQuadraticCLM_generator_recursion n M)

@[simp] theorem fockQuadraticCLM_eq_exteriorLift_apply (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (x : SpinorSpace (Vector n)) :
    fockQuadraticCLM n M x = exteriorLift (Matrix.toLin' M) x :=
  LinearMap.congr_fun (fockQuadraticCLM_toLinearMap_eq_exteriorLift n M) x

/-- The Hilbert pairing of the exterior derivation obeys the already
constructed real Fock transpose-adjoint law. -/
theorem exteriorLift_matrix_inner_transpose (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ) (x y : SpinorSpace (Vector n)) :
    inner ℝ (exteriorLift (Matrix.toLin' M) x) y =
      inner ℝ x (exteriorLift (Matrix.toLin' M.transpose) y) := by
  simpa only [fockQuadraticCLM_eq_exteriorLift_apply] using
    fockQuadraticCLM_inner_transpose n M x y

/-- Genuine Lie-representation identity on the full real Fock Hilbert space. -/
theorem fockQuadraticCLM_commutator (n : ℕ)
    (M N : Matrix (Fin n) (Fin n) ℝ) :
    (fockQuadraticCLM n M).comp (fockQuadraticCLM n N) -
        (fockQuadraticCLM n N).comp (fockQuadraticCLM n M) =
      fockQuadraticCLM n (M * N - N * M) := by
  ext x
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    fockQuadraticCLM_eq_exteriorLift_apply, map_sub, Matrix.toLin'_mul]
  exact LinearMap.congr_fun (exteriorLift_commutator (Matrix.toLin' M) (Matrix.toLin' N)) x

@[simp] theorem fockQuadraticCLM_zero (n : ℕ) :
    fockQuadraticCLM n (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  simp [fockQuadraticCLM]

/-- The one-particle sector witnesses faithfulness of the full operator map. -/
theorem fockQuadraticCLM_injective (n : ℕ) : Function.Injective (fockQuadraticCLM n) := by
  intro M N h
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  apply (ExteriorAlgebra.ι_inj ℝ _ _).mp
  have hx := congrArg (fun F : SpinorSpace (Vector n) →L[ℝ] SpinorSpace (Vector n) =>
    F (ι ℝ v)) h
  simpa only [fockQuadraticCLM_eq_exteriorLift_apply, exteriorLift_ι] using hx

/-- Noncommutation is preserved and reflected; no commuting surrogate is introduced. -/
theorem fockQuadraticCLM_comp_commute_iff (n : ℕ)
    (M N : Matrix (Fin n) (Fin n) ℝ) :
    (fockQuadraticCLM n M).comp (fockQuadraticCLM n N) =
        (fockQuadraticCLM n N).comp (fockQuadraticCLM n M) ↔ M * N = N * M := by
  constructor
  · intro h
    have hz := fockQuadraticCLM_commutator n M N
    rw [h, sub_self] at hz
    have heq : fockQuadraticCLM n (M * N - N * M) = fockQuadraticCLM n 0 := by
      rw [← hz, fockQuadraticCLM_zero]
    exact sub_eq_zero.mp (fockQuadraticCLM_injective n heq)
  · intro h
    have hz := fockQuadraticCLM_commutator n M N
    rw [h, sub_self, fockQuadraticCLM_zero] at hz
    exact sub_eq_zero.mp hz

/-- Two explicitly symmetric real coefficient matrices retain nonzero
commutator after lifting to the entire two-mode Fock space. -/
theorem exists_symmetric_noncommuting_fockQuadraticCLM :
    ∃ M N : Matrix (Fin 2) (Fin 2) ℝ, M.IsSymm ∧ N.IsSymm ∧
      M * N ≠ N * M ∧
      (fockQuadraticCLM 2 M).comp (fockQuadraticCLM 2 N) ≠
        (fockQuadraticCLM 2 N).comp (fockQuadraticCLM 2 M) := by
  have hMN : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 1, 0] ≠
      !![0, 1; 1, 0] * !![1, 0; 0, 0] := by
    intro h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h01
  refine ⟨!![1, 0; 0, 0], !![0, 1; 1, 0], ?_, ?_, hMN, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  · apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num
  · intro h
    exact hMN ((fockQuadraticCLM_comp_commute_iff 2 _ _).mp h)

end InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
