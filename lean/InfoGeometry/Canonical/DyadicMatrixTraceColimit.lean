/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Categorical.MatrixAmplificationTower
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Data.Matrix.Composition

/-!
# The normalized trace on the binary matrix-amplification colimit

This module uses the full recursive matrix rings and the actual algebraic
colimit already owned by `MatrixAmplificationTower`. The coefficient ring
is commutative, but the matrix stages and their colimit are not assumed
commutative. Inverting `2` suffices to normalize the trace at every stage.

The compatible traces descend as a linear map, using the native module
direct-limit lift on the same carrier. They are not ring homomorphisms:
opposite off-diagonal matrix units give an explicit counterexample.
No positivity, topology, completion or operator-algebra classification is
part of this algebraic construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.DyadicMatrixTraceColimit

open InfoGeometry.Algebra.DirectLimitSuperClosureLemmas

open InfoGeometry.Categorical

-- Matrix formulas need to see the native successor carrier during rewriting.
attribute [local reducible] MatrixAmplificationTower.stage MatrixAmplificationTower.matrixFunctor

variable (K : Type) [CommRing K]

/-- The existing binary amplification stages, with the coefficient ring at zero. -/
abbrev Stage (n : ℕ) : Type := MatrixAmplificationTower.stage (Fin 2) (RingCat.of K) n

/-- The existing algebraic colimit; no second carrier or quotient is introduced. -/
abbrev Carrier := MatrixAmplificationTower.Limit (Fin 2) (RingCat.of K)

/-- The scalar action is the ordinary entrywise matrix action at each stage. -/
instance stageAlgebra (n : ℕ) : Algebra K (Stage K n) :=
  Nat.rec (motive := fun n => Algebra K (Stage K n))
    (Algebra.id K)
    (fun n ih => by
      letI := ih
      change Algebra K (Matrix (Fin 2) (Fin 2) (Stage K n))
      infer_instance)
    n

/-- Native scalar matrix amplification, retaining its algebra-homomorphism data. -/
def bondAlg (n : ℕ) : Stage K n →ₐ[K] Stage K (n + 1) :=
  Matrix.scalarAlgHom (Fin 2) K

@[simp]
theorem bondAlg_toRingHom (n : ℕ) :
    (bondAlg K n).toRingHom = MatrixAmplificationTower.bond (Fin 2) (RingCat.of K) n := rfl

/-- The already-owned interval transition, with its scalar preservation proved. -/
def transitionAlg (i j : ℕ) (h : i ≤ j) : Stage K i →ₐ[K] Stage K j where
  toRingHom := bondMap (MatrixAmplificationTower.bond (Fin 2) (RingCat.of K)) i j h
  commutes' c := by
    refine Nat.le_induction
      (m := i)
      (P := fun j h =>
        bondMap (MatrixAmplificationTower.bond (Fin 2) (RingCat.of K)) i j h
          (algebraMap K (Stage K i) c) = algebraMap K (Stage K j) c)
      ?_ ?_ j h
    · simp only [bondMap_refl, RingHom.id_apply]
    · intro j hij ih
      rw [bondMap_succ]
      change MatrixAmplificationTower.bond (Fin 2) (RingCat.of K) j
        (bondMap (MatrixAmplificationTower.bond (Fin 2) (RingCat.of K)) i j hij
          (algebraMap K (Stage K i) c)) = _
      rw [ih]
      exact (bondAlg K j).commutes c

instance transitionDirectedSystem :
    DirectedSystem (Stage K) (fun i j h => transitionAlg K i j h) :=
  inferInstanceAs
    (DirectedSystem (Stage K)
      (fun i j h => bondMap (MatrixAmplificationTower.bond (Fin 2) (RingCat.of K)) i j h))

/-- The native direct-limit algebra structure on the existing ring carrier. -/
instance carrierAlgebra : Algebra K (Carrier K) :=
  inferInstanceAs
    (Algebra K
      (DirectLimit (Stage K) (fun i j h => transitionAlg K i j h)))

/-- Canonical inclusion with its scalar-preservation data. -/
def inclusionAlg (n : ℕ) : Stage K n →ₐ[K] Carrier K :=
  DirectLimit.Algebra.of (Stage K) (fun i j h => transitionAlg K i j h) n

@[simp]
theorem inclusionAlg_toRingHom (n : ℕ) :
    (inclusionAlg K n).toRingHom = MatrixAmplificationTower.inclusion (Fin 2) (RingCat.of K) n := rfl

@[simp]
theorem inclusionAlg_bond (n : ℕ) (x : Stage K n) :
    inclusionAlg K (n + 1) (bondAlg K n x) = inclusionAlg K n x :=
  directLimitOf_bond (MatrixAmplificationTower.bond (Fin 2) (RingCat.of K)) n x

theorem inclusionAlg_injective (n : ℕ) : Function.Injective (inclusionAlg K n) :=
  MatrixAmplificationTower.inclusion_injective (Fin 2) (RingCat.of K) n

/-- Three binary amplifications are genuinely full matrices on eight indices. -/
def stageThreeEquiv :
    Stage K 3 ≃ₐ[K]
      Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) K :=
  (Matrix.compAlgEquiv (Fin 2) (Fin 2) K K).mapMatrix.trans
    (Matrix.compAlgEquiv (Fin 2) (Fin 2 × Fin 2) K K)

theorem stageThree_index_card : Fintype.card (Fin 2 × (Fin 2 × Fin 2)) = 8 := by
  decide

variable [Invertible (2 : K)]

/-- The normalized trace, recursively taking the trace of each full matrix shell. -/
def stageTrace (n : ℕ) : Stage K n →ₗ[K] K :=
  Nat.rec (motive := fun n => Stage K n →ₗ[K] K)
    LinearMap.id
    (fun n τ =>
      ⅟(2 : K) • (τ.comp (Matrix.traceLinearMap (Fin 2) K (Stage K n))))
    n

@[simp]
theorem stageTrace_zero_apply (x : K) : stageTrace K 0 x = x := rfl

theorem stageTrace_succ_apply (n : ℕ) (x : Stage K (n + 1)) :
    stageTrace K (n + 1) x = ⅟(2 : K) * stageTrace K n (Matrix.trace x) := rfl

/-- Normalization is preserved by the actual scalar-matrix bond. -/
@[simp]
theorem stageTrace_bond (n : ℕ) (x : Stage K n) :
    stageTrace K (n + 1) (bondAlg K n x) = stageTrace K n x := by
  rw [stageTrace_succ_apply]
  have ht : Matrix.trace (bondAlg K n x) = x + x := by
    change Matrix.trace (Matrix.scalar (Fin 2) x) = x + x
    simp [Matrix.trace, Matrix.diag, Matrix.scalar_apply, Fin.sum_univ_two]
  rw [ht, map_add, ← two_mul, ← mul_assoc, invOf_mul_self, one_mul]

/-- Every normalized finite-stage trace is unital. -/
@[simp]
theorem stageTrace_one (n : ℕ) : stageTrace K n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← map_one (bondAlg K n), stageTrace_bond, ih]

/-- Cyclicity does not require commutative matrix coefficients: the induction
uses cyclicity of the previous stage, preserving the multiplication order. -/
theorem stageTrace_mul_comm (n : ℕ) (x y : Stage K n) :
    stageTrace K n (x * y) = stageTrace K n (y * x) := by
  induction n with
  | zero =>
      change (x : K) * (y : K) = (y : K) * (x : K)
      exact mul_comm (x : K) (y : K)
  | succ n ih =>
      rw [stageTrace_succ_apply, stageTrace_succ_apply]
      congr 1
      simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
        Matrix.mul_apply, map_add]
      rw [ih (x 0 0) (y 0 0), ih (x 0 1) (y 1 0),
        ih (x 1 0) (y 0 1), ih (x 1 1) (y 1 1)]
      ac_rfl

/-- Compatibility along every interval of the existing directed system. -/
theorem stageTrace_transition (i j : ℕ) (h : i ≤ j) (x : Stage K i) :
    stageTrace K j (transitionAlg K i j h x) = stageTrace K i x := by
  refine Nat.le_induction
    (m := i)
    (P := fun j h =>
      stageTrace K j
        (bondMap (MatrixAmplificationTower.bond (Fin 2) (RingCat.of K)) i j h x) = stageTrace K i x)
    ?_ ?_ j h
  · simp only [bondMap_refl, RingHom.id_apply]
  · intro j hij ih
    rw [bondMap_succ]
    change stageTrace K (j + 1)
      (bondAlg K j
        (bondMap (MatrixAmplificationTower.bond (Fin 2) (RingCat.of K)) i j hij x)) = _
    rw [stageTrace_bond, ih]

/-- The compatible linear trace descends to the actual algebraic colimit. -/
def colimitTrace : Carrier K →ₗ[K] K :=
  DirectLimit.Module.lift K ℕ (Stage K)
    (fun i j h => transitionAlg K i j h)
    (stageTrace K) (stageTrace_transition K)

/-- The descended functional agrees with every finite-stage normalized trace. -/
@[simp]
theorem colimitTrace_inclusion (n : ℕ) (x : Stage K n) :
    colimitTrace K (inclusionAlg K n x) = stageTrace K n x := rfl

/-- The descended functional is unital. -/
@[simp]
theorem colimitTrace_one : colimitTrace K 1 = 1 := by
  rw [← map_one (inclusionAlg K 0), colimitTrace_inclusion, stageTrace_one]

/-- Cyclicity is proved for arbitrary colimit elements by a common-stage representative. -/
theorem colimitTrace_mul_comm (x y : Carrier K) :
    colimitTrace K (x * y) = colimitTrace K (y * x) := by
  obtain ⟨n, a, b, hx, hy⟩ :=
    MatrixAmplificationTower.exists_common_stage (Fin 2) (RingCat.of K) x y
  change inclusionAlg K n a = x at hx
  change inclusionAlg K n b = y at hy
  rw [← hx, ← hy, ← map_mul, ← map_mul, colimitTrace_inclusion,
    colimitTrace_inclusion]
  exact stageTrace_mul_comm K n a b

/-- In particular, the colimit trace annihilates every associative commutator. -/
theorem colimitTrace_commutator (x y : Carrier K) :
    colimitTrace K (x * y - y * x) = 0 := by
  rw [map_sub, colimitTrace_mul_comm, sub_self]

/-- Finite-stage values determine the descended linear functional uniquely. -/
theorem colimitTrace_unique (τ : Carrier K →ₗ[K] K)
    (hτ : ∀ n (x : Stage K n), τ (inclusionAlg K n x) = stageTrace K n x) :
    τ = colimitTrace K := by
  ext x
  obtain ⟨n, a, h⟩ := MatrixAmplificationTower.exists_stage (Fin 2) (RingCat.of K) x
  change inclusionAlg K n a = x at h
  rw [← h, hτ, colimitTrace_inclusion]

@[simp]
theorem stageTrace_single_offdiag (n : ℕ) (i j : Fin 2) (hij : i ≠ j)
    (a : Stage K n) :
    stageTrace K (n + 1) (Matrix.single i j a) = 0 := by
  rw [stageTrace_succ_apply, Matrix.trace_single_eq_of_ne i j a hij, map_zero, mul_zero]

@[simp]
theorem stageTrace_single_diag (n : ℕ) (i : Fin 2) (a : Stage K n) :
    stageTrace K (n + 1) (Matrix.single i i a) = ⅟(2 : K) * stageTrace K n a := by
  rw [stageTrace_succ_apply, Matrix.trace_single_eq_same]

/-- Opposite off-diagonal units expose the error in treating trace as a ring homomorphism. -/
theorem stageTrace_not_multiplicative [Nontrivial K] (n : ℕ) :
    ¬ ∀ x y : Stage K (n + 1),
      stageTrace K (n + 1) (x * y) =
        stageTrace K (n + 1) x * stageTrace K (n + 1) y := by
  intro h
  have hw := h (Matrix.single (0 : Fin 2) 1 (1 : Stage K n))
    (Matrix.single (1 : Fin 2) 0 (1 : Stage K n))
  have hz : (⅟(2 : K)) = 0 := by
    simpa [Matrix.single_mul_single_same, stageTrace_single_offdiag,
      stageTrace_single_diag] using hw
  exact Invertible.ne_zero (⅟(2 : K)) hz

/-- The actual colimit functional is likewise not multiplicative. -/
theorem colimitTrace_not_multiplicative [Nontrivial K] :
    ¬ ∀ x y : Carrier K,
      colimitTrace K (x * y) = colimitTrace K x * colimitTrace K y := by
  intro h
  apply stageTrace_not_multiplicative K 0
  intro x y
  simpa only [← map_mul, colimitTrace_inclusion] using
    h (inclusionAlg K 1 x) (inclusionAlg K 1 y)

end InfoGeometry.Canonical.DyadicMatrixTraceColimit
