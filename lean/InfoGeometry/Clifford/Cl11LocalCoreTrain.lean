/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Clifford.Cl11HomogeneousChains
import InfoGeometry.Clifford.Cl11TensorTrainSynthesis
import Mathlib.Algebra.Module.BigOperators

/-!
# Actual local Clifford cores of a scalar tensor train

Each real four-letter core is converted entrywise into a genuine Clifford
atom in the basis `(1, η, K, Ω)`. The native contraction then sums over the
actual internal bonds and prepends each local atom through `consNative`.
It is defined without calling the global word-coordinate reconstruction.

The comparison with `wordReconstruct` is proved by induction on the supplied
train. Its bond dimensions may vary, including zero, and its terminal vector
is retained. Absorbing that vector into the last core is not claimed here.
The optional coefficient version retains exactly one terminal B factor.
-/

noncomputable section

open scoped Matrix Matrix.Module TensorProduct BigOperators

namespace InfoGeometry.Clifford.Cl11LocalCoreTrain

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11RecursiveUnrolling
open InfoGeometry.Clifford.Cl11HomogeneousChains
open InfoGeometry.Clifford.Cl11TensorTrainSynthesis
open InfoGeometry.Tensor.RankMinimalTensorTrain

/-- The actual native Clifford atoms, in the intake's coefficient order. -/
def basisAtom : Fin 4 → CliffordAlgebra q11 :=
  ![1, CliffordAlgebra.ι q11 (1, 0), J1_cl, CliffordAlgebra.ι q11 (0, 1)]

/-- A local core entry is a sum of four native Clifford atoms. -/
def localAtom (v : Fin 4 → ℝ) : CliffordAlgebra q11 :=
  ∑ α, v α • basisAtom α

theorem localAtom_eq_coordinateInverse (v : Fin 4 → ℝ) :
    localAtom v = atomCoordinates.symm v := by
  simpa [localAtom, Fin.sum_univ_four, basisAtom] using
    (atom_expansion (atomCoordinates.symm v)).symm

@[simp] theorem atomCoordinates_localAtom (v : Fin 4 → ℝ) :
    atomCoordinates (localAtom v) = v := by
  rw [localAtom_eq_coordinateInverse, LinearEquiv.apply_symm_apply]

/-- The rectangular matrix W of native Clifford atoms at one train site. -/
def localCore {r s : ℕ} (core : Fin 4 → Matrix (Fin r) (Fin s) ℝ) :
    Matrix (Fin r) (Fin s) (CliffordAlgebra q11) :=
  fun i j => localAtom (fun α => core α i j)

@[simp] theorem localCore_apply {r s : ℕ}
    (core : Fin 4 → Matrix (Fin r) (Fin s) ℝ) (i : Fin r) (j : Fin s) :
    localCore core i j = ∑ α, core α i j • basisAtom α := rfl

/-- Contract the local W matrices using actual native graded head insertion.
The base case is the supplied scalar terminal vector, not a unit boundary. -/
def nativeCoreContraction :
    {n r : ℕ} → Train ℝ 4 n r → Fin r → Clsplit n
  | _, _, .nil boundary, i => boundary i • (1 : Clsplit 0)
  | n + 1, _, .cons core tail, i =>
      ∑ j, consNative n (localCore core i j) (nativeCoreContraction tail j)

section Coefficients

universe u
variable (B : Type u) [Ring B] [Algebra ℝ B]

theorem consTensor_add_head (n : ℕ) (a a' : CliffordAlgebra q11)
    (z : Clsplit n ⊗[ℝ] B) :
    consTensor B n (a + a') z = consTensor B n a z + consTensor B n a' z := by
  induction z using TensorProduct.inductionOn with
  | tmul x b =>
      simp only [consTensor_tmul, consNative_add_head, TensorProduct.add_tmul]
  | add x y hx hy =>
      simp only [map_add, hx, hy]
      abel

theorem consTensor_smul_head (n : ℕ) (r : ℝ) (a : CliffordAlgebra q11)
    (z : Clsplit n ⊗[ℝ] B) :
    consTensor B n (r • a) z = r • consTensor B n a z := by
  induction z using TensorProduct.inductionOn with
  | tmul x b =>
      simp only [consTensor_tmul, consNative_smul_head, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem consTensor_localAtom (n : ℕ) (v : Fin 4 → ℝ) (z : Clsplit n ⊗[ℝ] B) :
    consTensor B n (localAtom v) z =
      ∑ α, v α • consTensor B n (basisAtom α) z := by
  simp only [localAtom, Fin.sum_univ_four, consTensor_add_head, consTensor_smul_head]

/-- A local atom acts on an arbitrary tail coefficient tensor through the
already established native four-word synthesis; the tail need not be pure. -/
theorem wordReconstruct_localAtom (n : ℕ) (v : Fin 4 → ℝ) (c : Words n → B) :
    wordReconstruct B (n + 1) (fun w => v (w 0) • c (Fin.tail w)) =
      consTensor B n (localAtom v) (wordReconstruct B n c) := by
  rw [wordReconstruct_succ, consTensor_localAtom, Fin.sum_univ_four]
  simp [basisAtom, map_smul]

/-- The same actual local contraction with a single terminal B coefficient.
Every local W atom still belongs to the real Clifford quotient. -/
def localCoreContraction (b : B) :
    {n r : ℕ} → Train ℝ 4 n r → Fin r → (Clsplit n ⊗[ℝ] B)
  | _, _, .nil boundary, i => (1 : Clsplit 0) ⊗ₜ[ℝ] (boundary i • b)
  | n + 1, _, .cons core tail, i =>
      ∑ j, consTensor B n (localCore core i j) (localCoreContraction B b tail j)

private theorem coeff_cons_smul {n r s : ℕ}
    (core : Fin 4 → Matrix (Fin r) (Fin s) ℝ) (tail : Train ℝ 4 n s)
    (i : Fin r) (b : B) :
    (fun w => (Train.cons core tail).coeff i w • b) =
      ∑ j : Fin s, (fun w => core (w 0) i j • (tail.coeff j (Fin.tail w) • b)) := by
  funext w
  simp only [Train.coeff, Matrix.of_apply, Finset.sum_apply, Finset.sum_smul,
    mul_smul, Fin.tail]

/-- Equality with global word synthesis is a theorem about the independently
defined local-W contraction, including its full terminal boundary vector. -/
theorem wordReconstruct_trainCoeff (b : B) :
    ∀ {n r : ℕ} (T : Train ℝ 4 n r) (i : Fin r),
      wordReconstruct B n (fun w => T.coeff i w • b) = localCoreContraction B b T i
  | _, _, .nil boundary, i => by
      rw [wordReconstruct_zero]
      rfl
  | n + 1, _, .cons core tail, i => by
      rw [coeff_cons_smul B core tail i b, map_sum]
      simp_rw [wordReconstruct_localAtom]
      change (∑ j, consTensor B n (localCore core i j)
        (wordReconstruct B n (fun w => tail.coeff j w • b))) =
          ∑ j, consTensor B n (localCore core i j) (localCoreContraction B b tail j)
      apply Finset.sum_congr rfl
      intro j _
      rw [wordReconstruct_trainCoeff B b tail j]

/-- The coefficient contraction is the ordinary extension of the actual
native scalar contraction by one terminal coefficient. -/
theorem localCoreContraction_eq_native (b : B) :
    ∀ {n r : ℕ} (T : Train ℝ 4 n r) (i : Fin r),
      localCoreContraction B b T i = nativeCoreContraction T i ⊗ₜ[ℝ] b
  | _, _, .nil boundary, i => by
      simp only [localCoreContraction, nativeCoreContraction,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  | n + 1, _, .cons core tail, i => by
      change (∑ j, consTensor B n (localCore core i j) (localCoreContraction B b tail j)) =
        (∑ j, consNative n (localCore core i j) (nativeCoreContraction tail j)) ⊗ₜ[ℝ] b
      rw [TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl
      intro j _
      rw [localCoreContraction_eq_native B b tail j, consTensor_tmul]

end Coefficients

/-- Scalar train coefficients reconstruct the native local-W chain, with the
one-dimensional real coefficient leg made explicit. -/
theorem wordReconstruct_trainCoeff_native {n r : ℕ} (T : Train ℝ 4 n r) (i : Fin r) :
    wordReconstruct ℝ n (fun w => T.coeff i w) =
      nativeCoreContraction T i ⊗ₜ[ℝ] (1 : ℝ) := by
  simpa only [smul_eq_mul, mul_one] using
    (wordReconstruct_trainCoeff ℝ 1 T i).trans (localCoreContraction_eq_native ℝ 1 T i)

/-- The previously defined train synthesis is the actual native local-core
contraction, rather than merely a new name for global word synthesis. -/
theorem trainSynthesis_eq_nativeCoreContraction {n : ℕ} (T : Train ℝ 4 n 1) :
    trainSynthesis ℝ T = nativeCoreContraction T 0 ⊗ₜ[ℝ] (1 : ℝ) :=
  wordReconstruct_trainCoeff_native T 0

/-- The train's matrix is read directly from the native local-W contraction. -/
theorem trainMatrix_eq_nativeCoreReadback {n : ℕ} (T : Train ℝ 4 n 1) :
    trainMatrix ℝ T = leftMatrixEquiv n (nativeCoreContraction T 0) := by
  rw [trainMatrix, trainSynthesis_eq_nativeCoreContraction, leftCoefficientEquiv_tmul]
  ext i j
  simp [coefficientReadback_apply]

end InfoGeometry.Clifford.Cl11LocalCoreTrain
