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
train. Its bond dimensions may vary, including zero. At positive length,
terminal-vector absorption gives a unit right boundary while preserving
every interior bond and the same native matrix readback.
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
noncomputable def nativeCoreContraction :
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
      change consNative n (a + a') x ⊗ₜ[ℝ] b =
        consNative n a x ⊗ₜ[ℝ] b + consNative n a' x ⊗ₜ[ℝ] b
      rw [consNative_add_head n a a' x, TensorProduct.add_tmul]
  | add x y hx hy =>
      rw [(consTensor B n (a + a')).map_add x y,
        (consTensor B n a).map_add x y, (consTensor B n a').map_add x y, hx, hy]
      abel

theorem consTensor_smul_head (n : ℕ) (r : ℝ) (a : CliffordAlgebra q11)
    (z : Clsplit n ⊗[ℝ] B) :
    consTensor B n (r • a) z = r • consTensor B n a z := by
  induction z using TensorProduct.inductionOn with
  | tmul x b =>
      change consNative n (r • a) x ⊗ₜ[ℝ] b = r • (consNative n a x ⊗ₜ[ℝ] b)
      rw [consNative_smul_head n r a x]
      exact ((TensorProduct.mk ℝ (Clsplit (n + 1)) B).flip b).map_smul r
        (consNative n a x)
  | add x y hx hy =>
      rw [(consTensor B n (r • a)).map_add x y,
        (consTensor B n a).map_add x y, hx, hy, smul_add]

theorem consTensor_localAtom (n : ℕ) (v : Fin 4 → ℝ) (z : Clsplit n ⊗[ℝ] B) :
    consTensor B n (localAtom v) z =
      ∑ α, v α • consTensor B n (basisAtom α) z := by
  simp only [localAtom, Fin.sum_univ_four]
  rw [consTensor_add_head B n
      (v 0 • basisAtom 0 + v 1 • basisAtom 1 + v 2 • basisAtom 2)
      (v 3 • basisAtom 3) z,
    consTensor_add_head B n (v 0 • basisAtom 0 + v 1 • basisAtom 1)
      (v 2 • basisAtom 2) z,
    consTensor_add_head B n (v 0 • basisAtom 0) (v 1 • basisAtom 1) z,
    consTensor_smul_head B n (v 0) (basisAtom 0) z,
    consTensor_smul_head B n (v 1) (basisAtom 1) z,
    consTensor_smul_head B n (v 2) (basisAtom 2) z,
    consTensor_smul_head B n (v 3) (basisAtom 3) z]

/-- A local atom acts on an arbitrary tail coefficient tensor through the
already established native four-word synthesis; the tail need not be pure. -/
theorem wordReconstruct_localAtom (n : ℕ) (v : Fin 4 → ℝ) (c : Words n → B) :
    wordReconstruct B (n + 1) (fun w => v (w 0) • c (Fin.tail w)) =
      consTensor B n (localAtom v) (wordReconstruct B n c) := by
  have hsmul (a : CliffordAlgebra q11) (r : ℝ) :
      consTensor B n a (wordReconstruct B n (fun w => r • c w)) =
        r • consTensor B n a (wordReconstruct B n c) :=
    ((consTensor B n a).comp (wordReconstruct B n).toLinearMap).map_smul r c
  rw [wordReconstruct_succ, consTensor_localAtom, Fin.sum_univ_four]
  change
    consTensor B n (basisAtom 0) (wordReconstruct B n (fun w => v 0 • c w)) +
        consTensor B n (basisAtom 1) (wordReconstruct B n (fun w => v 1 • c w)) +
      consTensor B n (basisAtom 2) (wordReconstruct B n (fun w => v 2 • c w)) +
      consTensor B n (basisAtom 3) (wordReconstruct B n (fun w => v 3 • c w)) =
    v 0 • consTensor B n (basisAtom 0) (wordReconstruct B n c) +
        v 1 • consTensor B n (basisAtom 1) (wordReconstruct B n c) +
      v 2 • consTensor B n (basisAtom 2) (wordReconstruct B n c) +
      v 3 • consTensor B n (basisAtom 3) (wordReconstruct B n c)
  rw [hsmul (basisAtom 0) (v 0), hsmul (basisAtom 1) (v 1),
    hsmul (basisAtom 2) (v 2), hsmul (basisAtom 3) (v 3)]

/-- The same actual local contraction with a single terminal B coefficient.
Every local W atom still belongs to the real Clifford quotient. -/
noncomputable def localCoreContraction (b : B) :
    {n r : ℕ} → Train ℝ 4 n r → Fin r → (Clsplit n ⊗[ℝ] B)
  | _, _, .nil boundary, i => (1 : Clsplit 0) ⊗ₜ[ℝ] (boundary i • b)
  | n + 1, _, .cons core tail, i =>
      ∑ j, consTensor B n (localCore core i j) (localCoreContraction b tail j)

private theorem coeff_cons_smul {n r s : ℕ}
    (core : Fin 4 → Matrix (Fin r) (Fin s) ℝ) (tail : Train ℝ 4 n s)
    (i : Fin r) (b : B) :
    (fun w => (Train.cons core tail).coeff i w • b) =
      ∑ j : Fin s, (fun w => core (w 0) i j • (tail.coeff j (Fin.tail w) • b)) := by
  funext w
  rw [Finset.sum_apply]
  change (∑ j : Fin s, core (w 0) i j * tail.coeff j (Fin.tail w)) • b =
    ∑ j : Fin s, core (w 0) i j • (tail.coeff j (Fin.tail w) • b)
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_smul (core (w 0) i j) (tail.coeff j (Fin.tail w)) b

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
      change (∑ j, wordReconstruct B (n + 1)
        (fun w => core (w 0) i j • (tail.coeff j (Fin.tail w) • b))) =
          ∑ j, consTensor B n (localCore core i j) (localCoreContraction B b tail j)
      apply Finset.sum_congr rfl
      intro j _
      exact (wordReconstruct_localAtom B n (fun α => core α i j)
        (fun w => tail.coeff j w • b)).trans
          (congrArg (consTensor B n (localCore core i j))
            (wordReconstruct_trainCoeff b tail j))

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
      rw [localCoreContraction_eq_native b tail j, consTensor_tmul]

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

/-- Absorbing the terminal vector preserves the matrix reconstructed from
the actual, ordered train coefficients. -/
@[simp] theorem trainMatrix_absorbTerminalBoundary {n : ℕ} (T : Train ℝ 4 n 1) :
    trainMatrix ℝ T.absorbTerminalBoundary = trainMatrix ℝ T := by
  apply (wordCoefficientEquiv ℝ n).injective
  simp only [wordCoefficient_trainMatrix, Train.absorbTerminalBoundary_coeff]

/-- Terminal normalization also preserves the independently defined native
local Clifford-core contraction after its faithful matrix readback. -/
theorem nativeCoreReadback_absorbTerminalBoundary {n : ℕ} (T : Train ℝ 4 n 1) :
    leftMatrixEquiv n (nativeCoreContraction T.absorbTerminalBoundary 0) =
      leftMatrixEquiv n (nativeCoreContraction T 0) := by
  rw [← trainMatrix_eq_nativeCoreReadback, trainMatrix_absorbTerminalBoundary,
    trainMatrix_eq_nativeCoreReadback]

/-- Every positive-length matrix has a native local-core train with both
outer bond dimensions one and a unit terminal vector. All interior bonds
attain the corrected unfolding ranks and are minimal among exact trains.
The terminal bond is a boundary convention, not an interior rank claim. -/
theorem exists_unitBoundary_minimal_native_core_train (n : ℕ)
    (M : CoefficientMatrix ℝ (n + 1)) :
    ∃ T : Train ℝ 4 (n + 1) 1,
      T.bond (Fin.last (n + 1)) = 1 ∧
      T.terminalBoundary = 1 ∧
      leftMatrixEquiv (n + 1) (nativeCoreContraction T 0) = M ∧
      (∀ k : Fin n, T.bond k.succ.castSucc =
        cutRank 4 (n + 1) (Fin 1)
          (Matrix.of fun _ word => wordCoefficientEquiv ℝ (n + 1) M word)
          k.succ.castSucc) ∧
      (∀ S : Train ℝ 4 (n + 1) 1,
        leftMatrixEquiv (n + 1) (nativeCoreContraction S 0) = M →
        ∀ k : Fin n, T.bond k.succ.castSucc ≤ S.bond k.succ.castSucc) := by
  obtain ⟨T, hT, hminimal, hlower⟩ := exists_minimal_clifford_train (n + 1) M
  refine ⟨T.absorbTerminalBoundary, Train.absorbTerminalBoundary_bond_last T,
    Train.absorbTerminalBoundary_terminalBoundary T, ?_, ?_, ?_⟩
  · rw [← trainMatrix_eq_nativeCoreReadback, trainMatrix_absorbTerminalBoundary]
    exact hT
  · intro k
    rw [Train.absorbTerminalBoundary_bond_castSucc]
    exact hminimal k.castSucc
  · intro S hS k
    rw [Train.absorbTerminalBoundary_bond_castSucc]
    apply hlower S ?_ k.castSucc
    rw [trainMatrix_eq_nativeCoreReadback]
    exact hS

end InfoGeometry.Clifford.Cl11LocalCoreTrain
