import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic

/-!
# Native Mathlib 4 Quaternion and Split-Quaternion Pauli Commutators

This file formalizes standard quaternions $\mathbb{H}$ and split-quaternions
$\mathbb{H}_{\text{split}}$ natively using Mathlib's `Quaternion` and `QuaternionAlgebra` types.

We define:
- Standard Quaternions: `Quat := ℍ[ℝ]` (which is `QuaternionAlgebra ℝ (-1) 0 (-1)`).
- Split-Quaternions: `SplitQuat := ℍ[ℝ, 1, 0, -1]`.

For each algebra, we define the standard generators `i`, `j`, `k`, and prove:
- Squaring relations (signature)
- Product relations
- Commutator relations `[A, B] = AB - BA`
- Anticommutator relations `{A, B} = AB + BA`

This formally establishes the signature difference:
- Standard Quaternions: $(-,-,-)$ division signature.
- Split-Quaternions: $(+,-,+)$ split signature.
-/

open scoped Quaternion

namespace InfoGeometry.Canonical.Sandbox.NativeQuaternionPauli

noncomputable section

/-! ## Section 1: Standard Quaternions ℍ -/

/-- Standard quaternion carrier over ℝ. -/
abbrev Quat := ℍ[ℝ]

def qI : Quat := ⟨0, 1, 0, 0⟩
def qJ : Quat := ⟨0, 0, 1, 0⟩
def qK : Quat := ⟨0, 0, 0, 1⟩

@[simp] theorem qI_sq : qI * qI = -1 := by
  ext <;> (unfold qI; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

@[simp] theorem qJ_sq : qJ * qJ = -1 := by
  ext <;> (unfold qJ; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

@[simp] theorem qK_sq : qK * qK = -1 := by
  ext <;> (unfold qK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem qI_mul_qJ : qI * qJ = qK := by
  ext <;> (unfold qI qJ qK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem qJ_mul_qI : qJ * qI = -qK := by
  ext <;> (unfold qI qJ qK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem qJ_mul_qK : qJ * qK = qI := by
  ext <;> (unfold qI qJ qK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem qK_mul_qJ : qK * qJ = -qI := by
  ext <;> (unfold qI qJ qK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem qK_mul_qI : qK * qI = qJ := by
  ext <;> (unfold qI qJ qK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem qI_mul_qK : qI * qK = -qJ := by
  ext <;> (unfold qI qJ qK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

/-! ## Section 2: Standard Quaternion Commutators & Anticommutators -/

def commutator {A : Type*} [Ring A] (X Y : A) : A :=
  X * Y - Y * X

def anticommutator {A : Type*} [Ring A] (X Y : A) : A :=
  X * Y + Y * X

theorem comm_qI_qJ : commutator qI qJ = 2 • qK := by
  simp [commutator, qI_mul_qJ, qJ_mul_qI, two_smul]

theorem comm_qJ_qK : commutator qJ qK = 2 • qI := by
  simp [commutator, qJ_mul_qK, qK_mul_qJ, two_smul]

theorem comm_qK_qI : commutator qK qI = 2 • qJ := by
  simp [commutator, qK_mul_qI, qI_mul_qK, two_smul]

theorem anticomm_qI_qI : anticommutator qI qI = -(2 • 1) := by
  simp [anticommutator, qI_sq, two_smul]

theorem anticomm_qJ_qJ : anticommutator qJ qJ = -(2 • 1) := by
  simp [anticommutator, qJ_sq, two_smul]

theorem anticomm_qK_qK : anticommutator qK qK = -(2 • 1) := by
  simp [anticommutator, qK_sq, two_smul]

theorem anticomm_qI_qJ : anticommutator qI qJ = 0 := by
  simp [anticommutator, qI_mul_qJ, qJ_mul_qI]

theorem anticomm_qJ_qK : anticommutator qJ qK = 0 := by
  simp [anticommutator, qJ_mul_qK, qK_mul_qJ]

theorem anticomm_qK_qI : anticommutator qK qI = 0 := by
  simp [anticommutator, qK_mul_qI, qI_mul_qK]


/-! ## Section 3: Split-Quaternions ℍ_split -/

/-- Split-quaternion carrier over ℝ, natively `ℍ[ℝ, 1, 0, -1]`. -/
abbrev SplitQuat := ℍ[ℝ, 1, 0, -1]

def sI : SplitQuat := ⟨0, 1, 0, 0⟩
def sJ : SplitQuat := ⟨0, 0, 1, 0⟩
def sK : SplitQuat := ⟨0, 0, 0, 1⟩

@[simp] theorem sI_sq : sI * sI = 1 := by
  ext <;> (unfold sI; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

@[simp] theorem sJ_sq : sJ * sJ = -1 := by
  ext <;> (unfold sJ; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

@[simp] theorem sK_sq : sK * sK = 1 := by
  ext <;> (unfold sK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem sI_mul_sJ : sI * sJ = sK := by
  ext <;> (unfold sI sJ sK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem sJ_mul_sI : sJ * sI = -sK := by
  ext <;> (unfold sI sJ sK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem sJ_mul_sK : sJ * sK = sI := by
  ext <;> (unfold sI sJ sK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem sK_mul_sJ : sK * sJ = -sI := by
  ext <;> (unfold sI sJ sK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem sK_mul_sI : sK * sI = -sJ := by
  ext <;> (unfold sI sJ sK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

theorem sI_mul_sK : sI * sK = sJ := by
  ext <;> (unfold sI sJ sK; dsimp [Mul.mul, QuaternionAlgebra.instMul]; simp)

/-! ## Section 4: Split-Quaternion Commutators & Anticommutators -/

theorem comm_sI_sJ : commutator sI sJ = 2 • sK := by
  simp [commutator, sI_mul_sJ, sJ_mul_sI, two_smul]

theorem comm_sJ_sK : commutator sJ sK = 2 • sI := by
  simp [commutator, sJ_mul_sK, sK_mul_sJ, two_smul]

theorem comm_sK_sI : commutator sK sI = -(2 • sJ) := by
  simp [commutator, sK_mul_sI, sI_mul_sK, two_smul, sub_eq_add_neg]

theorem anticomm_sI_sI : anticommutator sI sI = 2 • 1 := by
  simp [anticommutator, sI_sq, two_smul]

theorem anticomm_sJ_sJ : anticommutator sJ sJ = -(2 • 1) := by
  simp [anticommutator, sJ_sq, two_smul]

theorem anticomm_sK_sI : anticommutator sK sI = 0 := by
  simp [anticommutator, sK_mul_sI, sI_mul_sK]

theorem anticomm_sK_sK : anticommutator sK sK = 2 • 1 := by
  simp [anticommutator, sK_sq, two_smul]

theorem anticomm_sI_sJ : anticommutator sI sJ = 0 := by
  simp [anticommutator, sI_mul_sJ, sJ_mul_sI]

theorem anticomm_sJ_sK : anticommutator sJ sK = 0 := by
  simp [anticommutator, sJ_mul_sK, sK_mul_sJ]

/-- Conjugate of a split-quaternion, which is just the standard `star`. -/
def splitConj (q : SplitQuat) : SplitQuat := star q

/-- The norm-square of a split-quaternion. -/
def splitNormSq (q : SplitQuat) : ℝ :=
  q.1^2 - q.2^2 + q.3^2 - q.4^2

theorem split_mul_conj (q : SplitQuat) : q * splitConj q = (splitNormSq q : SplitQuat) := by
  ext <;> (unfold splitConj splitNormSq; dsimp [Mul.mul, QuaternionAlgebra.instMul, Star.star]; ring)

theorem split_conj_mul (q : SplitQuat) : splitConj q * q = (splitNormSq q : SplitQuat) := by
  ext <;> (unfold splitConj splitNormSq; dsimp [Mul.mul, QuaternionAlgebra.instMul, Star.star]; ring)

/-- The multiplicative inverse of a split-quaternion with non-zero norm-square. -/
def splitInv (q : SplitQuat) : SplitQuat :=
  (splitNormSq q)⁻¹ • splitConj q

theorem split_mul_inv (q : SplitQuat) (h : splitNormSq q ≠ 0) :
    q * splitInv q = 1 := by
  dsimp [splitInv]
  rw [mul_smul_comm, split_mul_conj]
  ext <;> simp [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, inv_mul_cancel₀ h]

theorem split_inv_mul (q : SplitQuat) (h : splitNormSq q ≠ 0) :
    splitInv q * q = 1 := by
  dsimp [splitInv]
  rw [smul_mul_assoc, split_conj_mul]
  ext <;> simp [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul, QuaternionAlgebra.imK_smul, inv_mul_cancel₀ h]

end

end InfoGeometry.Canonical.Sandbox.NativeQuaternionPauli
