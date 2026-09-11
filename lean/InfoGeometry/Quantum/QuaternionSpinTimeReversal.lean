import InfoGeometry.Topology.Q8V4SchurBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.SpinAffineCasimirRigidity
import Mathlib.Tactic

/-!
# Quaternion spin matrices and anti-linear time reversal are separate objects

The existing quaternion matrices are assembled into an actual faithful
representation of Mathlib's QuaternionGroup 2. Its V4 quotient is reused.
This does not identify Cl(0,3) with M2(C), nor construct a global Pin bundle.

The time-reversal operator includes complex conjugation. Its square and
Hermitian pairing are checked directly. The eigenvector statement retains
the necessary commutation of the Hamiltonian with time reversal.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace InfoGeometry.Quantum.QuaternionSpinTimeReversal

open QuaternionGroup
open InfoGeometry.Topology.Q8MonodromySpinorCover
open InfoGeometry.Topology.Q8V4SchurBridge
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Physics.SpinAffineCasimirRigidity
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open scoped BigOperators

/-!
## 1. Native Operator Algebra of the Quaternion Matrices
Instead of 64 brute-force matrix expansions, we evaluate the 9 fundamental
non-commutative relations once. The simplifier will use these to close the
group table at the operator level.
-/
section QuaternionAlgebra

@[simp] private theorem M_i_sq : M_i * M_i = -1 := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_i, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem M_j_sq : M_j * M_j = -1 := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_j, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem M_k_sq : M_k * M_k = -1 := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_k, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem M_i_M_j : M_i * M_j = M_k := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem M_j_M_i : M_j * M_i = -M_k := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem M_j_M_k : M_j * M_k = M_i := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem M_k_M_j : M_k * M_j = -M_i := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem M_k_M_i : M_k * M_i = M_j := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem M_i_M_k : M_i * M_k = -M_j := by
  ext r c; fin_cases r <;> fin_cases c <;> norm_num [M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

@[simp] private theorem neg_one_mul_matrix (A : SpinMatrix) : -(1 : SpinMatrix) * A = -A := by
  rw [Matrix.neg_mul, Matrix.one_mul]

@[simp] private theorem matrix_mul_neg_one (A : SpinMatrix) : A * -(1 : SpinMatrix) = -A := by
  rw [Matrix.mul_neg, Matrix.mul_one]

end QuaternionAlgebra

/-!
## 2. Formal Evaluation of the Group Homomorphism
-/

/-- The eight unit quaternion matrices, using the repository-owned generators. -/
def q8A (i : ZMod 4) : SpinMatrix :=
  match i.val with
  | 0 => 1
  | 1 => M_i
  | 2 => -1
  | _ => -M_i

def q8XA (i : ZMod 4) : SpinMatrix :=
  match i.val with
  | 0 => M_j
  | 1 => -M_k
  | 2 => -M_j
  | _ => M_k

def q8Matrix : QuaternionGroup 2 → SpinMatrix
  | a i => q8A i
  | xa i => q8XA i

@[simp] theorem q8Matrix_one : q8Matrix 1 = 1 := rfl

-- Informing the simplifier of the signed matrix interactions.
attribute [local simp] Matrix.neg_mul Matrix.mul_neg Matrix.one_mul Matrix.mul_one neg_neg

private theorem q8A_add (i j : ZMod 4) : q8A (i + j) = q8A i * q8A j := by
  match i, j with
  | 0, 0 => change q8A 0 = q8A 0 * q8A 0; norm_num [q8A, ZMod.val]
  | 0, 1 => change q8A 1 = q8A 0 * q8A 1; norm_num [q8A, ZMod.val]
  | 0, 2 => change q8A 2 = q8A 0 * q8A 2; norm_num [q8A, ZMod.val]
  | 0, 3 => change q8A 3 = q8A 0 * q8A 3; norm_num [q8A, ZMod.val]
  | 1, 0 => change q8A 1 = q8A 1 * q8A 0; norm_num [q8A, ZMod.val]
  | 1, 1 => change q8A 2 = q8A 1 * q8A 1; norm_num [q8A, ZMod.val]
  | 1, 2 => change q8A 3 = q8A 1 * q8A 2; norm_num [q8A, ZMod.val]
  | 1, 3 => change q8A 0 = q8A 1 * q8A 3; norm_num [q8A, ZMod.val]
  | 2, 0 => change q8A 2 = q8A 2 * q8A 0; norm_num [q8A, ZMod.val]
  | 2, 1 => change q8A 3 = q8A 2 * q8A 1; norm_num [q8A, ZMod.val]
  | 2, 2 => change q8A 0 = q8A 2 * q8A 2; norm_num [q8A, ZMod.val]
  | 2, 3 => change q8A 1 = q8A 2 * q8A 3; norm_num [q8A, ZMod.val]
  | 3, 0 => change q8A 3 = q8A 3 * q8A 0; norm_num [q8A, ZMod.val]
  | 3, 1 => change q8A 0 = q8A 3 * q8A 1; norm_num [q8A, ZMod.val]
  | 3, 2 => change q8A 1 = q8A 3 * q8A 2; norm_num [q8A, ZMod.val]
  | 3, 3 => change q8A 2 = q8A 3 * q8A 3; norm_num [q8A, ZMod.val]

private theorem q8A_xa (i j : ZMod 4) : q8XA (j - i) = q8A i * q8XA j := by
  match i, j with
  | 0, 0 => change q8XA 0 = q8A 0 * q8XA 0; norm_num [q8A, q8XA, ZMod.val]
  | 0, 1 => change q8XA 1 = q8A 0 * q8XA 1; norm_num [q8A, q8XA, ZMod.val]
  | 0, 2 => change q8XA 2 = q8A 0 * q8XA 2; norm_num [q8A, q8XA, ZMod.val]
  | 0, 3 => change q8XA 3 = q8A 0 * q8XA 3; norm_num [q8A, q8XA, ZMod.val]
  | 1, 0 => change q8XA 3 = q8A 1 * q8XA 0; norm_num [q8A, q8XA, ZMod.val]
  | 1, 1 => change q8XA 0 = q8A 1 * q8XA 1; norm_num [q8A, q8XA, ZMod.val]
  | 1, 2 => change q8XA 1 = q8A 1 * q8XA 2; norm_num [q8A, q8XA, ZMod.val]
  | 1, 3 => change q8XA 2 = q8A 1 * q8XA 3; norm_num [q8A, q8XA, ZMod.val]
  | 2, 0 => change q8XA 2 = q8A 2 * q8XA 0; norm_num [q8A, q8XA, ZMod.val]
  | 2, 1 => change q8XA 3 = q8A 2 * q8XA 1; norm_num [q8A, q8XA, ZMod.val]
  | 2, 2 => change q8XA 0 = q8A 2 * q8XA 2; norm_num [q8A, q8XA, ZMod.val]
  | 2, 3 => change q8XA 1 = q8A 2 * q8XA 3; norm_num [q8A, q8XA, ZMod.val]
  | 3, 0 => change q8XA 1 = q8A 3 * q8XA 0; norm_num [q8A, q8XA, ZMod.val]
  | 3, 1 => change q8XA 2 = q8A 3 * q8XA 1; norm_num [q8A, q8XA, ZMod.val]
  | 3, 2 => change q8XA 3 = q8A 3 * q8XA 2; norm_num [q8A, q8XA, ZMod.val]
  | 3, 3 => change q8XA 0 = q8A 3 * q8XA 3; norm_num [q8A, q8XA, ZMod.val]

private theorem q8XA_a (i j : ZMod 4) : q8XA (i + j) = q8XA i * q8A j := by
  match i, j with
  | 0, 0 => change q8XA 0 = q8XA 0 * q8A 0; norm_num [q8A, q8XA, ZMod.val]
  | 0, 1 => change q8XA 1 = q8XA 0 * q8A 1; norm_num [q8A, q8XA, ZMod.val]
  | 0, 2 => change q8XA 2 = q8XA 0 * q8A 2; norm_num [q8A, q8XA, ZMod.val]
  | 0, 3 => change q8XA 3 = q8XA 0 * q8A 3; norm_num [q8A, q8XA, ZMod.val]
  | 1, 0 => change q8XA 1 = q8XA 1 * q8A 0; norm_num [q8A, q8XA, ZMod.val]
  | 1, 1 => change q8XA 2 = q8XA 1 * q8A 1; norm_num [q8A, q8XA, ZMod.val]
  | 1, 2 => change q8XA 3 = q8XA 1 * q8A 2; norm_num [q8A, q8XA, ZMod.val]
  | 1, 3 => change q8XA 0 = q8XA 1 * q8A 3; norm_num [q8A, q8XA, ZMod.val]
  | 2, 0 => change q8XA 2 = q8XA 2 * q8A 0; norm_num [q8A, q8XA, ZMod.val]
  | 2, 1 => change q8XA 3 = q8XA 2 * q8A 1; norm_num [q8A, q8XA, ZMod.val]
  | 2, 2 => change q8XA 0 = q8XA 2 * q8A 2; norm_num [q8A, q8XA, ZMod.val]
  | 2, 3 => change q8XA 1 = q8XA 2 * q8A 3; norm_num [q8A, q8XA, ZMod.val]
  | 3, 0 => change q8XA 3 = q8XA 3 * q8A 0; norm_num [q8A, q8XA, ZMod.val]
  | 3, 1 => change q8XA 0 = q8XA 3 * q8A 1; norm_num [q8A, q8XA, ZMod.val]
  | 3, 2 => change q8XA 1 = q8XA 3 * q8A 2; norm_num [q8A, q8XA, ZMod.val]
  | 3, 3 => change q8XA 2 = q8XA 3 * q8A 3; norm_num [q8A, q8XA, ZMod.val]

private theorem q8XA_xa (i j : ZMod 4) : q8A (2 + j - i) = q8XA i * q8XA j := by
  match i, j with
  | 0, 0 => change q8A 2 = q8XA 0 * q8XA 0; norm_num [q8A, q8XA, ZMod.val]
  | 0, 1 => change q8A 3 = q8XA 0 * q8XA 1; norm_num [q8A, q8XA, ZMod.val]
  | 0, 2 => change q8A 0 = q8XA 0 * q8XA 2; norm_num [q8A, q8XA, ZMod.val]
  | 0, 3 => change q8A 1 = q8XA 0 * q8XA 3; norm_num [q8A, q8XA, ZMod.val]
  | 1, 0 => change q8A 1 = q8XA 1 * q8XA 0; norm_num [q8A, q8XA, ZMod.val]
  | 1, 1 => change q8A 2 = q8XA 1 * q8XA 1; norm_num [q8A, q8XA, ZMod.val]
  | 1, 2 => change q8A 3 = q8XA 1 * q8XA 2; norm_num [q8A, q8XA, ZMod.val]
  | 1, 3 => change q8A 0 = q8XA 1 * q8XA 3; norm_num [q8A, q8XA, ZMod.val]
  | 2, 0 => change q8A 0 = q8XA 2 * q8XA 0; norm_num [q8A, q8XA, ZMod.val]
  | 2, 1 => change q8A 1 = q8XA 2 * q8XA 1; norm_num [q8A, q8XA, ZMod.val]
  | 2, 2 => change q8A 2 = q8XA 2 * q8XA 2; norm_num [q8A, q8XA, ZMod.val]
  | 2, 3 => change q8A 3 = q8XA 2 * q8XA 3; norm_num [q8A, q8XA, ZMod.val]
  | 3, 0 => change q8A 3 = q8XA 3 * q8XA 0; norm_num [q8A, q8XA, ZMod.val]
  | 3, 1 => change q8A 0 = q8XA 3 * q8XA 1; norm_num [q8A, q8XA, ZMod.val]
  | 3, 2 => change q8A 1 = q8XA 3 * q8XA 2; norm_num [q8A, q8XA, ZMod.val]
  | 3, 3 => change q8A 2 = q8XA 3 * q8XA 3; norm_num [q8A, q8XA, ZMod.val]



/-- The finite table is checked natively against the operator algebra base rules. -/
theorem q8Matrix_mul (x y : QuaternionGroup 2) :
    q8Matrix (x * y) = q8Matrix x * q8Matrix y := by
  cases x with
  | a i =>
    cases y with
    | a j => simpa [q8Matrix] using q8A_add i j
    | xa j => simpa [q8Matrix] using q8A_xa i j
  | xa i =>
    cases y with
    | a j => simpa [q8Matrix] using q8XA_a i j
    | xa j => simpa [q8Matrix] using q8XA_xa i j

/-- Unit-valued realization of the actual finite group, not only its relations. -/
def q8Representation : QuaternionGroup 2 →* SpinMatrixˣ where
  toFun q :=
    { val := q8Matrix q
      inv := q8Matrix q⁻¹
      val_inv := by rw [← q8Matrix_mul]; simp
      inv_val := by rw [← q8Matrix_mul]; simp }
  map_one' := by apply Units.ext; exact q8Matrix_one
  map_mul' x y := by apply Units.ext; exact q8Matrix_mul x y

/-!
## 3. Injectivity via the Homomorphism Kernel
Instead of checking 64 negative combinations, we evaluate the kernel.
-/

private theorem q8Matrix_eq_one_iff (z : QuaternionGroup 2) : q8Matrix z = 1 ↔ z = 1 := by
  constructor
  · intro h
    cases z with
    | a i =>
      fin_cases i
      · rfl
      · revert h; simp [q8Matrix, q8A, ZMod.val, M_i]; intro h; have h0 := congrArg (fun (m : SpinMatrix) => Complex.im (m 0 0)) h; revert h0; simp
      · revert h; simp [q8Matrix, q8A, ZMod.val]; intro h; have h0 := congrArg (fun (m : SpinMatrix) => Complex.re (m 0 0)) h; revert h0; norm_num
      · revert h; simp [q8Matrix, q8A, ZMod.val, M_i]; intro h; have h0 := congrArg (fun (m : SpinMatrix) => Complex.im (m 0 0)) h; revert h0; simp
    | xa i =>
      fin_cases i
      · revert h; simp [q8Matrix, q8XA, ZMod.val, M_j]; intro h; have h0 := congrArg (fun (m : SpinMatrix) => Complex.re (m 0 1)) h; revert h0; norm_num
      · revert h; simp [q8Matrix, q8XA, ZMod.val, M_k]; intro h; have h0 := congrArg (fun (m : SpinMatrix) => Complex.im (m 0 1)) h; revert h0; simp
      · revert h; simp [q8Matrix, q8XA, ZMod.val, M_j]; intro h; have h0 := congrArg (fun (m : SpinMatrix) => Complex.re (m 0 1)) h; revert h0; norm_num
      · revert h; simp [q8Matrix, q8XA, ZMod.val, M_k]; intro h; have h0 := congrArg (fun (m : SpinMatrix) => Complex.im (m 0 1)) h; revert h0; simp
  · rintro rfl; exact q8Matrix_one

theorem q8Representation_injective : Function.Injective q8Representation := by
  intro x y h
  have h1 : (q8Representation x) * (q8Representation y)⁻¹ = 1 := mul_inv_eq_one.mpr h
  rw [← map_inv, ← map_mul] at h1
  have h2 : q8Matrix (x * y⁻¹) = 1 := congrArg Units.val h1
  have h3 := (q8Matrix_eq_one_iff _).mp h2
  exact mul_inv_eq_one.mp h3

theorem q8Matrix_injective : Function.Injective q8Matrix := by
  intro x y h
  have h_rep : q8Representation x = q8Representation y := by apply Units.ext; exact h
  exact q8Representation_injective h_rep

/-- The precise two-element kernel of the already installed rotational quotient. -/
theorem q8ToV4_kernel (q : QuaternionGroup 2) :
    q8ToV4 q = 1 ↔ q = a 0 ∨ q = a 2 := by
  fin_cases q <;> decide

theorem central_sign_matrix : q8Matrix (a 2) = -(1 : SpinMatrix) := rfl

/-!
## 4. Time Reversal and Kramers Algebra
-/

abbrev TwoSpinor := InfoGeometry.Algebra.FiniteSpin.Vec2C

/-- Anti-linear time reversal; its real matrix factor is the existing M_j. -/
def timeReverse (ψ : TwoSpinor) : TwoSpinor := ![star (ψ 1), -star (ψ 0)]

theorem timeReverse_eq_quaternion_conjugation (ψ : TwoSpinor) :
    timeReverse ψ = Matrix.mulVec M_j (fun i => star (ψ i)) := by
  funext i
  fin_cases i <;> simp [timeReverse, M_j, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem timeReverse_zero : timeReverse 0 = 0 := by
  funext i
  fin_cases i <;> simp [timeReverse]

theorem timeReverse_smul (c : ℂ) (ψ : TwoSpinor) :
    timeReverse (c • ψ) = star c • timeReverse ψ := by
  funext i
  fin_cases i <;> simp [timeReverse]

/-- The minus sign is checked with conjugation included, not discarded. -/
theorem timeReverse_sq (ψ : TwoSpinor) : timeReverse (timeReverse ψ) = -ψ := by
  funext i
  fin_cases i <;> simp [timeReverse]

/-- Standard Hermitian coordinate pairing on the existing complex two-spinor carrier. -/
def spinorPair (ψ χ : TwoSpinor) : ℂ := ∑ i, star (ψ i) * χ i

theorem timeReverse_antiunitary_pairing (ψ χ : TwoSpinor) :
    spinorPair (timeReverse ψ) (timeReverse χ) = star (spinorPair ψ χ) := by
  simp [spinorPair, timeReverse, Fin.sum_univ_two]
  ring

theorem timeReverse_orthogonal (ψ : TwoSpinor) : spinorPair ψ (timeReverse ψ) = 0 := by
  simp [spinorPair, timeReverse, Fin.sum_univ_two]
  ring

theorem timeReverse_ne_zero {ψ : TwoSpinor} (hψ : ψ ≠ 0) : timeReverse ψ ≠ 0 := by
  intro h
  have h2 := congrArg timeReverse h
  rw [timeReverse_sq, timeReverse_zero, neg_eq_zero] at h2
  exact hψ h2

/-- Kramers pairing requires the Hamiltonian symmetry and a real eigenvalue. -/
theorem kramers_eigenpair (H : SpinMatrix) (eigenvalue : ℝ) (ψ : TwoSpinor)
    (hψ : ψ ≠ 0)
    (hH : ∀ χ : TwoSpinor, Matrix.mulVec H (timeReverse χ) =
      timeReverse (Matrix.mulVec H χ))
    (heig : Matrix.mulVec H ψ = (eigenvalue : ℂ) • ψ) :
    timeReverse ψ ≠ 0 ∧ spinorPair ψ (timeReverse ψ) = 0 ∧
      Matrix.mulVec H (timeReverse ψ) = (eigenvalue : ℂ) • timeReverse ψ := by
  refine ⟨timeReverse_ne_zero hψ, timeReverse_orthogonal ψ, ?_⟩
  rw [hH, heig, timeReverse_smul]
  simp [mul_comm]

/-- A spin observable is time-reversal odd, not automatically an invariant Hamiltonian. -/
theorem cartan_timeReverse_odd (ψ : TwoSpinor) :
    timeReverse (Matrix.mulVec isospin3 ψ) =
      -(Matrix.mulVec isospin3 (timeReverse ψ)) := by
  funext i
  fin_cases i <;>
    simp [timeReverse, isospin3, pauli3, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

/-- In spin one-half the proposed quadratic squeezing generator is identically zero. -/
theorem spin_half_quadratic_squeeze_zero :
    isospinPlus * isospinPlus - isospinMinus * isospinMinus = (0 : SpinMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [isospinPlus, isospinMinus, pauli1, pauli2, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]

end InfoGeometry.Quantum.QuaternionSpinTimeReversal
