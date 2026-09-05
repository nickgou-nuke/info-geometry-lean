import InfoGeometry.Topology.Q8V4SchurBridge
import InfoGeometry.Physics.SpinAffineCasimirRigidity

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

namespace InfoGeometry.Quantum.QuaternionSpinTimeReversal

open QuaternionGroup
open InfoGeometry.Topology.Q8MonodromySpinorCover
open InfoGeometry.Topology.Q8V4SchurBridge
open InfoGeometry.Topology.V4RootSystem
open InfoGeometry.Physics.SpinAffineCasimirRigidity
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open scoped BigOperators

/-- The eight unit quaternion matrices, using the repository-owned generators. -/
def q8Matrix : QuaternionGroup 2 → SpinMatrix
  | a 0 => 1
  | a 1 => M_i
  | a 2 => -1
  | a 3 => -M_i
  | xa 0 => M_j
  | xa 1 => -M_k
  | xa 2 => -M_j
  | xa 3 => M_k

@[simp] theorem q8Matrix_one : q8Matrix 1 = 1 := rfl

/-- The finite table is checked against native matrix multiplication. -/
theorem q8Matrix_mul (x y : QuaternionGroup 2) :
    q8Matrix (x * y) = q8Matrix x * q8Matrix y := by
  fin_cases x <;> fin_cases y <;> funext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
      QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa,
      q8Matrix, M_i, M_j, M_k, Matrix.mul_apply, Fin.sum_univ_two]

/-- Unit-valued realization of the actual finite group, not only its relations. -/
def q8Representation : QuaternionGroup 2 →* SpinMatrixˣ where
  toFun q :=
    { val := q8Matrix q
      inv := q8Matrix q⁻¹
      val_inv := by rw [← q8Matrix_mul]; simp
      inv_val := by rw [← q8Matrix_mul]; simp }
  map_one' := by apply Units.ext; exact q8Matrix_one
  map_mul' x y := by apply Units.ext; exact q8Matrix_mul x y

theorem q8Matrix_injective : Function.Injective q8Matrix := by
  intro x y h
  have h00r := congrArg (fun M : SpinMatrix => (M 0 0).re) h
  have h00i := congrArg (fun M : SpinMatrix => (M 0 0).im) h
  have h01r := congrArg (fun M : SpinMatrix => (M 0 1).re) h
  have h01i := congrArg (fun M : SpinMatrix => (M 0 1).im) h
  fin_cases x <;> fin_cases y <;>
    norm_num [q8Matrix, M_i, M_j, M_k] at h00r h00i h01r h01i ⊢

theorem q8Representation_injective : Function.Injective q8Representation := by
  intro x y h
  apply q8Matrix_injective
  exact congrArg (fun u : SpinMatrixˣ => (u : SpinMatrix)) h

/-- The precise two-element kernel of the already installed rotational quotient. -/
theorem q8ToV4_kernel (q : QuaternionGroup 2) :
    q8ToV4 q = 1 ↔ q = a 0 ∨ q = a 2 := by
  fin_cases q <;> decide

theorem central_sign_matrix : q8Matrix (a 2) = -(1 : SpinMatrix) := rfl

abbrev TwoSpinor := Fin 2 → ℂ

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
theorem kramers_eigenpair (H : SpinMatrix) (λ : ℝ) (ψ : TwoSpinor)
    (hψ : ψ ≠ 0)
    (hH : ∀ χ : TwoSpinor, Matrix.mulVec H (timeReverse χ) =
      timeReverse (Matrix.mulVec H χ))
    (heig : Matrix.mulVec H ψ = (λ : ℂ) • ψ) :
    timeReverse ψ ≠ 0 ∧ spinorPair ψ (timeReverse ψ) = 0 ∧
      Matrix.mulVec H (timeReverse ψ) = (λ : ℂ) • timeReverse ψ := by
  refine ⟨timeReverse_ne_zero hψ, timeReverse_orthogonal ψ, ?_⟩
  rw [hH, heig, timeReverse_smul]
  simp

/-- A spin observable is time-reversal odd, not automatically an invariant Hamiltonian. -/
theorem cartan_timeReverse_odd (ψ : TwoSpinor) :
    timeReverse (Matrix.mulVec isospin3 ψ) =
      -(Matrix.mulVec isospin3 (timeReverse ψ)) := by
  funext i
  fin_cases i <;>
    simp [timeReverse, isospin3, pauli3, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- In spin one-half the proposed quadratic squeezing generator is identically zero. -/
theorem spin_half_quadratic_squeeze_zero :
    isospinPlus * isospinPlus - isospinMinus * isospinMinus = (0 : SpinMatrix) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [isospinPlus, isospinMinus, pauli1, pauli2,
      Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Quantum.QuaternionSpinTimeReversal
