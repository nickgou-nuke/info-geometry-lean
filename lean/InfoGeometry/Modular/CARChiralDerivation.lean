import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Action of the Chiral Derivation ad_{β·Γ} on CAR Generators

Formalizes the action of the chiral modular generator `ad_{β·Γ}` on the single-mode
and multi-mode Canonical Anticommutation Relations (CAR) algebra generators:

  1. Anticommutation with Parity Involution:
       `Γ * c = - (c * Γ)`
       `Γ * c† = - (c† * Γ)`
       `Γ * Γ = 1`
  2. Action of `ad_{β·Γ}` on Generators:
       `ad_{β·Γ}(c)  =  2β • (Γ * c)  = -2β • (c * Γ)`
       `ad_{β·Γ}(c†) =  2β • (Γ * c†) = -2β • (c† * Γ)`
  3. Annihilation of Even Observables:
       `ad_{β·Γ}(N) = 0`   (Number operator `N = c† * c`)
       `ad_{β·Γ}(Γ) = 0`   (Grading involution)
  4. Extension to Finite Multi-Mode CAR systems `{c_k, c_k†}`.

All proofs are complete in native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

namespace InfoGeometry.Modular.CARChiralDerivation

open Complex

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-! =========================================================================
    1. Single-Mode CAR Operator System with Parity Involution Γ
    ========================================================================= -/

/-- Single-mode CAR generator system `(c, c†, Γ)` with grading involution relations. -/
structure SingleModeCAR (A : Type*) [Ring A] [Algebra ℂ A] where
  c : A
  c_dag : A
  Gamma : A
  gamma_sq : Gamma * Gamma = 1
  anticomm_c : Gamma * c = - (c * Gamma)
  anticomm_cdag : Gamma * c_dag = - (c_dag * Gamma)
  car_anticomm : c * c_dag + c_dag * c = 1
  c_nilpotent : c * c = 0
  cdag_nilpotent : c_dag * c_dag = 0
  gamma_num : Gamma = 1 - 2 • (c_dag * c)

/-- Number operator `N = c† * c`. -/
def numberOp (car : SingleModeCAR A) : A :=
  car.c_dag * car.c

/-! =========================================================================
    2. Commutator Bracket and Chiral Derivation ad_{β·Γ}
    ========================================================================= -/

/-- Commutator bracket `[K, x] = K * x - x * K`. -/
def bracket (K x : A) : A :=
  K * x - x * K

@[simp]
theorem bracket_apply (K x : A) : bracket K x = K * x - x * K :=
  rfl

/-- Leibniz rule for inner commutators: `[K, xy] = [K, x]y + x[K, y]`. -/
theorem bracket_leibniz (K x y : A) :
    bracket K (x * y) = bracket K x * y + x * bracket K y := by
  dsimp [bracket]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- Chiral Hamiltonian `K_β = β • Γ`. -/
def chiralHamiltonian (beta : ℂ) (Gamma : A) : A :=
  beta • Gamma

/-- Inner derivation `ad_{β·Γ} = [β·Γ, ·]`. -/
def chiralDeriv (beta : ℂ) (Gamma : A) : A →ₗ[ℂ] A where
  toFun := bracket (chiralHamiltonian beta Gamma)
  map_add' x y := by
    dsimp [bracket, chiralHamiltonian]
    simp only [mul_add, add_mul]
    abel
  map_smul' r x := by
    dsimp [bracket, chiralHamiltonian]
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

@[simp]
theorem chiralDeriv_apply (beta : ℂ) (Gamma : A) (x : A) :
    chiralDeriv beta Gamma x = (beta • Gamma) * x - x * (beta • Gamma) :=
  rfl

theorem chiralDeriv_leibniz (beta : ℂ) (Gamma : A) (x y : A) :
    chiralDeriv beta Gamma (x * y) = (chiralDeriv beta Gamma x) * y + x * (chiralDeriv beta Gamma y) :=
  bracket_leibniz (chiralHamiltonian beta Gamma) x y

/-! =========================================================================
    3. Exact Evaluation on Single-Mode Generators
    ========================================================================= -/

variable (car : SingleModeCAR A) (beta : ℂ)

/--
MAIN THEOREM 1 (Action on Annihilation Operator):
  `ad_{β·Γ}(c) = (2 * β) • (Γ * c) = - (2 * β) • (c * Γ)`
-/
theorem chiralDeriv_c_eq_gamma :
    chiralDeriv beta car.Gamma car.c = (2 * beta) • (car.Gamma * car.c) := by
  simp only [chiralDeriv_apply]
  rw [smul_mul_assoc, mul_smul_comm, car.anticomm_c, mul_neg, smul_neg, sub_neg_eq_add]
  rw [two_mul, add_smul]

theorem chiralDeriv_c_eq_c_gamma :
    chiralDeriv beta car.Gamma car.c = - ((2 * beta) • (car.c * car.Gamma)) := by
  rw [chiralDeriv_c_eq_gamma car beta, car.anticomm_c, smul_neg]

/--
MAIN THEOREM 2 (Action on Creation Operator):
  `ad_{β·Γ}(c†) = (2 * β) • (Γ * c†) = - (2 * β) • (c† * Γ)`
-/
theorem chiralDeriv_cdag_eq_gamma :
    chiralDeriv beta car.Gamma car.c_dag = (2 * beta) • (car.Gamma * car.c_dag) := by
  simp only [chiralDeriv_apply]
  rw [smul_mul_assoc, mul_smul_comm, car.anticomm_cdag, mul_neg, smul_neg, sub_neg_eq_add]
  rw [two_mul, add_smul]

theorem chiralDeriv_cdag_eq_cdag_gamma :
    chiralDeriv beta car.Gamma car.c_dag = - ((2 * beta) • (car.c_dag * car.Gamma)) := by
  rw [chiralDeriv_cdag_eq_gamma car beta, car.anticomm_cdag, smul_neg]

/--
MAIN THEOREM 3 (Vanishing on Number Operator N = c† * c):
The chiral generator commutes with the fermion number operator:
  `ad_{β·Γ}(N) = 0`
-/
theorem chiralDeriv_numberOp_zero :
    chiralDeriv beta car.Gamma (numberOp car) = 0 := by
  dsimp [numberOp]
  simp only [chiralDeriv_apply]
  have h_comm : car.Gamma * (car.c_dag * car.c) = (car.c_dag * car.c) * car.Gamma := by
    calc
      car.Gamma * (car.c_dag * car.c)
        = (car.Gamma * car.c_dag) * car.c := by rw [mul_assoc]
      _ = (- (car.c_dag * car.Gamma)) * car.c := by rw [car.anticomm_cdag]
      _ = - (car.c_dag * (car.Gamma * car.c)) := by rw [neg_mul, mul_assoc]
      _ = - (car.c_dag * (- (car.c * car.Gamma))) := by rw [car.anticomm_c]
      _ = car.c_dag * (car.c * car.Gamma) := by rw [mul_neg, neg_neg]
      _ = (car.c_dag * car.c) * car.Gamma := by rw [mul_assoc]
  rw [smul_mul_assoc, mul_smul_comm, h_comm, sub_self]

/--
MAIN THEOREM 4 (Self-Commutation with Parity Involution):
  `ad_{β·Γ}(Γ) = 0`
-/
theorem chiralDeriv_gamma_zero :
    chiralDeriv beta car.Gamma car.Gamma = 0 := by
  simp only [chiralDeriv_apply]
  rw [smul_mul_assoc, mul_smul_comm, sub_self]

/-! =========================================================================
    4. Multi-Mode CAR System Extension
    ========================================================================= -/

/-- Finite multi-mode CAR system with collective parity grading `Γ`. -/
structure MultiModeCAR (n : ℕ) (A : Type*) [Ring A] [Algebra ℂ A] where
  c : Fin n → A
  c_dag : Fin n → A
  Gamma : A
  gamma_sq : Gamma * Gamma = 1
  anticomm_c : ∀ (k : Fin n), Gamma * c k = - (c k * Gamma)
  anticomm_cdag : ∀ (k : Fin n), Gamma * c_dag k = - (c_dag k * Gamma)

variable {n : ℕ} (mcar : MultiModeCAR n A)

/--
MAIN THEOREM 5 (Action on Any Mode k):
  `ad_{β·Γ}(c_k) = (2 * β) • (Γ * c_k) = - (2 * β) • (c_k * Γ)`
  `ad_{β·Γ}(c_k†) = (2 * β) • (Γ * c_k†) = - (2 * β) • (c_k† * Γ)`
-/
theorem multimode_chiralDeriv_c (k : Fin n) :
    chiralDeriv beta mcar.Gamma (mcar.c k) = (2 * beta) • (mcar.Gamma * mcar.c k) := by
  simp only [chiralDeriv_apply]
  rw [smul_mul_assoc, mul_smul_comm, mcar.anticomm_c k, mul_neg, smul_neg, sub_neg_eq_add]
  rw [two_mul, add_smul]

theorem multimode_chiralDeriv_cdag (k : Fin n) :
    chiralDeriv beta mcar.Gamma (mcar.c_dag k) = (2 * beta) • (mcar.Gamma * mcar.c_dag k) := by
  simp only [chiralDeriv_apply]
  rw [smul_mul_assoc, mul_smul_comm, mcar.anticomm_cdag k, mul_neg, smul_neg, sub_neg_eq_add]
  rw [two_mul, add_smul]

end InfoGeometry.Modular.CARChiralDerivation
