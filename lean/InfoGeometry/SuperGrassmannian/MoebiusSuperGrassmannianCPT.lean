import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair
import InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
import InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge

/-!
# Finite reflection identities on the ordered `2|1` matrix carrier

This module records finite matrix consequences of the reflection
`τ = J Γ`, reusing the Section 86 OSp generators, parity-aware superbracket,
and Jordan-pair triple operations. It reuses Section 87's definition of the
OSp pairing element and proves its conjugation law on the `3 × 3` carrier; it
does not transport that law through the even-corner map to a BdG/QPNM matrix.

The theorems below establish an involutory matrix conjugation, reversal of the
Cartan-adjoint eigenvalue, covariance of the canonical ambient triple
operations, and the parameter-flip identity for the OSp pairing element.
They do not construct a Möbius bundle or spin structure, a time-reversal
operator or total CPT action, nor an action of `τ` on the one-dimensional
contact Jordan-pair summands. In particular, the ambient triple covariance
proved here is not a claim that `τ` exchanges the positive and negative
Jordan-pair carriers.
-/

namespace InfoGeometry.SuperGrassmannian.MoebiusReflection

open Matrix
open InfoGeometry.SuperGrassmannian.SuperconformalOSpJordanPair
open InfoGeometry.Nuclear.NuclearQuasiphononJordanPairBridge

variable {R : Type*} [CommRing R]

abbrev M₃ (R : Type*) [CommRing R] := Matrix (Fin 3) (Fin 3) R

/-- The parity operator for the Section 86 ordering `(even, odd, even)`. -/
def Gamma : M₃ R := Matrix.diagonal ![(1 : R), -1, 1]

/-- The matrix reflection `τ = J Γ`, with `J` reused from Section 85. -/
def tau : M₃ R := InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J R * Gamma

/-- The grading derivation on the canonical Section 86 matrix carrier. -/
def adH (X : M₃ R) : M₃ R := commutator (H_gen R) X

/-- `Γ` is an involution. -/
theorem Gamma_sq : Gamma (R := R) * Gamma = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gamma]

/-- The parity operator commutes with the sheet permutation `J`. -/
theorem Gamma_comm_J :
    Gamma (R := R) * InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J R =
      InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J R * Gamma := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gamma, InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
      Matrix.diagonal_apply, Matrix.mul_apply, Fin.sum_univ_three]

/-- The reflection matrix `τ = J Γ` squares to the identity. -/
theorem tau_sq : tau (R := R) * tau = 1 := by
  unfold tau
  let J := InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J R
  have hJ : J * J = 1 := InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J_involutive
  have hcomm : J * Gamma (R := R) = Gamma * J := (Gamma_comm_J (R := R)).symm
  calc
    (J * Gamma) * (J * Gamma) = J * (Gamma * J) * Gamma := by simp only [mul_assoc]
    _ = J * (J * Gamma) * Gamma := by rw [hcomm]
    _ = (J * J) * (Gamma * Gamma) := by noncomm_ring
    _ = 1 := by rw [hJ, Gamma_sq]; simp

/-- Conjugation by `τ` is multiplicative. -/
theorem tau_conj_mul (A B : M₃ R) :
    tau (R := R) * (A * B) * tau =
      (tau * A * tau) * (tau * B * tau) := by
  calc
    tau * (A * B) * tau = tau * A * B * tau := by simp only [mul_assoc]
    _ = tau * A * (1 * B) * tau := by rw [one_mul]
    _ = tau * A * (tau * tau * B) * tau := by rw [← tau_sq]
    _ = (tau * A * tau) * (tau * B * tau) := by noncomm_ring

/-- Conjugation by `τ` preserves the ordinary matrix commutator. -/
theorem tau_conj_commutator (A B : M₃ R) :
    tau (R := R) * commutator A B * tau =
      commutator (tau * A * tau) (tau * B * tau) := by
  unfold SuperconformalOSpJordanPair.commutator
  rw [Matrix.mul_sub, Matrix.sub_mul, tau_conj_mul, tau_conj_mul]

/-- Conjugation by `τ` preserves the matrix anticommutator. -/
theorem tau_conj_anticommutator (A B : M₃ R) :
    tau (R := R) * anticommutator A B * tau =
      anticommutator (tau * A * tau) (tau * B * tau) := by
  unfold anticommutator
  rw [Matrix.mul_add, Matrix.add_mul, tau_conj_mul, tau_conj_mul]

/-- The reflection intertwines the repository's parity-aware superbracket. -/
theorem tau_conj_superBracket (p q : Bool) (A B : M₃ R) :
    tau (R := R) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket p q A B * tau =
      InfoGeometry.Algebra.SupergradedBracket.superBracket p q
        (tau * A * tau) (tau * B * tau) := by
  cases p <;> cases q <;>
    simp [InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      tau_conj_mul]

/-- The reflection sends the Cartan generator to its negative. -/
theorem tau_conj_H :
    tau (R := R) * H_gen R * tau = - H_gen R := by
  unfold tau Gamma H_gen E
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
      Matrix.diagonal_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]

/-- The Cartan-adjoint derivation reverses sign under the reflection. -/
theorem tau_conj_adH (X : M₃ R) :
    adH (tau (R := R) * X * tau) = -(tau * adH X * tau) := by
  unfold adH
  have h := tau_conj_commutator (H_gen R) X
  rw [tau_conj_H] at h
  have h' : tau * SuperconformalOSpJordanPair.commutator (H_gen R) X * tau =
      -(SuperconformalOSpJordanPair.commutator (H_gen R) (tau * X * tau)) := by
    simpa [SuperconformalOSpJordanPair.commutator, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc] using h
  simpa [SuperconformalOSpJordanPair.commutator] using (congrArg Neg.neg h').symm

/-- A Cartan-adjoint eigenvector of weight `k` is sent to weight `-k`. -/
theorem tau_reverses_adH_eigenvalue (k : R) (X : M₃ R)
    (hX : adH X = k • X) :
    adH (tau (R := R) * X * tau) = (-k) • (tau * X * tau) := by
  rw [tau_conj_adH, hX]
  simp

/-- Conjugation by `τ` preserves the canonical positive ambient triple operation. -/
theorem tau_jordanPairPlus_covariant (x y z : M₃ R) :
    tau (R := R) * jordanPairPlus x y z * tau =
      jordanPairPlus (tau * x * tau) (tau * y * tau) (tau * z * tau) := by
  unfold jordanPairPlus
  rw [tau_conj_superBracket false true, tau_conj_superBracket true true]

/-- Conjugation by `τ` preserves the canonical negative ambient triple operation. -/
theorem tau_jordanPairMinus_covariant (y x w : M₃ R) :
    tau (R := R) * jordanPairMinus y x w * tau =
      jordanPairMinus (tau * y * tau) (tau * x * tau) (tau * w * tau) := by
  unfold jordanPairMinus
  rw [Matrix.mul_neg, Matrix.neg_mul,
    tau_conj_superBracket false true, tau_conj_superBracket true true]

/-- The canonical supertrace is preserved by the reflection. -/
theorem supertrace_tau_invariant (X : M₃ R) :
    supertrace (tau (R := R) * X * tau) = supertrace X := by
  have h0 : (tau * X * tau : M₃ R) 0 0 = X 2 2 := by
    unfold tau Gamma
    simp [InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
      Matrix.diagonal_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]
  have h1 : (tau * X * tau : M₃ R) 1 1 = X 1 1 := by
    unfold tau Gamma
    simp [InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
      Matrix.diagonal_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]
  have h2 : (tau * X * tau : M₃ R) 2 2 = X 0 0 := by
    unfold tau Gamma
    simp [InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
      Matrix.diagonal_apply, Matrix.mul_apply, Matrix.of_apply]
  unfold supertrace
  rw [h0, h1, h2]
  ring

/-- The Section 87 OSp pairing element is covariant under energy reversal. -/
theorem tau_intertwines_ospPairingElement (ε Δ : ℝ) :
    tau (R := ℝ) *
        ospPairingElement ε Δ * tau =
      ospPairingElement (-ε) Δ := by
  unfold ospPairingElement
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  have hE : tau (R := ℝ) * (E_gen ℝ) * tau = F_gen ℝ := by
    unfold tau Gamma E_gen F_gen E
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
        Matrix.diagonal_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]
  have hF : tau (R := ℝ) * (F_gen ℝ) * tau = E_gen ℝ := by
    unfold tau Gamma E_gen F_gen E
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian.J,
        Matrix.diagonal_apply, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_three]
  have hEF : tau (R := ℝ) * (E_gen ℝ + F_gen ℝ) * tau =
      E_gen ℝ + F_gen ℝ := by
    rw [Matrix.mul_add, Matrix.add_mul, hE, hF, add_comm]
  rw [tau_conj_H, hEF]
  simp [neg_smul, add_comm]

/-- Energy reversal is an involution on the two real parameters. -/
def energyFlip (ε Δ : ℝ) : ℝ × ℝ := (-ε, Δ)

theorem energyFlip_involutive (ε Δ : ℝ) : energyFlip (energyFlip ε Δ).1 (energyFlip ε Δ).2 = (ε, Δ) := by
  apply Prod.ext
  · dsimp [energyFlip]
    ring
  · rfl

/-- The finite matrix identities collected for this owner. -/
theorem compile_moebius_matrix_reflection :
    tau (R := ℝ) * tau = 1 ∧
    (∀ ε Δ : ℝ,
      tau * ospPairingElement ε Δ * tau =
        ospPairingElement (-ε) Δ) ∧
    (∀ X : Matrix (Fin 3) (Fin 3) ℝ,
      supertrace (tau * X * tau) = supertrace X) ∧
    (∀ x y z : Matrix (Fin 3) (Fin 3) ℝ,
      tau * jordanPairPlus x y z * tau =
        jordanPairPlus (tau * x * tau) (tau * y * tau) (tau * z * tau)) := by
  exact ⟨tau_sq, tau_intertwines_ospPairingElement,
    supertrace_tau_invariant, tau_jordanPairPlus_covariant⟩

end InfoGeometry.SuperGrassmannian.MoebiusReflection
