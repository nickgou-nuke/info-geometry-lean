import Mathlib

/-!
# Finite Krein adjoint and commutant calculus

This file proves only finite-dimensional matrix identities.  The matrix `eta`
is supplied with the involution law `eta * eta = 1`; no Hilbert-space,
`C*`-algebra, or Kasparov-product structure is asserted here.
-/

namespace InfoGeometry.Physics.Algebra

open Matrix
noncomputable section

variable {n : ℕ}
variable (eta : Matrix (Fin n) (Fin n) ℂ)
variable (h_eta_sq : eta * eta = 1)

/-- Krein adjoint relative to an involutive metric matrix. -/
def kreinAdjoint (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  eta * Aᴴ * eta

theorem kreinAdjoint_involutive
    (h_eta_sq : eta * eta = 1)
    (h_eta_selfAdjoint : etaᴴ = eta)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    kreinAdjoint eta (kreinAdjoint eta A) = A := by
  dsimp [kreinAdjoint]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, h_eta_selfAdjoint]
  calc
    eta * (eta * (A * eta)) * eta =
        (eta * eta) * A * (eta * eta) := by
          simp only [mul_assoc]
    _ = A := by simp [h_eta_sq]

theorem kreinAdjoint_mul
    (h_eta_sq : eta * eta = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    kreinAdjoint eta (A * B) =
      kreinAdjoint eta B * kreinAdjoint eta A := by
  dsimp [kreinAdjoint]
  rw [conjTranspose_mul]
  calc
    eta * (Bᴴ * Aᴴ) * eta =
        eta * Bᴴ * Aᴴ * eta := by
      simp only [mul_assoc]
    _ = eta * Bᴴ * (eta * eta) * Aᴴ * eta := by
      rw [h_eta_sq, mul_one]
    _ = (eta * Bᴴ * eta) * (eta * Aᴴ * eta) := by
      simp only [mul_assoc]

/-- Matrix commutator. -/
def comm (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

theorem kreinAdjoint_comm_eq_neg
    (h_eta_sq : eta * eta = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    kreinAdjoint eta (comm A B) =
      -comm (kreinAdjoint eta A) (kreinAdjoint eta B) := by
  dsimp [comm, kreinAdjoint]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul]
  simp only [mul_sub, sub_mul]
  rw [show eta * (Bᴴ * Aᴴ) * eta =
      (eta * Bᴴ * eta) * (eta * Aᴴ * eta) by
        calc
          eta * (Bᴴ * Aᴴ) * eta = eta * Bᴴ * Aᴴ * eta := by
            simp only [mul_assoc]
          _ = eta * Bᴴ * (eta * eta) * Aᴴ * eta := by
            rw [h_eta_sq, mul_one]
          _ = (eta * Bᴴ * eta) * (eta * Aᴴ * eta) := by
            simp only [mul_assoc],
    show eta * (Aᴴ * Bᴴ) * eta =
      (eta * Aᴴ * eta) * (eta * Bᴴ * eta) by
        calc
          eta * (Aᴴ * Bᴴ) * eta = eta * Aᴴ * Bᴴ * eta := by
            simp only [mul_assoc]
          _ = eta * Aᴴ * (eta * eta) * Bᴴ * eta := by
            rw [h_eta_sq, mul_one]
          _ = (eta * Aᴴ * eta) * (eta * Bᴴ * eta) := by
            simp only [mul_assoc]]
  simp only [sub_eq_add_neg]
  abel

/-- The Krein-skew and Krein-symmetric operator sectors. -/
def kreinSkew (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  kreinAdjoint eta A = -A

def kreinSymmetric (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  kreinAdjoint eta A = A

theorem kreinSkew_comm_closed
    (h_eta_sq : eta * eta = 1)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : kreinSkew eta A) (hB : kreinSkew eta B) :
    kreinSkew eta (comm A B) := by
  calc
    kreinAdjoint eta (comm A B) =
        -comm (kreinAdjoint eta A) (kreinAdjoint eta B) :=
      kreinAdjoint_comm_eq_neg eta h_eta_sq A B
    _ = -comm (-A) (-B) := by rw [hA, hB]
    _ = -comm A B := by simp [comm]

theorem kreinSkew_comm_kreinSymmetric
    (h_eta_sq : eta * eta = 1)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : kreinSkew eta A) (hB : kreinSymmetric eta B) :
    kreinSymmetric eta (comm A B) := by
  calc
    kreinAdjoint eta (comm A B) =
        -comm (kreinAdjoint eta A) (kreinAdjoint eta B) :=
      kreinAdjoint_comm_eq_neg eta h_eta_sq A B
    _ = -comm (-A) B := by rw [hA, hB]
    _ = comm A B := by
      simp only [comm, neg_mul, sub_eq_add_neg]
      noncomm_ring

theorem kreinSymmetric_comm_closed
    (h_eta_sq : eta * eta = 1)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : kreinSymmetric eta A) (hB : kreinSymmetric eta B) :
    kreinSkew eta (comm A B) := by
  calc
    kreinAdjoint eta (comm A B) =
        -comm (kreinAdjoint eta A) (kreinAdjoint eta B) :=
      kreinAdjoint_comm_eq_neg eta h_eta_sq A B
    _ = -comm A B := by rw [hA, hB]

/-- The linear Lie-Cartan involution induced by the Krein adjoint. -/
def kreinCartanInvolution (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  -kreinAdjoint eta A

theorem kreinAdjoint_neg
    (A : Matrix (Fin n) (Fin n) ℂ) :
    kreinAdjoint eta (-A) = -kreinAdjoint eta A := by
  simp [kreinAdjoint]

theorem kreinCartanInvolution_involutive
    (h_eta_sq : eta * eta = 1)
    (h_eta_selfAdjoint : etaᴴ = eta)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    kreinCartanInvolution eta
        (kreinCartanInvolution eta A) = A := by
  rw [kreinCartanInvolution, kreinCartanInvolution, kreinAdjoint_neg]
  simp only [neg_neg]
  exact kreinAdjoint_involutive eta h_eta_sq h_eta_selfAdjoint A

theorem kreinCartanInvolution_comm
    (h_eta_sq : eta * eta = 1)
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    kreinCartanInvolution eta (comm A B) =
      comm (kreinCartanInvolution eta A)
        (kreinCartanInvolution eta B) := by
  calc
    kreinCartanInvolution eta (comm A B) =
        -kreinAdjoint eta (comm A B) := rfl
    _ = -(-comm (kreinAdjoint eta A) (kreinAdjoint eta B)) := by
      rw [kreinAdjoint_comm_eq_neg eta h_eta_sq A B]
    _ = comm (-kreinAdjoint eta A) (-kreinAdjoint eta B) := by
      simp [comm]
    _ = comm (kreinCartanInvolution eta A)
        (kreinCartanInvolution eta B) := by rfl

theorem kreinCartanInvolution_fixed_iff_kreinSkew
    (A : Matrix (Fin n) (Fin n) ℂ) :
    kreinCartanInvolution eta A = A ↔ kreinSkew eta A := by
  simp [kreinCartanInvolution, kreinSkew, neg_eq_iff_eq_neg]

theorem kreinCartanInvolution_antifixed_iff_kreinSymmetric
    (A : Matrix (Fin n) (Fin n) ℂ) :
    kreinCartanInvolution eta A = -A ↔ kreinSymmetric eta A := by
  simp only [kreinCartanInvolution, kreinSymmetric, neg_inj]

/-- Finite spinor bilinear, represented as a `1 × 1` matrix. -/
def kreinBilinear
    (x : Matrix (Fin n) (Fin 1) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (y : Matrix (Fin n) (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ :=
  xᴴ * eta * A * y

theorem kreinBilinear_adjoint
    (h_eta_sq : eta * eta = 1)
    (x : Matrix (Fin n) (Fin 1) ℂ)
    (A C : Matrix (Fin n) (Fin n) ℂ)
    (y : Matrix (Fin n) (Fin 1) ℂ) :
      kreinBilinear eta (C * x) A y =
      kreinBilinear eta x (kreinAdjoint eta C * A) y := by
  dsimp [kreinBilinear, kreinAdjoint]
  rw [conjTranspose_mul]
  have h_cancel (Z : Matrix (Fin n) (Fin n) ℂ) :
      eta * (eta * Z) = Z := by
    calc
      eta * (eta * Z) = (eta * eta) * Z := by rw [mul_assoc]
      _ = Z := by rw [h_eta_sq, one_mul]
  have hc := congrArg
    (fun Z : Matrix (Fin n) (Fin n) ℂ => xᴴ * Z * y)
    (h_cancel (Cᴴ * (eta * A)))
  convert hc.symm using 1 <;> simp only [Matrix.mul_assoc]

theorem kreinAdjoint_comm
    (A C : Matrix (Fin n) (Fin n) ℂ)
    (h_eta_sq : eta * eta = 1)
    (h : comm A C = 0) :
    comm (kreinAdjoint eta A) (kreinAdjoint eta C) = 0 := by
  dsimp [comm] at h ⊢
  have h_prod (X Y : Matrix (Fin n) (Fin n) ℂ) :
      kreinAdjoint eta X * kreinAdjoint eta Y =
        eta * (Y * X)ᴴ * eta := by
    dsimp [kreinAdjoint]
    calc
      (eta * Xᴴ * eta) * (eta * Yᴴ * eta) =
          eta * Xᴴ * (eta * eta) * Yᴴ * eta := by
            simp only [mul_assoc]
      _ = eta * Xᴴ * 1 * Yᴴ * eta := by rw [h_eta_sq]
      _ = eta * Xᴴ * Yᴴ * eta := by rw [Matrix.mul_one]
      _ = eta * (Xᴴ * Yᴴ) * eta := by simp only [mul_assoc]
      _ = eta * (Y * X)ᴴ * eta := by rw [← conjTranspose_mul]
  have h_comm : A * C = C * A := by
    exact eq_of_sub_eq_zero h
  calc
    kreinAdjoint eta A * kreinAdjoint eta C -
          kreinAdjoint eta C * kreinAdjoint eta A =
        eta * (C * A)ᴴ * eta - eta * (A * C)ᴴ * eta := by
          rw [h_prod A C, h_prod C A]
    _ = eta * (A * C)ᴴ * eta - eta * (A * C)ᴴ * eta := by rw [h_comm]
    _ = 0 := sub_self _

end
end InfoGeometry.Physics.Algebra
