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

/-- Matrix commutator. -/
def comm (A B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  A * B - B * A

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
