import Mathlib.LinearAlgebra.Matrix.Block
import InfoGeometry.Volume.PfaffianGeneral
import InfoGeometry.Volume.PfaffianPathBridge
import InfoGeometry.Quantum.NeutralKreinMajoranaFrame

/-!
# Finite doubled Majorana pairing carrier

The two isotropic halves of a doubled real carrier can be paired by a single
off-diagonal skew matrix.  This file proves only the finite algebraic
skewness and block readout; Pfaffian normalization and boundary topology are
kept in the existing volume owners.
-/

namespace InfoGeometry.Physics.MajoranaKreinPfaffianCarrier

open InfoGeometry.Volume.PfaffianPathBridge
open InfoGeometry.Volume.PfaffianGeneral

variable {R α : Type*} [CommRing R]

/-- Off-diagonal skew pairing of two copies of a finite label set. -/
def offDiagonalPairing [DecidableEq α] (K : Matrix α α R) :
    Matrix (Sum α α) (Sum α α) R :=
  Matrix.fromBlocks 0 K (-K.transpose) 0

theorem offDiagonalPairing_skew [DecidableEq α] [Fintype α]
    (K : Matrix α α R) :
    (offDiagonalPairing K).transpose = -offDiagonalPairing K := by
  rw [offDiagonalPairing, Matrix.fromBlocks_transpose]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.transpose_apply]

@[simp] theorem offDiagonalPairing_left_left [DecidableEq α]
    (K : Matrix α α R) (i j : α) :
    offDiagonalPairing K (Sum.inl i) (Sum.inl j) = 0 := by
  simp [offDiagonalPairing]

@[simp] theorem offDiagonalPairing_right_right [DecidableEq α]
    (K : Matrix α α R) (i j : α) :
    offDiagonalPairing K (Sum.inr i) (Sum.inr j) = 0 := by
  simp [offDiagonalPairing]

@[simp] theorem offDiagonalPairing_left_right [DecidableEq α]
    (K : Matrix α α R) (i j : α) :
    offDiagonalPairing K (Sum.inl i) (Sum.inr j) = K i j := by
  simp [offDiagonalPairing]

@[simp] theorem offDiagonalPairing_right_left [DecidableEq α]
    (K : Matrix α α R) (i j : α) :
    offDiagonalPairing K (Sum.inr i) (Sum.inl j) = -(K j i) := by
  simp [offDiagonalPairing]

theorem offDiagonalPairing_det_sq_eq_det_fourth
    [DecidableEq α] [Fintype α] (K : Matrix α α R) :
    (offDiagonalPairing K).det ^ 2 = K.det ^ 4 := by
  have hmul :
      offDiagonalPairing K * (offDiagonalPairing K).transpose =
        Matrix.fromBlocks (K * K.transpose) 0 0 (K.transpose * K) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [offDiagonalPairing, Matrix.fromBlocks_multiply,
        Matrix.fromBlocks_transpose, Matrix.transpose_apply, Matrix.mul_apply,
        Finset.mul_sum, Finset.sum_mul, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_transpose] at hdet
  rw [Matrix.det_fromBlocks_zero₂₁] at hdet
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_transpose] at hdet
  calc
    (offDiagonalPairing K).det ^ 2 =
        (offDiagonalPairing K).det * (offDiagonalPairing K).det := by ring
    _ = K.det * K.det * (K.det * K.det) := hdet
    _ = K.det ^ 4 := by ring

theorem abs_det_offDiagonalPairing_eq_det_sq
    [DecidableEq α] [Fintype α] (K : Matrix α α ℝ) :
    |(offDiagonalPairing K).det| = K.det ^ 2 := by
  have hsq := offDiagonalPairing_det_sq_eq_det_fourth K
  have hnonneg : 0 ≤ K.det ^ 2 := sq_nonneg _
  apply (sq_eq_sq₀ (abs_nonneg _) hnonneg).mp
  calc
    |(offDiagonalPairing K).det| ^ 2 = (offDiagonalPairing K).det ^ 2 := by
      rw [sq_abs]
    _ = K.det ^ 4 := hsq
    _ = (K.det ^ 2) ^ 2 := by ring

theorem offDiagonalPairing_det_eq_zero_iff
    [DecidableEq α] [Fintype α] (K : Matrix α α ℝ) :
    (offDiagonalPairing K).det = 0 ↔ K.det = 0 := by
  constructor
  · intro h
    have hsq : K.det ^ 2 = 0 := by
      calc
        K.det ^ 2 = |(offDiagonalPairing K).det| :=
          (abs_det_offDiagonalPairing_eq_det_sq K).symm
        _ = 0 := by simp [h]
    nlinarith
  · intro h
    have hz : |(offDiagonalPairing K).det| = 0 := by
      rw [abs_det_offDiagonalPairing_eq_det_sq K]
      simp [h]
    exact abs_eq_zero.mp hz

theorem offDiagonalPairing_det_ne_zero_iff
    [DecidableEq α] [Fintype α] (K : Matrix α α ℝ) :
    (offDiagonalPairing K).det ≠ 0 ↔ K.det ≠ 0 := by
  exact not_congr (offDiagonalPairing_det_eq_zero_iff K)

/-- Package the finite doubled pairing in the existing signed-Pfaffian owner. -/
def toSkewPairingMatrixPacket [DecidableEq α] [Fintype α]
    (K : Matrix α α ℝ) : SkewPairingMatrixPacket where
  Boundary := Sum α α
  boundaryFinite := inferInstance
  boundaryDecidableEq := inferInstance
  W := offDiagonalPairing K
  skew := by
    intro i j
    have h := congrFun (congrFun (offDiagonalPairing_skew K) j) i
    simpa [Matrix.transpose_apply] using h

/-- The existing arbitrary-pair block Pfaffian identity is exposed through
the Majorana carrier namespace without introducing a second Pfaffian API. -/
theorem blockPfaffian_sq_eq_det (n : ℕ) (a : Fin n → ℝ) :
    (pfaffianBlock n a) ^ 2 = (blockSkewMatrix n a).det :=
  pfaffian_sq_eq_det_general n a

/-! ## Neutral Krein and Majorana structures on the doubled carrier -/

def neutralKreinMetric [DecidableEq α] :
    Matrix (Sum α α) (Sum α α) R :=
  Matrix.fromBlocks 0 (1 : Matrix α α R) (1 : Matrix α α R) 0

def polarizationGrading [DecidableEq α] :
    Matrix (Sum α α) (Sum α α) R :=
  Matrix.fromBlocks (1 : Matrix α α R) 0 0 (-1 : Matrix α α R)

def polarizationExchange [DecidableEq α] :
    Matrix (Sum α α) (Sum α α) R :=
  neutralKreinMetric

theorem neutralKreinMetric_symmetric [DecidableEq α] [Fintype α] :
    (neutralKreinMetric (R := R) (α := α)).transpose = neutralKreinMetric := by
  rw [neutralKreinMetric, Matrix.fromBlocks_transpose]
  simp

theorem neutralKreinMetric_sq [DecidableEq α] [Fintype α] :
    neutralKreinMetric (R := R) (α := α) * neutralKreinMetric =
      (1 : Matrix (Sum α α) (Sum α α) R) := by
  rw [neutralKreinMetric, Matrix.fromBlocks_multiply]
  simp

theorem polarizationGrading_sq [DecidableEq α] [Fintype α] :
    polarizationGrading (R := R) (α := α) * polarizationGrading =
      (1 : Matrix (Sum α α) (Sum α α) R) := by
  rw [polarizationGrading, Matrix.fromBlocks_multiply]
  simp

theorem polarizationExchange_sq [DecidableEq α] [Fintype α] :
    polarizationExchange (R := R) (α := α) * polarizationExchange =
      (1 : Matrix (Sum α α) (Sum α α) R) := by
  exact neutralKreinMetric_sq

theorem polarizationExchange_anticommutes_grading
    [DecidableEq α] [Fintype α] :
    polarizationExchange (R := R) (α := α) * polarizationGrading =
      -(polarizationGrading * polarizationExchange) := by
  rw [polarizationExchange, polarizationGrading, neutralKreinMetric,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

theorem neutralKreinMetric_exchange_eq_one [DecidableEq α] [Fintype α] :
    neutralKreinMetric (R := R) (α := α) * polarizationExchange =
      (1 : Matrix (Sum α α) (Sum α α) R) := by
  rw [polarizationExchange]
  exact neutralKreinMetric_sq

theorem majoranaRelativeEndomorphism_eq_blockDiagonal
    [DecidableEq α] [Fintype α] (K : Matrix α α R) :
    neutralKreinMetric (R := R) (α := α) * offDiagonalPairing K =
      Matrix.fromBlocks (-K.transpose) 0 0 K := by
  rw [neutralKreinMetric, offDiagonalPairing, Matrix.fromBlocks_multiply]
  simp

end InfoGeometry.Physics.MajoranaKreinPfaffianCarrier
