import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The real Hestenes--Krein split-quaternion cell

This file isolates the algebraic consequence of a real complex structure `K`
and a Krein involution `η` which anticommute.  It is intentionally generic:
it does not identify `η` with exterior chirality or with Cayley conjugation,
and it does not choose an orientation for a particular split-octonion Zorn
channel.

For endomorphisms of a real module we define `H := K η`, the two Peirce
projectors `e₊`, `e₋`, and the two nilpotent Witt generators `q₊`, `q₋`.
All statements are finite algebraic identities in `Module.End`; no completion
or analytic extension is involved.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinSplitQuaternionBridge

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev End (W : Type*) [AddCommGroup W] [Module ℝ W] := Module.End ℝ W

structure Datum where
  K : End V
  eta : End V
  K_sq : K * K = -(1 : End V)
  eta_sq : eta * eta = (1 : End V)
  K_eta_anticomm : K * eta = -(eta * K)

def H (D : Datum (V := V)) : End V := D.K * D.eta

def ePlus (D : Datum (V := V)) : End V :=
  (1 / 2 : ℝ) • ((1 : End V) + D.eta)

def eMinus (D : Datum (V := V)) : End V :=
  (1 / 2 : ℝ) • ((1 : End V) - D.eta)

def qPlus (D : Datum (V := V)) : End V :=
  (1 / 2 : ℝ) • (H D - D.K)

def qMinus (D : Datum (V := V)) : End V :=
  (1 / 2 : ℝ) • (H D + D.K)

theorem H_sq (D : Datum (V := V)) : H D * H D = (1 : End V) := by
  dsimp [H]
  have hηK : D.eta * D.K = -(D.K * D.eta) := by
    rw [D.K_eta_anticomm]
    simp
  calc
    (D.K * D.eta) * (D.K * D.eta) =
        D.K * (D.eta * D.K) * D.eta := by noncomm_ring
    _ = D.K * (-(D.K * D.eta)) * D.eta := by rw [hηK]
    _ = (1 : End V) := by
      calc
        D.K * (-(D.K * D.eta)) * D.eta =
            -((D.K * D.K) * (D.eta * D.eta)) := by noncomm_ring
        _ = (1 : End V) := by rw [D.K_sq, D.eta_sq]; noncomm_ring

theorem K_mul_eta_eq_H (D : Datum (V := V)) : D.K * D.eta = H D := rfl

theorem eta_mul_K_eq_neg_H (D : Datum (V := V)) :
    D.eta * D.K = -(H D) := by
  rw [H]
  rw [D.K_eta_anticomm]
  simp

theorem K_mul_H_eq_neg_eta (D : Datum (V := V)) :
    D.K * H D = -(D.eta) := by
  dsimp [H]
  rw [← mul_assoc, D.K_sq]
  noncomm_ring

theorem H_mul_K_eq_eta (D : Datum (V := V)) :
    H D * D.K = D.eta := by
  dsimp [H]
  have hηK : D.eta * D.K = -(D.K * D.eta) := by
    rw [D.K_eta_anticomm]
    simp
  calc
    (D.K * D.eta) * D.K = D.K * (D.eta * D.K) := by rw [mul_assoc]
    _ = D.K * (-(D.K * D.eta)) := by rw [hηK]
    _ = D.eta := by
      calc
        D.K * (-(D.K * D.eta)) = -((D.K * D.K) * D.eta) := by noncomm_ring
        _ = D.eta := by rw [D.K_sq]; noncomm_ring

theorem eta_mul_H_eq_neg_K (D : Datum (V := V)) :
    D.eta * H D = -(D.K) := by
  dsimp [H]
  have hηK : D.eta * D.K = -(D.K * D.eta) := by
    rw [D.K_eta_anticomm]
    simp
  calc
    D.eta * (D.K * D.eta) = (D.eta * D.K) * D.eta := by rw [mul_assoc]
    _ = (-(D.K * D.eta)) * D.eta := by rw [hηK]
    _ = -(D.K) := by
      calc
        (-(D.K * D.eta)) * D.eta = -(D.K * (D.eta * D.eta)) := by noncomm_ring
        _ = -(D.K) := by rw [D.eta_sq]; simp

theorem H_mul_eta_eq_K (D : Datum (V := V)) :
    H D * D.eta = D.K := by
  dsimp [H]
  rw [mul_assoc, D.eta_sq]
  simp

theorem ePlus_sq (D : Datum (V := V)) : ePlus D * ePlus D = ePlus D := by
  dsimp [ePlus]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : ((1 : End V) + D.eta) * ((1 : End V) + D.eta) =
      (2 : ℝ) • ((1 : End V) + D.eta) := by
    calc
      ((1 : End V) + D.eta) * ((1 : End V) + D.eta) =
          (1 : End V) + D.eta + D.eta + D.eta * D.eta := by noncomm_ring
      _ = (2 : ℝ) • ((1 : End V) + D.eta) := by
        rw [D.eta_sq]
        module
  rw [h]
  module

theorem eMinus_sq (D : Datum (V := V)) : eMinus D * eMinus D = eMinus D := by
  dsimp [eMinus]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : ((1 : End V) - D.eta) * ((1 : End V) - D.eta) =
      (2 : ℝ) • ((1 : End V) - D.eta) := by
    calc
      ((1 : End V) - D.eta) * ((1 : End V) - D.eta) =
          (1 : End V) - D.eta - D.eta + D.eta * D.eta := by noncomm_ring
      _ = (2 : ℝ) • ((1 : End V) - D.eta) := by
        rw [D.eta_sq]
        module
  rw [h]
  module

theorem ePlus_mul_eMinus (D : Datum (V := V)) : ePlus D * eMinus D = 0 := by
  dsimp [ePlus, eMinus]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : ((1 : End V) + D.eta) * ((1 : End V) - D.eta) = 0 := by
    calc
      ((1 : End V) + D.eta) * ((1 : End V) - D.eta) =
          (1 : End V) - D.eta * D.eta := by noncomm_ring
      _ = 0 := by rw [D.eta_sq]; module
  rw [h]
  simp

theorem eMinus_mul_ePlus (D : Datum (V := V)) : eMinus D * ePlus D = 0 := by
  dsimp [ePlus, eMinus]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : ((1 : End V) - D.eta) * ((1 : End V) + D.eta) = 0 := by
    calc
      ((1 : End V) - D.eta) * ((1 : End V) + D.eta) =
          (1 : End V) - D.eta * D.eta := by noncomm_ring
      _ = 0 := by rw [D.eta_sq]; module
  rw [h]
  simp

theorem ePlus_add_eMinus (D : Datum (V := V)) :
    ePlus D + eMinus D = (1 : End V) := by
  dsimp [ePlus, eMinus]
  module

theorem ePlus_sub_eMinus (D : Datum (V := V)) :
    ePlus D - eMinus D = D.eta := by
  dsimp [ePlus, eMinus]
  module

theorem qPlus_sq (D : Datum (V := V)) : qPlus D * qPlus D = 0 := by
  dsimp [qPlus]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : (H D - D.K) * (H D - D.K) = 0 := by
    calc
      (H D - D.K) * (H D - D.K) =
          H D * H D - H D * D.K - D.K * H D + D.K * D.K := by
            noncomm_ring
      _ = 0 := by
        rw [H_sq D, H_mul_K_eq_eta D, K_mul_H_eq_neg_eta D, D.K_sq]
        module
  rw [h]
  simp

theorem qMinus_sq (D : Datum (V := V)) : qMinus D * qMinus D = 0 := by
  dsimp [qMinus]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : (H D + D.K) * (H D + D.K) = 0 := by
    calc
      (H D + D.K) * (H D + D.K) =
          H D * H D + H D * D.K + D.K * H D + D.K * D.K := by
            noncomm_ring
      _ = 0 := by
        rw [H_sq D, H_mul_K_eq_eta D, K_mul_H_eq_neg_eta D, D.K_sq]
        module
  rw [h]
  simp

theorem qPlus_add_qMinus (D : Datum (V := V)) :
    qPlus D + qMinus D = H D := by
  dsimp [qPlus, qMinus]
  module

theorem qMinus_sub_qPlus (D : Datum (V := V)) :
    qMinus D - qPlus D = D.K := by
  dsimp [qPlus, qMinus]
  module

theorem splitQuaternion_packet (D : Datum (V := V)) :
    H D * H D = (1 : End V) ∧
      ePlus D * ePlus D = ePlus D ∧
      eMinus D * eMinus D = eMinus D ∧
      ePlus D * eMinus D = 0 ∧
      eMinus D * ePlus D = 0 ∧
      qPlus D * qPlus D = 0 ∧
      qMinus D * qMinus D = 0 ∧
      ePlus D + eMinus D = (1 : End V) ∧
      qPlus D + qMinus D = H D := by
  exact ⟨H_sq D, ePlus_sq D, eMinus_sq D, ePlus_mul_eMinus D,
    eMinus_mul_ePlus D, qPlus_sq D, qMinus_sq D, ePlus_add_eMinus D,
    qPlus_add_qMinus D⟩

end InfoGeometry.Canonical.HestenesKreinSplitQuaternionBridge
