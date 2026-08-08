import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Clifford and parafermion braid interfaces

This file separates static generator systems from braid/Yang--Baxter data.
It contains theorem boundaries only as structure fields, avoiding speculative
existence claims such as "every parafermion system has a braid operator".
-/

namespace InfoGeometry.Algebra

/-- Static Majorana/Clifford generators. -/
structure MajoranaSystem (n : Nat) (A : Type*) [Ring A] where
  gamma : Fin n → A
  square_one : ∀ i, gamma i * gamma i = 1
  anti_comm : ∀ i j, i ≠ j → gamma i * gamma j = - (gamma j * gamma i)

/-- Trivial instance of MajoranaSystem on PUnit. -/
def punitMajoranaSystem (n : Nat) : MajoranaSystem n PUnit where
  gamma _ := ⟨⟩
  square_one _ := rfl
  anti_comm _ _ _ := rfl

/-- Exact scalar data for `1 / sqrt 2` over an arbitrary coefficient field. -/
structure CliffordBraidScalars (K : Type*) [Field K] where
  invSqrtTwo : K
  invSqrtTwo_sq : invSqrtTwo * invSqrtTwo = (1 : K) / 2

/-- Real instance of CliffordBraidScalars. -/
noncomputable def realCliffordBraidScalars : CliffordBraidScalars ℝ where
  invSqrtTwo := (Real.sqrt 2)⁻¹
  invSqrtTwo_sq := by
    rw [← mul_inv]
    rw [Real.mul_self_sqrt (by norm_num)]
    exact inv_eq_one_div (2 : ℝ)

/-- Certified Clifford braid operators. -/
structure CliffordBraidData (A : Type*) [Ring A] where
  B : Nat → A
  squareTarget : Nat → A
  square_eq_target : ∀ i, B i * B i = squareTarget i
  fourth_central_sign : ∀ i, B i ^ 4 = -1
  eighth_identity : ∀ i, B i ^ 8 = 1
  adjacent_artin : ∀ i, B i * B (i+1) * B i = B (i+1) * B i * B (i+1)
  far_commute : ∀ i j, i + 1 < j → B i * B j = B j * B i

/-- Trivial instance of CliffordBraidData on PUnit. -/
def punitCliffordBraidData : CliffordBraidData PUnit where
  B _ := ⟨⟩
  squareTarget _ := ⟨⟩
  square_eq_target _ := rfl
  fourth_central_sign _ := rfl
  eighth_identity _ := rfl
  adjacent_artin _ := rfl
  far_commute _ _ _ := rfl

/-- Static `Z_N` parafermion phase algebra. -/
structure ParafermionSystem
    (N n : Nat) (K A : Type*) [CommRing K] [Ring A] [Algebra K A] where
  omega : K
  omega_pow : omega ^ N = 1
  omega_primitive : ∀ k : Nat, 0 < k → k < N → omega ^ k ≠ 1
  psi : Fin n → A
  psi_pow : ∀ i, psi i ^ N = 1
  comm_phase : ∀ i j : Fin n, i < j →
    psi i * psi j = algebraMap K A omega * (psi j * psi i)

/-- Trivial instance of ParafermionSystem on PUnit for N=1. -/
def punitParafermionSystem (n : Nat) : ParafermionSystem 1 n PUnit PUnit where
  omega := ⟨⟩
  omega_pow := rfl
  omega_primitive k hk1 hk2 := by linarith
  psi _ := ⟨⟩
  psi_pow _ := rfl
  comm_phase _ _ _ := rfl

/-- Extra Yang--Baxter-compatible braid data. Not automatic from parafermions. -/
structure ParafermionBraidData
    (N n : Nat) (K A : Type*) [CommRing K] [Ring A] [Algebra K A]
    (sys : ParafermionSystem N n K A) where
  R : Nat → A
  adjacent_artin : ∀ i, R i * R (i+1) * R i = R (i+1) * R i * R (i+1)
  far_commute : ∀ i j, i + 1 < j → R i * R j = R j * R i

/-- Trivial instance of ParafermionBraidData on PUnit. -/
def punitParafermionBraidData (n : Nat) : ParafermionBraidData 1 n PUnit PUnit (punitParafermionSystem n) where
  R _ := ⟨⟩
  adjacent_artin _ := rfl
  far_commute _ _ _ := rfl

end InfoGeometry.Algebra
