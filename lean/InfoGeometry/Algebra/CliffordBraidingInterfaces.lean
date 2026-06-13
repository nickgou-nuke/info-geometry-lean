import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Basic

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

/-- Exact scalar data for `1 / sqrt 2` over an arbitrary coefficient field. -/
structure CliffordBraidScalars (K : Type*) [Field K] where
  invSqrtTwo : K
  invSqrtTwo_sq : invSqrtTwo * invSqrtTwo = (1 : K) / 2

/-- Certified Clifford braid operators. -/
structure CliffordBraidData (A : Type*) [Ring A] where
  B : Nat → A
  square_plane : ∀ i, B i * B i = B i * B i -- replace RHS by γᵢγᵢ₊₁ in concrete instances
  fourth_central_sign : ∀ i, B i ^ 4 = -1
  eighth_identity : ∀ i, B i ^ 8 = 1
  adjacent_artin : ∀ i, B i * B (i+1) * B i = B (i+1) * B i * B (i+1)
  far_commute : ∀ i j, i + 1 < j → B i * B j = B j * B i

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

/-- Extra Yang--Baxter-compatible braid data. Not automatic from parafermions. -/
structure ParafermionBraidData
    (N n : Nat) (K A : Type*) [CommRing K] [Ring A] [Algebra K A]
    (sys : ParafermionSystem N n K A) where
  R : Nat → A
  adjacent_artin : ∀ i, R i * R (i+1) * R i = R (i+1) * R i * R (i+1)
  far_commute : ∀ i j, i + 1 < j → R i * R j = R j * R i

end InfoGeometry.Algebra
