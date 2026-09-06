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
def MajoranaSystemLaws {n : Nat} {A : Type*} [Ring A]
    (S : MajoranaSystem n A) : Prop :=
  (∀ i, S.gamma i * S.gamma i = 1) ∧
  (∀ i j, i ≠ j → S.gamma i * S.gamma j = -(S.gamma j * S.gamma i))

/-- Exact scalar data for `1 / sqrt 2` over an arbitrary coefficient field. -/
structure CliffordBraidScalars (K : Type*) [Field K] where
  invSqrtTwo : K
def CliffordBraidScalarsLaws {K : Type*} [Field K]
    (S : CliffordBraidScalars K) : Prop :=
  S.invSqrtTwo * S.invSqrtTwo = (1 : K) / 2

/-- Real instance of CliffordBraidScalars. -/
noncomputable def realCliffordBraidScalars : CliffordBraidScalars ℝ where
  invSqrtTwo := (Real.sqrt 2)⁻¹

theorem realCliffordBraidScalars_laws :
    CliffordBraidScalarsLaws realCliffordBraidScalars := by
  change (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 : ℝ) / 2
  rw [← mul_inv]
  rw [Real.mul_self_sqrt (by norm_num)]
  exact inv_eq_one_div (2 : ℝ)

/-- Certified Clifford braid operators. -/
structure CliffordBraidData (A : Type*) [Ring A] where
  B : Nat → A
  squareTarget : Nat → A
def CliffordBraidDataLaws {A : Type*} [Ring A]
    (S : CliffordBraidData A) : Prop :=
  (∀ i, S.B i * S.B i = S.squareTarget i) ∧
  (∀ i, S.B i ^ 4 = -1) ∧
  (∀ i, S.B i ^ 8 = 1) ∧
  (∀ i, S.B i * S.B (i + 1) * S.B i =
    S.B (i + 1) * S.B i * S.B (i + 1)) ∧
  (∀ i j, i + 1 < j → S.B i * S.B j = S.B j * S.B i)

/-- Static `Z_N` parafermion phase algebra. -/
structure ParafermionSystem
    (N n : Nat) (K A : Type*) [CommRing K] [Ring A] [Algebra K A] where
  omega : K
  psi : Fin n → A
def ParafermionSystemLaws {N n : Nat} {K A : Type*}
    [CommRing K] [Ring A] [Algebra K A]
    (S : ParafermionSystem N n K A) : Prop :=
  S.omega ^ N = 1 ∧
  (∀ k : Nat, 0 < k → k < N → S.omega ^ k ≠ 1) ∧
  (∀ i, S.psi i ^ N = 1) ∧
  (∀ i j : Fin n, i < j →
    S.psi i * S.psi j = algebraMap K A S.omega * (S.psi j * S.psi i))

/-- Extra Yang--Baxter-compatible braid data. Not automatic from parafermions. -/
structure ParafermionBraidData
    (N n : Nat) (K A : Type*) [CommRing K] [Ring A] [Algebra K A]
    (sys : ParafermionSystem N n K A) where
  R : Nat → A
def ParafermionBraidDataLaws {N n : Nat} {K A : Type*}
    [CommRing K] [Ring A] [Algebra K A]
    {sys : ParafermionSystem N n K A}
    (S : ParafermionBraidData N n K A sys) : Prop :=
  (∀ i, S.R i * S.R (i + 1) * S.R i =
    S.R (i + 1) * S.R i * S.R (i + 1)) ∧
  (∀ i j, i + 1 < j → S.R i * S.R j = S.R j * S.R i)

end InfoGeometry.Algebra
