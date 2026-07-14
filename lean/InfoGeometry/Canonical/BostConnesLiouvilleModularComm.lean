/-
# Bost-Connes: Liouville-Modular Flow Commutation

This file formalizes a scalar commutation theorem: the Liouville grading
operator Γ, given by prime-factor parity `(-1)^Ω(n)`, commutes with the
modular-flow phase `σ_t` on the chosen arithmetic generators.
-/

import Mathlib
import InfoGeometry.Arithmetic.BostConnesSystem
import InfoGeometry.Canonical.BostConnesModularFlow
import InfoGeometry.Canonical.BostConnesKMS

noncomputable section

namespace BostConnesLiouvilleModularComm

open InfoGeometry.Arithmetic.BostConnesSystem
open InfoGeometry.Canonical.BostConnesModularFlow
open scoped BigOperators

universe u

variable {Op : Type u} [NormedRing Op] [NormedAlgebra ℂ Op] [StarRing Op]

/-!
## 1. The Liouville Function and Prime Factor Counting
-/

/-- The real-valued Liouville function on positive integers. -/
def liouvilleReal (n : ℕ+) : ℝ := (-1 : ℝ) ^ totalPrimeFactors n

/-- The real-valued Liouville function extended to all natural numbers. -/
def LiouvilleFunc (n : ℕ) : ℝ :=
  if h : n = 0 then 0
  else liouvilleReal ⟨n, Nat.pos_of_ne_zero h⟩

/-- Cast of liouvilleReal to complex is the complex liouville. -/
theorem coe_liouvilleReal (n : ℕ+) :
    (liouvilleReal n : ℂ) = liouville n := by
  dsimp [liouvilleReal, liouville]
  push_cast
  rfl

/-!
## 2. Modular Flow Phase Factors
-/

/-- The modular flow phase factor: χ_t(n) = n^{it} -/
def modularPhase (t : ℝ) (n : ℕ+) : ℂ :=
  Complex.exp (Complex.I * t * Real.log (n : ℝ))

/-- Modular phase is multiplicative: (nm)^{it} = n^{it} · m^{it} -/
theorem modularPhase_multiplicative (t : ℝ) (n m : ℕ+) :
    modularPhase t (n * m) = modularPhase t n * modularPhase t m := by
  dsimp [modularPhase]
  push_cast
  rw [Real.log_mul (by positivity) (by positivity)]
  push_cast
  rw [mul_add, Complex.exp_add]

/-- Modular phase at 1 is 1 -/
theorem modularPhase_one (t : ℝ) :
    modularPhase t 1 = 1 := by
  simp [modularPhase]

/-- |n^{it}| = 1 (phase factor lies on unit circle) -/
theorem modularPhase_norm (t : ℝ) (n : ℕ+) :
    ‖modularPhase t n‖ = 1 := by
  dsimp [modularPhase]
  have h1 : Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ) = ((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1]
  exact Complex.norm_exp_ofReal_mul_I (t * Real.log (n : ℝ))

/-!
## 3. The Commutation Theorem
-/

structure LiouvilleGrading (C : CuntzMultiplicativeIndexing Op) where
  Γ : Op →L[ℂ] Op
  action_on_generators : ∀ n : ℕ+,
    Γ (C.generator n) = ((liouville n : ℂ)) • C.generator n

/-- The Liouville grading commutes with the modular flow on generators. -/
theorem liouville_commutes_with_modular_flow
    (C : CuntzMultiplicativeIndexing Op)
    (F : ArithmeticModularFlow C)
    (L : LiouvilleGrading C)
    (t : ℝ) (n : ℕ+) :
    L.Γ (F.σ t (C.generator n)) = F.σ t (L.Γ (C.generator n)) := by
  rw [F.scaling t n, map_smul, L.action_on_generators n, map_smul, F.scaling t n]
  simp [smul_smul, mul_comm]

/-- Alternative formulation: Explicit computation of both sides -/
theorem liouville_modular_comm_explicit
    (C : CuntzMultiplicativeIndexing Op)
    (F : ArithmeticModularFlow C)
    (L : LiouvilleGrading C)
    (t : ℝ) (n : ℕ+) :
    L.Γ (F.σ t (C.generator n)) =
    (modularPhase t n * liouville n) • C.generator n := by
  rw [F.scaling t n, map_smul, L.action_on_generators n]
  simp [smul_smul, modularPhase]

/-- The reverse order gives the same result (commutativity) -/
theorem modular_liouville_comm_explicit
    (C : CuntzMultiplicativeIndexing Op)
    (F : ArithmeticModularFlow C)
    (L : LiouvilleGrading C)
    (t : ℝ) (n : ℕ+) :
    F.σ t (L.Γ (C.generator n)) =
    (modularPhase t n * liouville n) • C.generator n := by
  rw [L.action_on_generators n, map_smul, F.scaling t n]
  simp [smul_smul, mul_comm, modularPhase]

/-- Corollary: the two explicit scalar readbacks agree. -/
theorem commutation_corollary
    (C : CuntzMultiplicativeIndexing Op)
    (F : ArithmeticModularFlow C)
    (L : LiouvilleGrading C)
    (t : ℝ) (n : ℕ+) :
    L.Γ (F.σ t (C.generator n)) = F.σ t (L.Γ (C.generator n)) := by
  rw [liouville_modular_comm_explicit, modular_liouville_comm_explicit]

/-!
## 4. Witten Index and Flow Invariance
-/

/-- Partial Witten index sum (finite approximation). -/
def wittenIndexPartial (N : ℕ) (β : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, LiouvilleFunc n * (n : ℝ)^(-β)

/-- A `t = 0` readback for the finite Witten-index-style expression. -/
theorem witten_index_invariant_under_flow
    (C : CuntzMultiplicativeIndexing Op)
    (_F : ArithmeticModularFlow C)
    (_L : LiouvilleGrading C)
    (N : ℕ+) (β : ℝ) :
    ∑ n ∈ Finset.Icc 1 (N : ℕ),
      LiouvilleFunc n * Complex.re (modularPhase 0 (if h : n = 0 then 1 else ⟨n, Nat.pos_of_ne_zero h⟩)) * (n : ℝ)^(-β) =
    wittenIndexPartial N β * Complex.re (modularPhase 0 1) := by
  dsimp [wittenIndexPartial, modularPhase]
  simp

end BostConnesLiouvilleModularComm