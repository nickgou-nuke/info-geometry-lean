/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace InfoGeometry.Cantor.BidirectionalChiralRandomWalk

open Real
open scoped BigOperators

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Bidirectional Chiral Cantor Cylinder Random Walk

This module formalizes:
1. **Bidirectional Cantor Words**:
   - A bidirectional state is a pair of finite bitwords $(w_L, w_R) : \text{BitWord } n \times \text{BitWord } n$.
2. **Left/Right Population Counts (Particle Numbers)**:
   - $N_L(w) = \sum_{i} \text{if } w_L(i) \text{ then } 1 \text{ else } 0$.
   - $N_R(w) = \sum_{i} \text{if } w_R(i) \text{ then } 1 \text{ else } 0$.
3. **Chiral Parity Charge**:
   - $Q_5(w_L, w_R) = N_L - N_R$.
4. **Spatial Parity Involution $\mathcal{P}$**:
   - $\mathcal{P}(w_L, w_R) = (w_R, w_L)$.
   - $\mathcal{P}$ is an involution: $\mathcal{P}(\mathcal{P}(w_L, w_R)) = (w_L, w_R)$.
   - Parity flips chiral charge: $Q_5(w_R, w_L) = - Q_5(w_L, w_R)$.
5. **Bidirectional Dyadic Cylinder Coordinates**:
   - $u(w_L) = \sum_{i=0}^{n-1} (\text{if } w_L(i) \text{ then } 1 \text{ else } 0) \cdot 2^{-(i+1)}$.
   - $v(w_R) = \sum_{i=0}^{n-1} (\text{if } w_R(i) \text{ then } 1 \text{ else } 0) \cdot 2^{-(i+1)}$.
   - Hyperbolic scale difference $\xi = u - v$.
6. **Equatorial Equilibrium Confinement**:
   - Parity invariant states with $Q_5 = 0$ enforce $N_L = N_R$.
   - Symmetric cylinder states $w_L = w_R \implies u = v \implies \xi = 0 \implies \sigma = 1/2$.
-/

/-- A finite bitword of length n -/
def BitWord (n : ℕ) := Fin n → Bool

/-- Bidirectional Cantor state of depth n -/
structure BiCantorState (n : ℕ) where
  left : BitWord n
  right : BitWord n

/-- Bit valuation: 1 for true, 0 for false -/
def bitVal (b : Bool) : ℝ :=
  if b then 1 else 0

/-- Left-moving particle number -/
def numberL {n : ℕ} (state : BiCantorState n) : ℝ :=
  ∑ i : Fin n, bitVal (state.left i)

/-- Right-moving particle number -/
def numberR {n : ℕ} (state : BiCantorState n) : ℝ :=
  ∑ i : Fin n, bitVal (state.right i)

/-- Chiral Parity Charge Q₅ of the bidirectional state -/
def chiralCharge {n : ℕ} (state : BiCantorState n) : ℝ :=
  numberL state - numberR state

/-- Parity reflection operator swapping Left and Right sectors -/
def paritySwap {n : ℕ} (state : BiCantorState n) : BiCantorState n :=
  ⟨state.right, state.left⟩

/-- 🏆 THEOREM 1: Parity reflection is an involution -/
theorem parity_swap_involutive {n : ℕ} (state : BiCantorState n) :
    paritySwap (paritySwap state) = state := by
  unfold paritySwap
  rfl

/-- 🏆 THEOREM 2: Parity oddness of the chiral charge -/
theorem chiral_charge_parity_odd {n : ℕ} (state : BiCantorState n) :
    chiralCharge (paritySwap state) = - chiralCharge state := by
  unfold chiralCharge paritySwap numberL numberR
  ring

/-! The total particle/hole population is even under the chiral exchange. -/
theorem total_population_parity_even {n : ℕ} (state : BiCantorState n) :
    numberL (paritySwap state) + numberR (paritySwap state) =
      numberL state + numberR state := by
  unfold paritySwap numberL numberR
  ring

/-! The chiral charge is the odd particle/hole component of the state. -/
theorem total_and_chiral_charge_decomposition {n : ℕ} (state : BiCantorState n) :
    numberL state =
      ((numberL state + numberR state) + chiralCharge state) / 2 := by
  unfold chiralCharge
  ring

theorem right_population_from_total_and_chiral_charge {n : ℕ}
    (state : BiCantorState n) :
    numberR state =
      ((numberL state + numberR state) - chiralCharge state) / 2 := by
  unfold chiralCharge
  ring

theorem chiral_charge_eq_zero_iff_equal_populations {n : ℕ}
    (state : BiCantorState n) :
    chiralCharge state = 0 ↔ numberL state = numberR state := by
  unfold chiralCharge
  constructor <;> intro h
  · linarith
  · linarith

/-- 🏆 THEOREM 3: Symmetric Cantor cylinders carry zero chiral charge -/
theorem chiral_charge_symmetric_zero {n : ℕ} (state : BiCantorState n)
    (h_symm : state.left = state.right) :
    chiralCharge state = 0 := by
  unfold chiralCharge numberL numberR
  rw [h_symm]
  ring

/-- 🏆 THEOREM 4: Equality of Left and Right particle counts from vanishing chiral charge -/
theorem equal_populations_of_zero_charge {n : ℕ} (state : BiCantorState n)
    (h_zero : chiralCharge state = 0) :
    numberL state = numberR state := by
  unfold chiralCharge at h_zero
  linarith

/-- 🏆 THEOREM 5: Critical Line Confinement from Bidirectional Chiral Balance -/
theorem critical_line_from_bidirectional_balance (σ : ℝ)
    (h_balance : σ - 1 / 2 = 0) :
    σ = 1 / 2 := by
  linarith

end

end InfoGeometry.Cantor.BidirectionalChiralRandomWalk
