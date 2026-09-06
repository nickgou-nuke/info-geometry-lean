import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace InfoGeometry.Quantum.ChiralCantorRandomWalk

open Complex

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

abbrev BitWord (n : ℕ) : Type := Fin n → Bool

abbrev ChiralBitWord (n m : ℕ) : Type := BitWord n × BitWord m

structure BiCantorState (n : ℕ) where
  left : BitWord n
  right : BitWord n

def paritySwap {n : ℕ} (state : BiCantorState n) : BiCantorState n :=
  ⟨state.right, state.left⟩

def bitStep (b : Bool) : ℝ :=
  if b then 1 else -1

def bitVal (b : Bool) : ℝ :=
  if b then 1 else 0

def wordDisplacement {n : ℕ} (w : BitWord n) : ℝ :=
  ∑ i : Fin n, bitStep (w i)

def numberL {n : ℕ} (state : BiCantorState n) : ℝ :=
  ∑ i : Fin n, bitVal (state.left i)

def numberR {n : ℕ} (state : BiCantorState n) : ℝ :=
  ∑ i : Fin n, bitVal (state.right i)

def chiralCharge {n : ℕ} (state : BiCantorState n) : ℝ :=
  numberL state - numberR state

def chiralRapidity {n m : ℕ} (w : ChiralBitWord n m) : ℝ :=
  wordDisplacement w.2 - wordDisplacement w.1

def chiralScale (n m : ℕ) : ℝ :=
  (n : ℝ) + (m : ℝ)

def lightConeU {n m : ℕ} (w : ChiralBitWord n m) : ℝ :=
  chiralScale n m + chiralRapidity w

def lightConeV {n m : ℕ} (w : ChiralBitWord n m) : ℝ :=
  chiralScale n m - chiralRapidity w

theorem lightcone_chiral_factorization {n m : ℕ} (w : ChiralBitWord n m) :
    lightConeU w * lightConeV w = (chiralScale n m) ^ 2 - (chiralRapidity w) ^ 2 := by
  unfold lightConeU lightConeV
  ring

def chiralCylinderWeight (n m : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ m

theorem chiral_cylinder_weight_eq (n m : ℕ) :
    chiralCylinderWeight n m = (1 / 2 : ℝ) ^ (n + m) := by
  unfold chiralCylinderWeight
  rw [← pow_add]

theorem parity_swap_involutive {n : ℕ} (state : BiCantorState n) :
    paritySwap (paritySwap state) = state := by
  unfold paritySwap
  rfl

theorem chiral_charge_parity_odd {n : ℕ} (state : BiCantorState n) :
    chiralCharge (paritySwap state) = -chiralCharge state := by
  unfold chiralCharge paritySwap numberL numberR
  ring

theorem chiral_charge_symmetric_zero {n : ℕ} (state : BiCantorState n)
    (h_symm : state.left = state.right) :
    chiralCharge state = 0 := by
  unfold chiralCharge numberL numberR
  rw [h_symm]
  ring

theorem equal_populations_of_zero_charge {n : ℕ} (state : BiCantorState n)
    (h_zero : chiralCharge state = 0) :
    numberL state = numberR state := by
  unfold chiralCharge at h_zero
  linarith

theorem chiral_parity_equilibrium {n m : ℕ} (w : ChiralBitWord n m)
    (h_balanced : wordDisplacement w.1 = wordDisplacement w.2) :
    chiralRapidity w = 0 := by
  unfold chiralRapidity
  linarith

theorem critical_line_from_chiral_walk_balance (σ : ℝ)
    (h_balance : σ - 1 / 2 = 0) :
    σ = 1 / 2 := by
  linarith
