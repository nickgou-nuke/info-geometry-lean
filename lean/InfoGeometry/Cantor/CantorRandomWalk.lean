import InfoGeometry.Dynamics.KanDecomposition
import Mathlib.Tactic

noncomputable section

/-!
# CantorRandomWalk

Finite algebraic Cantor/random-walk shadow for the parabolic `N` lane.

The Cantor carrier is the binary sequence space `ℕ → Bool`. This file proves
the concrete bit-flip laws and connects a local mode-step matrix to the already
owned parabolic `componentN` power law.

It does not construct a probability measure, a stochastic process, a CAR
algebra, or a metric-space instance for Cantor space.
-/

namespace InfoGeometry.Cantor.CantorRandomWalk

open Matrix
open InfoGeometry.Dynamics.KanDecomposition

/-- Cantor binary sequence space, read as infinitely many occupation bits. -/
abbrev CantorWord : Type :=
  ℕ → Bool

/-- Dirac-sea reference word with every mode unoccupied. -/
def diracSea : CantorWord :=
  fun _ => false

/-- Predicate saying two Cantor words differ at coordinate `n`. -/
def DifferAt (x y : CantorWord) (n : ℕ) : Prop :=
  x n ≠ y n

/-- A singleton bit flip at coordinate `i`. -/
def flipBit (i : ℕ) (x : CantorWord) : CantorWord :=
  fun j => if j = i then !(x j) else x j

/-- The flipped coordinate is negated. -/
@[simp] theorem flipBit_self (i : ℕ) (x : CantorWord) :
    flipBit i x i = !(x i) := by
  simp [flipBit]

/-- Other coordinates are unchanged by a singleton bit flip. -/
theorem flipBit_other {i j : ℕ} (hji : j ≠ i) (x : CantorWord) :
    flipBit i x j = x j := by
  simp [flipBit, hji]

/-- Flipping the same coordinate twice is the identity. -/
@[simp] theorem flipBit_involutive (i : ℕ) (x : CantorWord) :
    flipBit i (flipBit i x) = x := by
  ext j
  by_cases hji : j = i <;> simp [flipBit, hji]

/-- Flips at distinct coordinates commute. -/
theorem flipBit_commute_of_ne {i j : ℕ} (hij : i ≠ j) (x : CantorWord) :
    flipBit i (flipBit j x) = flipBit j (flipBit i x) := by
  ext k
  by_cases hki : k = i
  · have hkj : k ≠ j := by
      intro h
      exact hij (hki ▸ h)
    simp [flipBit, hki, hkj, hij, Ne.symm hij]
  · by_cases hkj : k = j
    · simp [flipBit, hki, hkj, hij, Ne.symm hij]
    · simp [flipBit, hki, hkj, hij, Ne.symm hij]

/-- A singleton bit flip always changes the word. -/
theorem flipBit_ne_self (i : ℕ) (x : CantorWord) :
    flipBit i x ≠ x := by
  intro h
  have hi := congrFun h i
  simp [flipBit] at hi

/-- If two Cantor words are unequal, they differ at some coordinate. -/
theorem exists_differAt_of_ne {x y : CantorWord} (hxy : x ≠ y) :
    ∃ n : ℕ, DifferAt x y n := by
  by_contra hnone
  apply hxy
  funext n
  by_contra hd
  exact hnone ⟨n, hd⟩

/--
First coordinate at which two unequal Cantor words differ.

This is the discrete depth readout behind the usual Cantor ultrametric. The
file only uses the depth, not a metric-space instance.
-/
def firstDifference (x y : CantorWord) (hxy : x ≠ y) : ℕ :=
  by
    classical
    exact Nat.find (exists_differAt_of_ne hxy)

/-- The first-difference coordinate really differs. -/
theorem firstDifference_spec (x y : CantorWord) (hxy : x ≠ y) :
    DifferAt x y (firstDifference x y hxy) := by
  classical
  exact Nat.find_spec (exists_differAt_of_ne hxy)

/-- Before the first-difference depth, the two Cantor words agree. -/
theorem agree_before_firstDifference
    (x y : CantorWord) (hxy : x ≠ y) {k : ℕ}
    (hk : k < firstDifference x y hxy) :
    x k = y k := by
  classical
  by_contra hd
  have hle : firstDifference x y hxy ≤ k :=
    Nat.find_min' (exists_differAt_of_ne hxy) hd
  exact (not_le_of_gt hk) hle

/-- Local parabolic matrix step attached to one Cantor mode. -/
def localQuantumFlipStep (_i : ℕ) (δ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  componentN δ

/-- Local mode steps are exactly the KAN parabolic `N` gate. -/
theorem localQuantumFlipStep_eq_componentN (i : ℕ) (δ : ℂ) :
    localQuantumFlipStep i δ = componentN δ := rfl

/--
Repeated local parabolic perturbations accumulate linearly in the shear
parameter. This is a deterministic matrix law, not a probabilistic random-walk
limit theorem.
-/
theorem cantor_noise_accumulation (i : ℕ) (δ : ℂ) (n : ℕ) :
    (localQuantumFlipStep i δ) ^ n = localQuantumFlipStep i ((n : ℂ) * δ) := by
  simpa [localQuantumFlipStep] using componentN_pow δ n

/-- The accumulated local mode step has the explicit unipotent coordinate form. -/
theorem cantor_noise_accumulation_matrix (i : ℕ) (δ : ℂ) (n : ℕ) :
    (localQuantumFlipStep i δ) ^ n =
      !![1, (n : ℂ) * δ; 0, 1] := by
  rw [cantor_noise_accumulation]
  exact componentN_eq ((n : ℂ) * δ)

end InfoGeometry.Cantor.CantorRandomWalk
