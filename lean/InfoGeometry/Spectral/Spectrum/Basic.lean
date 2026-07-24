import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import InfoGeometry.Canonical.SplitCliffordDirectLimit

/-!
# Finite Spectral Readouts for the Split-Clifford Tower

This file provides a kernel-checked finite spectral API over the repository's
existing split-Clifford direct-limit owner.

It does not claim a full stable homotopy spectrum, a spectrification functor,
or an equivalence with mathlib's triangulated `SpectralObject`. The closed
facts here are finite clock/readout theorems and direct-limit representative
transport facts.
-/

noncomputable section

namespace InfoGeometry.Spectral.Spectrum.Basic

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-! ## Minimal prespectrum-shaped bookkeeping -/

/-- A concrete prespectrum-shaped sequence with one-step structure maps. -/
structure Prespectrum where
  space : ℕ → Type*
  step : ∀ n, space n → space (n + 1)

/-- Current finite spectral-port spectrum object. -/
abbrev Spectrum := Prespectrum

namespace Prespectrum

/-- Build a prespectrum-shaped sequence from explicit stage data. -/
def ofFun (space : ℕ → Type*) (step : ∀ n, space n → space (n + 1)) :
    Prespectrum where
  space := space
  step := step

@[simp]
theorem ofFun_space (space : ℕ → Type*) (step : ∀ n, space n → space (n + 1))
    (n : ℕ) :
    (ofFun space step).space n = space n :=
  rfl

@[simp]
theorem ofFun_step (space : ℕ → Type*) (step : ∀ n, space n → space (n + 1))
    (n : ℕ) (x : space n) :
    (ofFun space step).step n x = step n x :=
  rfl

end Prespectrum

/-- The split-Clifford tower viewed as a prespectrum-shaped sequence. -/
def SplitCliffordPrespectrum : Prespectrum :=
  Prespectrum.ofFun
    (fun n => SplitClNNAlg n)
    (fun n x => splitCliffordStep n x)

@[simp]
theorem SplitCliffordPrespectrum_space (n : ℕ) :
    SplitCliffordPrespectrum.space n = SplitClNNAlg n :=
  rfl

@[simp]
theorem SplitCliffordPrespectrum_step (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordPrespectrum.step n x = splitCliffordStep n x :=
  rfl

/-! ## Bott clock and finite Dirac readout -/

/-- The eight-step Bott clock sampled at stage `n`. -/
def bottClockStage (n : ℕ) : ℕ := n + 8

@[simp]
theorem bottClockStage_sub_self (n : ℕ) :
    bottClockStage n - n = 8 := by
  simp [bottClockStage]

theorem bottClockStage_pos (n : ℕ) :
    n < bottClockStage n := by
  simp [bottClockStage]

/-- A two-eigenvalue finite Dirac readout. -/
def diracOperator (m : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m, 0; 0, -m]

/-- The finite Dirac readout squares to the scalar mass shell. -/
theorem diracOperator_sq (m : ℝ) :
    diracOperator m * diracOperator m = (m ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diracOperator, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The spectrum readout attached to the finite Dirac operator. -/
def diracSpectrum (m : ℝ) : Finset ℝ :=
  {m, -m}

@[simp]
theorem mem_diracSpectrum_iff (m lam : ℝ) :
    lam ∈ diracSpectrum m ↔ lam = m ∨ lam = -m := by
  by_cases h : m = 0
  · subst h
    simp [diracSpectrum]
  · simp [diracSpectrum]

/-- The finite spectral readout has one point at zero mass and two otherwise. -/
theorem diracSpectrum_card (m : ℝ) :
    (diracSpectrum m).card = if m = 0 then 1 else 2 := by
  by_cases h : m = 0
  · subst h
    simp [diracSpectrum]
  · have hne : m ≠ -m := by
      intro hm
      have : m = 0 := by linarith
      exact h this
    simp [diracSpectrum, h, hne]

/-! ## Stable split-Clifford direct-limit readouts -/

/--
Every split-Clifford direct-limit element has representatives arbitrarily far
out in the tower.
-/
theorem stableHomotopyClifford
    (z : SplitCliffordInfinity) (N : ℕ) :
    ∃ n ≥ N, ∃ x : SplitClNNAlg n,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z :=
  splitCliffordInfinity_unbounded_representatives z N

/-- Every split-Clifford direct-limit element has at least one representative. -/
theorem stableHomotopyClifford_nonempty
    (z : SplitCliffordInfinity) :
    ∃ n, ∃ x : SplitClNNAlg n,
      DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x = z := by
  rcases stableHomotopyClifford z 0 with ⟨n, _hn, x, hx⟩
  exact ⟨n, x, hx⟩

/--
The same representative can be read at the eight-step Bott clock stage without
changing the direct-limit element.
-/
theorem stableHomotopyClifford_period
    (n : ℕ) (x : SplitClNNAlg n) :
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) (bottClockStage n)
        (splitCliffordMap n (bottClockStage n) (Nat.le_add_right n 8) x)
      =
    DirectLimit.Module.of ℝ ℕ SplitClNNAlg
        (fun m n h => splitCliffordMap m n h) n x := by
  simpa [bottClockStage] using
    (DirectLimit.Module.of_f
      (f := fun m n h => splitCliffordMap m n h)
      (i := n) (j := n + 8) (hij := Nat.le_add_right n 8) (x := x))

end InfoGeometry.Spectral.Spectrum.Basic
