import Mathlib
import InfoGeometry.Canonical.SplitCliffordDirectLimit

noncomputable section

/-!
# Finite split-Clifford spectral readouts

This file deliberately avoids claiming a port of HoTT spectra or a
spectrification theorem.  It exposes the finite split-Clifford tower as a
small prespectrum-style API and records the elementary readouts that are
available from the existing kernel-checked split-Clifford direct-limit lane.
-/

namespace InfoGeometry.Spectral.Spectrum.Basic

open InfoGeometry.Canonical.SplitCliffordDirectLimit
open InfoGeometry.Canonical.SplitCliffordTensorBridge

/-- A minimal one-step prespectrum-style carrier. -/
structure Prespectrum where
  /-- Stage carrier. -/
  space : ℕ → Type
  /-- One-step structure map. -/
  step : ∀ n, space n → space (n + 1)

namespace Prespectrum

/-- Construct a prespectrum from a stage family and one-step maps. -/
def ofFun (X : ℕ → Type) (f : ∀ n, X n → X (n + 1)) : Prespectrum :=
  ⟨X, f⟩

@[simp]
theorem ofFun_space (X : ℕ → Type) (f : ∀ n, X n → X (n + 1)) :
    (Prespectrum.ofFun X f).space = X :=
  rfl

@[simp]
theorem ofFun_step (X : ℕ → Type) (f : ∀ n, X n → X (n + 1)) :
    (Prespectrum.ofFun X f).step = f :=
  rfl

end Prespectrum

/-- The existing split `Cl(n,n)` tower as a finite prespectrum-style object. -/
def SplitCliffordPrespectrum : Prespectrum :=
  Prespectrum.ofFun SplitClNNAlg (fun n x => splitCliffordStep n x)

@[simp]
theorem SplitCliffordPrespectrum_space (n : ℕ) :
    SplitCliffordPrespectrum.space n = SplitClNNAlg n :=
  rfl

@[simp]
theorem SplitCliffordPrespectrum_step (n : ℕ) (x : SplitClNNAlg n) :
    SplitCliffordPrespectrum.step n x = splitCliffordStep n x :=
  rfl

/-- The Bott clock stage eight steps after `n`. -/
def bottClockStage (n : ℕ) : ℕ :=
  n + 8

@[simp]
theorem bottClockStage_sub_self (n : ℕ) :
    bottClockStage n - n = 8 := by
  simp [bottClockStage]

theorem bottClockStage_pos (n : ℕ) :
    n < bottClockStage n := by
  simp [bottClockStage]

/-- The zero finite Dirac readout at stage `n`. -/
def diracOperator (n : ℕ) : SplitClNNAlg n :=
  0

@[simp]
theorem diracOperator_sq (n : ℕ) :
    diracOperator n * diracOperator n = 0 := by
  simp [diracOperator]

/-- Finite spectral readout for the zero Dirac operator. -/
def diracSpectrum (_n : ℕ) : Multiset ℝ :=
  {0}

@[simp]
theorem mem_diracSpectrum_iff (n : ℕ) (lam : ℝ) :
    lam ∈ diracSpectrum n ↔ lam = 0 := by
  simp [diracSpectrum]

@[simp]
theorem diracSpectrum_card (n : ℕ) :
    (diracSpectrum n).card = 1 := by
  simp [diracSpectrum]

/-- A finite 8-periodic stable-homotopy readout used as a clock index. -/
def stableHomotopyClifford (k : ℕ) : Type :=
  Fin ((k % 8) + 1)

theorem stableHomotopyClifford_nonempty (k : ℕ) :
    Nonempty (stableHomotopyClifford k) :=
  ⟨⟨0, Nat.succ_pos (k % 8)⟩⟩

@[simp]
theorem stableHomotopyClifford_period (k : ℕ) :
    stableHomotopyClifford (k + 8) = stableHomotopyClifford k := by
  unfold stableHomotopyClifford
  rw [Nat.add_mod_right]

end InfoGeometry.Spectral.Spectrum.Basic
