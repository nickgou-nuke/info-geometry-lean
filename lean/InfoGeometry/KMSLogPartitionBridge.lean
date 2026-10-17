/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.KMSLogPartitionBridge

variable {ι : Type*} [Fintype ι] {β : ℝ} {E : ι → ℝ}

def PartitionZ (β : ℝ) (E : ι → ℝ) : ℝ := ∑ i : ι, Real.exp (-β * E i)
def LogPartitionPhi (β : ℝ) (E : ι → ℝ) : ℝ := Real.log (PartitionZ β E)
def GibbsWeight (β : ℝ) (E : ι → ℝ) (i : ι) : ℝ := Real.exp (-β * E i)
def GibbsState (β : ℝ) (E : ι → ℝ) (i : ι) : ℝ := GibbsWeight β E i / PartitionZ β E

theorem exp_logPartitionPhi_eq_PartitionZ (β : ℝ) (E : ι → ℝ) (hZ : 0 < PartitionZ β E) :
    Real.exp (LogPartitionPhi β E) = PartitionZ β E := by
  rw [LogPartitionPhi, Real.exp_log hZ]

def ModularHamiltonian (β : ℝ) (E : ι → ℝ) (i : ι) : ℝ := β * E i + LogPartitionPhi β E

def CentralPhase (s : ℝ) (β : ℝ) (E : ι → ℝ) : ℂ :=
  Complex.exp (-Complex.I * s * (LogPartitionPhi β E : ℂ))

theorem centralPhase_selfInv (s : ℝ) (β : ℝ) (E : ι → ℝ) :
    CentralPhase s β E * (CentralPhase (-s) β E) = 1 := by
  unfold CentralPhase; rw [mul_comm, ← Complex.exp_add]; simp

def RelativeLogPartitionGap (βA βB : ℝ) (EA EB : ι → ℝ) : ℝ :=
  LogPartitionPhi βB EB - LogPartitionPhi βA EA

def RelativeCocyclePhase (s : ℝ) (βA βB : ℝ) (EA EB : ι → ℝ) : ℂ :=
  Complex.exp (Complex.I * s * (RelativeLogPartitionGap βA βB EA EB : ℂ))

def KMSStripPhase (s τ : ℝ) (β : ℝ) (E : ι → ℝ) : ℂ :=
  Complex.exp (-Complex.I * (s - τ * Complex.I) * (LogPartitionPhi β E : ℂ))

def RadialDilatation (τ : ℝ) (β : ℝ) (E : ι → ℝ) (hZ : 0 < PartitionZ β E) : ℝ :=
  (PartitionZ β E) ^ (-τ)

end InfoGeometry.KMSLogPartitionBridge

end
