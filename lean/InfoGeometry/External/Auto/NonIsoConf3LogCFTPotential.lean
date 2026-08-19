import Mathlib.Tactic
import InfoGeometry.External.Auto.NonIsoConf3DeRhamCooperad

/-!
# Non-isotropic Conf3 Log-CFT potential skeleton

A small theorem-honest finite Gibbs/log-potential layer.  It provides the
branch-diagnostic structures used by `NonIsoConf3LogPotentialDecision` without
claiming analytic CFT or KMS theorems.
-/

noncomputable section

namespace NonIsoConf3LogCFTPotential

open scoped BigOperators
open NonIsoConf3DeRhamCooperad

/-- Finite-state Gibbs/Log-CFT style package. -/
structure LogPotentialSystem (S : Type*) where
  [fintypeS : Fintype S]
  H : S → ℝ
  beta : ℝ
  nonempty : Nonempty S

attribute [instance] LogPotentialSystem.fintypeS

variable {S S₁ S₂ : Type*}

/-- Partition function `Z(β)`. -/
def partitionFunction (sys : LogPotentialSystem S) : ℝ := by
  letI : Fintype S := sys.fintypeS
  exact ∑ s : S, Real.exp (-sys.beta * sys.H s)

/-- The partition function is positive for nonempty finite systems. -/
lemma partitionFunction_pos (sys : LogPotentialSystem S) : 0 < partitionFunction sys := by
  letI : Fintype S := sys.fintypeS
  rcases sys.nonempty with ⟨s0⟩
  let f : S → ℝ := fun s => Real.exp (-sys.beta * sys.H s)
  have hpos : ∀ s : S, 0 < f s := fun s => Real.exp_pos _
  have hsum_pos : 0 < ∑ s : S, f s := by
    exact Finset.sum_pos' (s := Finset.univ) (fun s _ => le_of_lt (hpos s)) ⟨s0, by simp, hpos s0⟩
  simpa [partitionFunction, f] using hsum_pos

lemma partitionFunction_ne_zero (sys : LogPotentialSystem S) : partitionFunction sys ≠ 0 :=
  ne_of_gt (partitionFunction_pos sys)

/-- Log generating potential `G(β)=log Z(β)`. -/
def logGeneratingPotential (sys : LogPotentialSystem S) : ℝ :=
  Real.log (partitionFunction sys)

/-- Boltzmann free energy convention `F=-log Z / β`. -/
def boltzmannFreeEnergy (sys : LogPotentialSystem S) : ℝ :=
  -(1 / sys.beta) * logGeneratingPotential sys

/-- Boltzmann weight. -/
def boltzmannWeight (sys : LogPotentialSystem S) (s : S) : ℝ :=
  Real.exp (-sys.beta * sys.H s) / partitionFunction sys

/-- Finite modular Hamiltonian expression `K=βH+log Z`. -/
def modularHamiltonian (sys : LogPotentialSystem S) (s : S) : ℝ :=
  sys.beta * sys.H s + logGeneratingPotential sys

/-- Rényi potential `S_n=(1/(1-n)) log Tr ρ^n`. -/
def renyiPotential (sys : LogPotentialSystem S) (n : ℕ) : ℝ := by
  letI : Fintype S := sys.fintypeS
  exact (1 / (1 - (n : ℝ))) * Real.log (∑ s : S, (boltzmannWeight sys s) ^ n)

/-- Product-system bookkeeping.  The actual factorization theorem is represented
below as a conditional theorem, avoiding hidden analytic assumptions. -/
def productSystem (sys1 : LogPotentialSystem S₁) (sys2 : LogPotentialSystem S₂)
    (_hβ : sys1.beta = sys2.beta) : LogPotentialSystem (S₁ × S₂) where
  H := fun p => sys1.H p.1 + sys2.H p.2
  beta := sys1.beta
  fintypeS := by
    letI : Fintype S₁ := sys1.fintypeS
    letI : Fintype S₂ := sys2.fintypeS
    infer_instance
  nonempty := by
    rcases sys1.nonempty with ⟨s1⟩
    rcases sys2.nonempty with ⟨s2⟩
    exact ⟨(s1, s2)⟩

/-- Conditional factorization of the log-generating potential. -/
theorem logGenerating_additive_of_partition_mul
    (sys1 : LogPotentialSystem S₁) (sys2 : LogPotentialSystem S₂)
    (hβ : sys1.beta = sys2.beta)
    (hpart : partitionFunction (productSystem sys1 sys2 hβ) =
      partitionFunction sys1 * partitionFunction sys2) :
    logGeneratingPotential (productSystem sys1 sys2 hβ)
      = logGeneratingPotential sys1 + logGeneratingPotential sys2 := by
  unfold logGeneratingPotential
  rw [hpart]
  exact Real.log_mul (partitionFunction_ne_zero sys1) (partitionFunction_ne_zero sys2)

/-- Branch selector by logarithmic finite potential ordering. -/
def logPotentialBranchChoice (gProduct gOS : ℝ) : ModelChoice :=
  if gProduct > gOS then ModelChoice.productLeray else ModelChoice.osAlpha

theorem logPotentialBranchChoice_product (gProduct gOS : ℝ) (h : gProduct > gOS) :
    logPotentialBranchChoice gProduct gOS = ModelChoice.productLeray := by
  simp [logPotentialBranchChoice, h]

theorem logPotentialBranchChoice_osAlpha (gProduct gOS : ℝ) (h : ¬ gProduct > gOS) :
    logPotentialBranchChoice gProduct gOS = ModelChoice.osAlpha := by
  simp [logPotentialBranchChoice, h]

/-- Entropy-gap helper used by the algebraic diagnostic. -/
def entropyGapValue (entropyPotentialProduct entropyPotentialOS : ℝ) : ℝ :=
  entropyPotentialProduct - entropyPotentialOS

/-- Compact diagnostic tuple for algebraic branch choice. -/
abbrev EntropicBranchChoice := ℝ × ℝ

namespace EntropicBranchChoice

def entropyPotentialProduct (d : EntropicBranchChoice) : ℝ := d.1
def entropyPotentialOS (d : EntropicBranchChoice) : ℝ := d.2

def entropyGap (d : EntropicBranchChoice) : ℝ :=
  entropyGapValue (entropyPotentialProduct d) (entropyPotentialOS d)

@[simp] theorem entropyGapEq (d : EntropicBranchChoice) :
    entropyGap d = entropyGapValue (entropyPotentialProduct d) (entropyPotentialOS d) := rfl

def chosen (d : EntropicBranchChoice) : ModelChoice :=
  logPotentialBranchChoice (entropyPotentialProduct d) (entropyPotentialOS d)

@[simp] theorem chosen_eq (d : EntropicBranchChoice) :
    chosen d = logPotentialBranchChoice (entropyPotentialProduct d) (entropyPotentialOS d) := rfl

end EntropicBranchChoice

/-- Compatibility alias for existing call sites. -/
abbrev LogPotentialBranchDiagnostic := EntropicBranchChoice

def liftDiagnosticToChoice
    (d : LogPotentialBranchDiagnostic)
    (h : d.entropyPotentialProduct > d.entropyPotentialOS) :
    d.chosen = ModelChoice.productLeray := by
  rw [d.chosen_eq]
  exact logPotentialBranchChoice_product d.entropyPotentialProduct d.entropyPotentialOS h

/-- Direct entropy-gap criterion in the diagnostic channel. -/
theorem entropicChoiceFromGap (d : EntropicBranchChoice)
    (h : d.entropyGap > 0) :
    d.chosen = ModelChoice.productLeray := by
  have hEq : d.entropyGap = d.entropyPotentialProduct - d.entropyPotentialOS := by
    rfl
  have hgap : d.entropyPotentialProduct - d.entropyPotentialOS > 0 := by
    rw [← hEq]
    exact h
  exact liftDiagnosticToChoice d (by linarith [hgap])

theorem entropicChoiceFromNotGap (d : EntropicBranchChoice)
    (h : ¬ d.entropyGap > 0) :
    d.chosen = ModelChoice.osAlpha := by
  have hEq : d.entropyGap = d.entropyPotentialProduct - d.entropyPotentialOS := by
    rfl
  have hgap : ¬ d.entropyPotentialProduct > d.entropyPotentialOS := by
    linarith [h, hEq]
  rw [d.chosen_eq]
  simp [logPotentialBranchChoice, hgap]

end NonIsoConf3LogCFTPotential

end noncomputable section
