import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HilbertSchmidtMatrixPairing

open Matrix

namespace InfoGeometry.Dynamics.OperatorHodgeHelmholtz

/-!
# Finite operator Hodge--Helmholtz readout

This file is the finite `2 x 2` readout layer for the generic Hodge--Dirac
owners.  It proves Hilbert--Schmidt orthogonality of the radial and rotational
channels and identifies their joint kernel.  It does not identify a Hodge
Laplacian with a modular surprisal operator; that identification is exposed as
an explicit bridge structure below.
-/

noncomputable section

def gamma : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

def kPhase : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

def trace2 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := A 0 0 + A 1 1

abbrev hilbertSchmidt (A B : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  HilbertSchmidtMatrix.hilbertSchmidtPairing A B

def surprisal (κ a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  κ • 1 + a • gamma

def flowIrr (κ a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -surprisal κ a

def flowRot (κ a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  -(kPhase * surprisal κ a)

lemma surprisal_val (κ a : ℝ) :
    surprisal κ a = !![κ + a, 0; 0, κ - a] := by
  ext i j
  unfold surprisal gamma
  fin_cases i <;> fin_cases j <;> simp
  all_goals ring

lemma flowIrr_val (κ a : ℝ) :
    flowIrr κ a = !![-(κ + a), 0; 0, -(κ - a)] := by
  rw [flowIrr, surprisal_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma flowRot_val (κ a : ℝ) :
    flowRot κ a = !![0, κ - a; -(κ + a), 0] := by
  unfold flowRot kPhase
  rw [surprisal_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem trace2_surprisal (κ a : ℝ) :
    trace2 (surprisal κ a) = 2 * κ := by
  rw [surprisal_val]
  unfold trace2
  simp
  ring

theorem flow_orthogonality (κ a : ℝ) :
    hilbertSchmidt (flowIrr κ a) (flowRot κ a) = 0 := by
  change HilbertSchmidtMatrix.hilbertSchmidtPairing
    (flowIrr κ a) (flowRot κ a) = 0
  rw [flowIrr_val, flowRot_val,
    HilbertSchmidtMatrix.hilbertSchmidtPairing_eq_sum]
  simp

theorem joint_flow_zero_iff_undeformed (κ a : ℝ) :
    (flowIrr κ a = 0 ∧ flowRot κ a = 0) ↔ (κ = 0 ∧ a = 0) := by
  constructor
  · rintro ⟨hIrr, _⟩
    rw [flowIrr_val] at hIrr
    have h₁ : -(κ + a) = 0 := by
      simpa using congr_fun (congr_fun hIrr 0) 0
    have h₂ : -(κ - a) = 0 := by
      simpa using congr_fun (congr_fun hIrr 1) 1
    constructor <;> linarith
  · rintro ⟨hκ, ha⟩
    subst hκ
    subst ha
    constructor
    · rw [flowIrr_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · rw [flowRot_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

end
end InfoGeometry.Dynamics.OperatorHodgeHelmholtz
