import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.KleinFourAnomalyCancellation

open Complex

variable (H : Type*) [AddCommGroup H] [Module ℂ H]

/-- V₄ as the additive square `Fin 2 × Fin 2`. -/
def V4 : Type := Fin 2 × Fin 2

def V4Mul (g h : V4) : V4 := (g.1 + h.1, g.2 + h.2)

def e_id : V4 := (0, 0)
def eJ : V4 := (1, 0)
def eε : V4 := (0, 1)
def eJE : V4 := (1, 1)

/-- Linear representation data for the two V₄ generators on `H`. -/
structure KleinFourData (H : Type*) [AddCommGroup H] [Module ℂ H] where
  J : Module.End ℂ H
  ε : Module.End ℂ H
  hJ_involution : J * J = 1
  hε_involution : ε * ε = 1
  hComm : J * ε = ε * J
  δK : Module.End ℂ H
  h_crosscap : (ε * δK) * ε = -δK
  h_automorphism : ε * δK = δK * ε

/-- Action of V₄ elements via the two commuting involutions. -/
def kleinAction (A : KleinFourData H) : V4 → Module.End ℂ H
  | (0, 0) => 1
  | (1, 0) => A.J
  | (0, 1) => A.ε
  | (1, 1) => A.J * A.ε

@[simp] lemma kleinAction_id (A : KleinFourData H) : kleinAction (H := H) A (0, 0) = 1 := rfl
@[simp] lemma kleinAction_J (A : KleinFourData H) : kleinAction (H := H) A (1, 0) = A.J := rfl
@[simp] lemma kleinAction_ε (A : KleinFourData H) : kleinAction (H := H) A (0, 1) = A.ε := rfl
@[simp] lemma kleinAction_Jε (A : KleinFourData H) : kleinAction (H := H) A (1, 1) = A.J * A.ε := rfl

/-- V₄ data are involutive on generators and commute. -/
theorem klein_four_relations (A : KleinFourData H) :
    kleinAction (H := H) A eJ * kleinAction (H := H) A eJ = 1 ∧
    kleinAction (H := H) A eε * kleinAction (H := H) A eε = 1 ∧
    kleinAction (H := H) A eJ * kleinAction (H := H) A eε = kleinAction (H := H) A eε * kleinAction (H := H) A eJ := by
  constructor
  · simp [eJ, kleinAction, A.hJ_involution]
  constructor
  · simp [eε, kleinAction, A.hε_involution]
  · simp [eJ, eε, kleinAction, A.hComm]

/-- Algebraic core: `ε`-cross-cap inversion plus V₄ automorphism compatibility force `δK = 0`. -/
theorem anomaly_vanishes (A : KleinFourData H)
    (hC : A.ε * A.δK = A.δK * A.ε) (hX : (A.ε * A.δK) * A.ε = -A.δK) : A.δK = 0 := by
  have h_auto : (A.ε * A.δK) * A.ε = A.δK := by
    calc
      (A.ε * A.δK) * A.ε = (A.δK * A.ε) * A.ε := by simpa [hC]
      _ = A.δK * (A.ε * A.ε) := by simpa [mul_assoc]
      _ = A.δK * 1 := by rw [A.hε_involution]
      _ = A.δK := by simp
  have hsign : -A.δK = A.δK := by
    calc
      -A.δK = (A.ε * A.δK) * A.ε := by simpa using hX.symm
      _ = A.δK := h_auto
  ext x
  have hpoint : -(A.δK x) = (A.δK x) := by
    simpa using congrArg (fun T : Module.End ℂ H => T x) hsign
  have hmul : (2 : ℂ) • (A.δK x) = 0 := by
    calc
      (2 : ℂ) • (A.δK x) = (A.δK x) + (A.δK x) := by simpa using (two_smul (R := ℂ) (M := H) (A.δK x))
      _ = -(A.δK x) + (A.δK x) := by simpa [hpoint]
      _ = 0 := neg_add_cancel (A.δK x)
  exact (smul_eq_zero.mp hmul).resolve_left (by norm_num)

/-- Final module-level theorem for the V₄ anomaly data. -/
theorem anomaly_must_vanish (A : KleinFourData H) : A.δK = 0 := by
  exact anomaly_vanishes (H := H) A A.h_automorphism A.h_crosscap

end InfoGeometry.Canonical.KleinFourAnomalyCancellation
