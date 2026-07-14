import InfoGeometry.Canonical.FiniteMajoranaBraiding

/-!
# InfoGeometry.Canonical.FiniteMajoranaProjectiveBraiding

Finite projective phase layer for Majorana braid-word readouts.

This file adds a purely finite/projective wrapper around
`FiniteMajoranaBraiding`: a braid word has

* a permutation readout, `evalBraidWord w`, and
* a supplied unit phase, `phase w : ℂˣ`.

A projective gate is then `phase w • readout (evalBraidWord w)`.  The only
invariance claims proved here are finite rewrite invariances, either under an
explicit phase-invariance hypothesis or when the phase itself factors through
`evalBraidWord`.

No anyon category.
No fault-tolerance theorem.
No analytic/topological completion.
-/

namespace FiniteMajoranaProjectiveBraiding

open InfoGeometry.Canonical.FiniteMajoranaBraiding

/-- A unit-complex phase assigned to each finite braid word. -/
abbrev BraidPhase := BraidWord → Units ℂ

/-- A phase assignment that factors through braid-word evaluation. -/
def phaseOfEval (χ : Equiv.Perm ℕ → Units ℂ) : BraidPhase :=
  fun w => χ (evalBraidWord w)

/--
A finite projective gate readout: scalar unit phase times a gate readout that
depends only on the evaluated braid permutation.
-/
def projectiveBraidGate (Gate : Type*) [SMul (Units ℂ) Gate]
    (phase : BraidPhase) (readout : Equiv.Perm ℕ → Gate)
    (w : BraidWord) : Gate :=
  phase w • readout (evalBraidWord w)

/-- If the phase is invariant under a braid rewrite, so is the projective gate. -/
theorem projectiveBraidGate_braid_rewrite_of_phase
    (Gate : Type*) [SMul (Units ℂ) Gate]
    (phase : BraidPhase) (readout : Equiv.Perm ℕ → Gate)
    (i : ℕ) (left right : BraidWord)
    (hphase : phase (left ++ [i, i + 1, i] ++ right) =
      phase (left ++ [i + 1, i, i + 1] ++ right)) :
    projectiveBraidGate Gate phase readout (left ++ [i, i + 1, i] ++ right) =
      projectiveBraidGate Gate phase readout (left ++ [i + 1, i, i + 1] ++ right) := by
  unfold projectiveBraidGate
  rw [hphase, evalBraidWord_braid_rewrite]

/-- If the phase is invariant under separated commutation, so is the projective gate. -/
theorem projectiveBraidGate_commute_rewrite_of_phase
    (Gate : Type*) [SMul (Units ℂ) Gate]
    (phase : BraidPhase) (readout : Equiv.Perm ℕ → Gate)
    {i j : ℕ} (hsep : i + 1 < j) (left right : BraidWord)
    (hphase : phase (left ++ [i, j] ++ right) =
      phase (left ++ [j, i] ++ right)) :
    projectiveBraidGate Gate phase readout (left ++ [i, j] ++ right) =
      projectiveBraidGate Gate phase readout (left ++ [j, i] ++ right) := by
  unfold projectiveBraidGate
  rw [hphase, evalBraidWord_commute_rewrite hsep]

/-- Evaluation-factored phases are invariant under the adjacent braid rewrite. -/
theorem phaseOfEval_braid_rewrite
    (χ : Equiv.Perm ℕ → Units ℂ)
    (i : ℕ) (left right : BraidWord) :
    phaseOfEval χ (left ++ [i, i + 1, i] ++ right) =
      phaseOfEval χ (left ++ [i + 1, i, i + 1] ++ right) := by
  unfold phaseOfEval
  rw [evalBraidWord_braid_rewrite]

/-- Evaluation-factored phases are invariant under separated commutation. -/
theorem phaseOfEval_commute_rewrite
    (χ : Equiv.Perm ℕ → Units ℂ)
    {i j : ℕ} (hsep : i + 1 < j) (left right : BraidWord) :
    phaseOfEval χ (left ++ [i, j] ++ right) =
      phaseOfEval χ (left ++ [j, i] ++ right) := by
  unfold phaseOfEval
  rw [evalBraidWord_commute_rewrite hsep]

/-- Projective gates with evaluation-factored phases are braid-rewrite invariant. -/
theorem projectiveBraidGate_braid_rewrite_of_evalPhase
    (Gate : Type*) [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate)
    (i : ℕ) (left right : BraidWord) :
    projectiveBraidGate Gate (phaseOfEval χ) readout (left ++ [i, i + 1, i] ++ right) =
      projectiveBraidGate Gate (phaseOfEval χ) readout
        (left ++ [i + 1, i, i + 1] ++ right) := by
  exact projectiveBraidGate_braid_rewrite_of_phase Gate (phaseOfEval χ) readout i left right
    (phaseOfEval_braid_rewrite χ i left right)

/-- Projective gates with evaluation-factored phases are separated-commutation invariant. -/
theorem projectiveBraidGate_commute_rewrite_of_evalPhase
    (Gate : Type*) [SMul (Units ℂ) Gate]
    (χ : Equiv.Perm ℕ → Units ℂ) (readout : Equiv.Perm ℕ → Gate)
    {i j : ℕ} (hsep : i + 1 < j) (left right : BraidWord) :
    projectiveBraidGate Gate (phaseOfEval χ) readout (left ++ [i, j] ++ right) =
      projectiveBraidGate Gate (phaseOfEval χ) readout (left ++ [j, i] ++ right) := by
  exact projectiveBraidGate_commute_rewrite_of_phase Gate (phaseOfEval χ) readout hsep
    left right (phaseOfEval_commute_rewrite χ hsep left right)

end FiniteMajoranaProjectiveBraiding
