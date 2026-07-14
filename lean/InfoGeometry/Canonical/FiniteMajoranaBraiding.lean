import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.FiniteMajoranaBraiding

Finite algebraic braid readouts for Majorana/topological-qubit toy models.

This file deliberately proves only the finite Coxeter shadow of braiding:
adjacent exchanges act as swaps on mode labels, separated exchanges commute,
and adjacent exchanges satisfy the Yang--Baxter braid relation after evaluation.

No anyon category.
No analytic fault-tolerance theorem.
No infinite limit.
-/

namespace FiniteMajoranaBraiding

/--
The finite algebraic readout of a neighboring Majorana exchange on mode labels:
exchange positions `i` and `i + 1`.
-/
def majoranaSwap (i : ℕ) : Equiv.Perm ℕ :=
  Equiv.swap i (i + 1)

@[simp]
theorem majoranaSwap_apply_left (i : ℕ) :
    majoranaSwap i i = i + 1 := by
  simp [majoranaSwap]

@[simp]
theorem majoranaSwap_apply_right (i : ℕ) :
    majoranaSwap i (i + 1) = i := by
  simp [majoranaSwap]

/-- Each neighboring exchange is involutive at the permutation readout level. -/
theorem majoranaSwap_sq (i : ℕ) :
    majoranaSwap i * majoranaSwap i = 1 := by
  ext x
  simp [majoranaSwap]

/-- Separated neighboring exchanges commute. -/
theorem majoranaSwap_comm_of_separated {i j : ℕ} (h : i + 1 < j) :
    majoranaSwap i * majoranaSwap j = majoranaSwap j * majoranaSwap i := by
  ext x
  change majoranaSwap i (majoranaSwap j x) = majoranaSwap j (majoranaSwap i x)
  simp only [majoranaSwap, Equiv.swap_apply_def]
  split_ifs <;> omega

/-- Adjacent neighboring exchanges satisfy the braid/Yang--Baxter relation. -/
theorem majoranaSwap_braid (i : ℕ) :
    majoranaSwap i * majoranaSwap (i + 1) * majoranaSwap i =
      majoranaSwap (i + 1) * majoranaSwap i * majoranaSwap (i + 1) := by
  ext x
  change majoranaSwap i (majoranaSwap (i + 1) (majoranaSwap i x)) =
    majoranaSwap (i + 1) (majoranaSwap i (majoranaSwap (i + 1) x))
  simp only [majoranaSwap, Equiv.swap_apply_def]
  split_ifs <;> omega

/-- A finite braid word is a list of neighboring exchange indices. -/
abbrev BraidWord := List ℕ

/-- Evaluate a finite braid word as a permutation of Majorana mode labels. -/
def evalBraidWord : BraidWord → Equiv.Perm ℕ
  | [] => 1
  | i :: w => majoranaSwap i * evalBraidWord w

@[simp]
theorem evalBraidWord_nil :
    evalBraidWord [] = 1 :=
  rfl

@[simp]
theorem evalBraidWord_cons (i : ℕ) (w : BraidWord) :
    evalBraidWord (i :: w) = majoranaSwap i * evalBraidWord w :=
  rfl

/-- Evaluation sends word concatenation to multiplication of permutation readouts. -/
theorem evalBraidWord_append (u v : BraidWord) :
    evalBraidWord (u ++ v) = evalBraidWord u * evalBraidWord v := by
  induction u with
  | nil => simp
  | cons i u ih =>
      simp [ih, mul_assoc]

/-- Evaluation is invariant under the separated-commutation braid rewrite. -/
theorem evalBraidWord_commute_rewrite {i j : ℕ} (h : i + 1 < j)
    (left right : BraidWord) :
    evalBraidWord (left ++ [i, j] ++ right) =
      evalBraidWord (left ++ [j, i] ++ right) := by
  rw [evalBraidWord_append, evalBraidWord_append]
  rw [evalBraidWord_append, evalBraidWord_append]
  simp [majoranaSwap_comm_of_separated h, mul_assoc]

/-- Evaluation is invariant under the adjacent braid/Yang--Baxter rewrite. -/
theorem evalBraidWord_braid_rewrite (i : ℕ) (left right : BraidWord) :
    evalBraidWord (left ++ [i, i + 1, i] ++ right) =
      evalBraidWord (left ++ [i + 1, i, i + 1] ++ right) := by
  rw [evalBraidWord_append, evalBraidWord_append]
  rw [evalBraidWord_append, evalBraidWord_append]
  have h := congrArg (fun g => evalBraidWord left * g * evalBraidWord right)
    (majoranaSwap_braid i)
  simpa [mul_assoc] using h

/--
A finite gate readout assigned to braid words through their Majorana-label
permutation readout.
-/
def braidGateReadout (Gate : Type*) (readout : Equiv.Perm ℕ → Gate)
    (w : BraidWord) : Gate :=
  readout (evalBraidWord w)

/-- Any gate readout depending only on evaluation is invariant under braid rewrites. -/
theorem braidGateReadout_braid_rewrite
    (Gate : Type*) (readout : Equiv.Perm ℕ → Gate)
    (i : ℕ) (left right : BraidWord) :
    braidGateReadout Gate readout (left ++ [i, i + 1, i] ++ right) =
      braidGateReadout Gate readout (left ++ [i + 1, i, i + 1] ++ right) := by
  unfold braidGateReadout
  rw [evalBraidWord_braid_rewrite]

/-- Any gate readout depending only on evaluation is invariant under separated commutation. -/
theorem braidGateReadout_commute_rewrite
    (Gate : Type*) (readout : Equiv.Perm ℕ → Gate)
    {i j : ℕ} (h : i + 1 < j) (left right : BraidWord) :
    braidGateReadout Gate readout (left ++ [i, j] ++ right) =
      braidGateReadout Gate readout (left ++ [j, i] ++ right) := by
  unfold braidGateReadout
  rw [evalBraidWord_commute_rewrite h]

end FiniteMajoranaBraiding
