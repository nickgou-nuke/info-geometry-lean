import InfoGeometry.OperatorAlgebra.TKKClosure
import InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK

/-!
# TKKLieClosure to literature-level 3-grading bridge

This file does not invent new structure.  It repackages the native
`InfoGeometry.OperatorAlgebra.TKKClosure.TKKLieClosure` into the abstract
`TKKThreeGradedClosure` interface used by the literature-facing canonical layer.

The sign convention is aligned with the native owner as follows:

* literature `g₊`  = native negative grade;
* literature `g₋`  = native positive grade;
* literature `g₀`  = native zero grade.

This is purely a transport convention.  No new algebraic claim is added.
-/

noncomputable section

namespace InfoGeometry.Canonical.TKKLieThreeGradedBridge

open InfoGeometry.OperatorAlgebra
open InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK

namespace TKKLieClosure

variable
    {J L : Type*}
    [AddCommGroup J] [Module ℝ J]
    [AddCommGroup L] [Module ℝ L]
    (T : TKKLieClosure J L)

/-- Negating the first bracket argument negates the bracket. -/
theorem bracket_neg_left
    (x y : L) :
    T.lie.bracket (-x) y = - T.lie.bracket x y := by
  simpa using (T.lie.bracket_smul_left (-1 : ℝ) x y)

/-- Negating the second bracket argument negates the bracket. -/
theorem bracket_neg_right
    (x y : L) :
    T.lie.bracket x (-y) = - T.lie.bracket x y := by
  calc
    T.lie.bracket x (-y) = - T.lie.bracket (-y) x := by
      rw [T.lie.bracket_skew]
    _ = - (- T.lie.bracket y x) := by
      rw [bracket_neg_left]
    _ = T.lie.bracket y x := by simp
    _ = - T.lie.bracket x y := by
      rw [T.lie.bracket_skew]

/--
Repackage the native TKK Lie closure as the abstract literature-level
3-grading packet.

The transport predicates are sign-closed images of the native generators so
that the closure laws remain explicit and theorem-honest.
-/
def toLiteratureThreeGradedClosure :
    TKKThreeGradedClosure L where
  bracket := T.lie.bracket
  inGPlus := fun x => ∃ a : J, x = T.neg a ∨ x = -T.neg a
  inGZero := fun x => ∃ a b : J, x = T.zero a b ∨ x = -T.zero a b
  inGMinus := fun x => ∃ a : J, x = T.pos a ∨ x = -T.pos a
  bracket_plus_minus_mem_zero := by
    intro x y hx hy
    rcases hx with ⟨a, rfl | rfl⟩
    · rcases hy with ⟨b, rfl | rfl⟩
      · exact ⟨a, b, Or.inl (T.bracket_neg_pos a b)⟩
      · refine ⟨a, b, Or.inr ?_⟩
        rw [bracket_neg_right (T := T)]
        simp [T.bracket_neg_pos]
    · rcases hy with ⟨b, rfl | rfl⟩
      · refine ⟨a, b, Or.inr ?_⟩
        rw [bracket_neg_left (T := T)]
        simp [T.bracket_neg_pos]
      · refine ⟨a, b, Or.inl ?_⟩
        rw [bracket_neg_left (T := T), bracket_neg_right (T := T)]
        simp [T.bracket_neg_pos]
  bracket_zero_plus_mem_plus := by
    intro x y hx hy
    rcases hx with ⟨a, b, rfl | rfl⟩
    · rcases hy with ⟨c, rfl | rfl⟩
      · exact ⟨T.jordan.triple a b c, Or.inl (T.bracket_zero_neg a b c)⟩
      · refine ⟨T.jordan.triple a b c, Or.inr ?_⟩
        have h :
            T.lie.bracket (T.zero a b) (-T.neg c) =
              -T.neg (T.jordan.triple a b c) := by
          rw [bracket_neg_right (T := T), T.bracket_zero_neg]
        exact h
    · rcases hy with ⟨c, rfl | rfl⟩
      · refine ⟨T.jordan.triple a b c, Or.inr ?_⟩
        have h :
            T.lie.bracket (-T.zero a b) (T.neg c) =
              -T.neg (T.jordan.triple a b c) := by
          rw [bracket_neg_left (T := T), T.bracket_zero_neg]
        exact h
      · refine ⟨T.jordan.triple a b c, Or.inl ?_⟩
        have h :
            T.lie.bracket (-T.zero a b) (-T.neg c) =
              T.neg (T.jordan.triple a b c) := by
          rw [bracket_neg_left (T := T), bracket_neg_right (T := T), T.bracket_zero_neg]
          simp
        exact h
  bracket_zero_minus_mem_minus := by
    intro x y hx hy
    rcases hx with ⟨a, b, rfl | rfl⟩
    · rcases hy with ⟨c, rfl | rfl⟩
      · exact ⟨T.jordan.triple b a c, Or.inr (T.bracket_zero_pos a b c)⟩
      · refine ⟨T.jordan.triple b a c, Or.inl ?_⟩
        have h :
            T.lie.bracket (T.zero a b) (-T.pos c) =
              T.pos (T.jordan.triple b a c) := by
          rw [bracket_neg_right (T := T), T.bracket_zero_pos]
          simp
        exact h
    · rcases hy with ⟨c, rfl | rfl⟩
      · refine ⟨T.jordan.triple b a c, Or.inl ?_⟩
        have h :
            T.lie.bracket (-T.zero a b) (T.pos c) =
              T.pos (T.jordan.triple b a c) := by
          rw [bracket_neg_left (T := T), T.bracket_zero_pos]
          simp
        exact h
      · refine ⟨T.jordan.triple b a c, Or.inr ?_⟩
        have h :
            T.lie.bracket (-T.zero a b) (-T.pos c) =
              -T.pos (T.jordan.triple b a c) := by
          rw [bracket_neg_left (T := T), bracket_neg_right (T := T), T.bracket_zero_pos]
          simp
        exact h
  bracket_zero_zero_mem_zero := by
    intro x y hx hy
    rcases hx with ⟨a, b, rfl | rfl⟩
    · rcases hy with ⟨c, d, rfl | rfl⟩
      · rcases T.zero_zero_bracket a b c d with ⟨u, v, hu⟩
        exact ⟨u, v, Or.inl hu⟩
      · rcases T.zero_zero_bracket a b c d with ⟨u, v, hu⟩
        refine ⟨u, v, Or.inr ?_⟩
        simpa [bracket_neg_right (T := T)] using congrArg Neg.neg hu
    · rcases hy with ⟨c, d, rfl | rfl⟩
      · rcases T.zero_zero_bracket a b c d with ⟨u, v, hu⟩
        refine ⟨u, v, Or.inr ?_⟩
        simpa [bracket_neg_left (T := T)] using congrArg Neg.neg hu
      · rcases T.zero_zero_bracket a b c d with ⟨u, v, hu⟩
        refine ⟨u, v, Or.inl ?_⟩
        simpa [bracket_neg_left (T := T), bracket_neg_right (T := T)] using hu

end TKKLieClosure

end InfoGeometry.Canonical.TKKLieThreeGradedBridge
