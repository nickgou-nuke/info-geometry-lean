/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.EpistemicCompilerPeirceBridge
import InfoGeometry.Algebra.NestedGroupWords
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Units.Hom

/-!
# Exact variation of an ordered Peirce shear

For a fixed idempotent, the upper and lower Peirce corners give a reversible
ordered gate. This module reuses `epistemicCornerShear` and its reverse-ordered
inverse. It proves the exact finite update, state reconstruction, and the
right-trivialized algebraic variation in independent parameter directions.

The finite update retains its quadratic remainder. The variation becomes a
Fréchet derivative only after supplying the normed-algebra structure and the
corresponding differentiability proof. No complexity or numerical stability
claim follows from these ring identities.

Finally, products whose factors all belong to the same fixed upper-corner
alphabet depend only on the sum of their parameters. Their permutation
invariance is a restriction of that alphabet, not an assumption that the
ambient ring is commutative.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- The finite parameter update has an exact mixed quadratic remainder.
Neither an idempotency assumption nor a limiting argument is needed for
this expansion. -/
theorem epistemicCornerShear_add (P A C dA dC : B) :
    epistemicCornerShear P (A + dA) (C + dC) =
      epistemicCornerShear P A C +
        (conePlus P dA * (1 + coneMinus P C) +
          (1 + conePlus P A) * coneMinus P dC) +
        conePlus P dA * coneMinus P dC := by
  simp only [epistemicCornerShear, conePlus_add, coneMinus_add]
  noncomm_ring

variable {P : B} (hP : P * P = P)
include hP

/-- The midpoint can be recovered from the output by the upper inverse
factor, while retaining the original multiplication order. -/
theorem epistemicCornerShear_midpoint (A C x : B) :
    (1 - conePlus P A) * (epistemicCornerShear P A C * x) =
      (1 + coneMinus P C) * x := by
  simp only [epistemicCornerShear]
  peirce_nf hP

/-- Applying the reverse-ordered inverse recovers the input exactly. -/
theorem epistemicCornerShear_reconstruct (A C x : B) :
    epistemicCornerShearInv P A C * (epistemicCornerShear P A C * x) = x := by
  rcases master_epistemic_compiler_synthesis hP A C 0 0 0 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hInv, _⟩
  rw [← mul_assoc, hInv, one_mul]

/-- The right-trivialized parameter variation loses its explicit lower
parameter coefficient through same-corner annihilation. The output on which
this coefficient acts can still depend on both parameters. -/
theorem epistemicCornerShear_rightVariation (A C dA dC : B) :
    (conePlus P dA * (1 + coneMinus P C) +
        (1 + conePlus P A) * coneMinus P dC) *
      epistemicCornerShearInv P A C =
      conePlus P dA +
        (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A) := by
  simp only [epistemicCornerShearInv]
  peirce_nf hP

/-- Expansion of the right-trivialized variation retains the ordered
quadratic sandwich. It is not just the commutator contribution. -/
theorem epistemicCornerShear_rightVariation_expansion (A C dA dC : B) :
    (conePlus P dA * (1 + coneMinus P C) +
        (1 + conePlus P A) * coneMinus P dC) *
      epistemicCornerShearInv P A C =
      conePlus P dA + coneMinus P dC +
        comm (conePlus P A) (coneMinus P dC) -
        conePlus P A * coneMinus P dC * conePlus P A := by
  rw [epistemicCornerShear_rightVariation hP]
  simp only [comm]
  noncomm_ring

/-- The full variation, including an arbitrary input direction, can be
written using the output and the recovered midpoint. This is an algebraic
identity; the analytic derivative theorem supplies its interpretation as
the derivative of the gate application. -/
theorem epistemicCornerShear_outputVariation (A C dA dC x dx : B) :
    (conePlus P dA * (1 + coneMinus P C) +
        (1 + conePlus P A) * coneMinus P dC) * x +
      epistemicCornerShear P A C * dx =
      conePlus P dA * (epistemicCornerShear P A C * x) +
        (1 + conePlus P A) * coneMinus P dC *
          ((1 - conePlus P A) * (epistemicCornerShear P A C * x)) +
        epistemicCornerShear P A C * dx := by
  calc
    _ = ((conePlus P dA * (1 + coneMinus P C) +
          (1 + conePlus P A) * coneMinus P dC) *
        epistemicCornerShearInv P A C) *
          (epistemicCornerShear P A C * x) +
        epistemicCornerShear P A C * dx := by
          rw [mul_assoc, epistemicCornerShear_reconstruct hP]
    _ = (conePlus P dA +
          (1 + conePlus P A) * coneMinus P dC * (1 - conePlus P A)) *
          (epistemicCornerShear P A C * x) +
        epistemicCornerShear P A C * dx := by
          rw [epistemicCornerShear_rightVariation hP]
    _ = _ := by noncomm_ring

/-- A word formed entirely from one fixed upper Peirce corner depends
only on the sum of its parameters, even in a noncommutative ambient ring. -/
theorem prod_one_add_conePlus (xs : List B) :
    (xs.map fun A => 1 + conePlus P A).prod = 1 + conePlus P xs.sum := by
  induction xs with
  | nil => simp [conePlus_zero]
  | cons A xs ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, conePlus_add]
      peirce_nf hP

/-- In particular, a fixed-upper-corner gate word cannot distinguish
permutations of its labels. This does not apply to mixed-corner words. -/
theorem prod_one_add_conePlus_eq_of_perm {xs ys : List B} (h : xs.Perm ys) :
    (xs.map fun A => 1 + conePlus P A).prod =
      (ys.map fun A => 1 + conePlus P A).prod := by
  rw [prod_one_add_conePlus hP, prod_one_add_conePlus hP, h.sum_eq]

/-- Balanced labeled trees cancel for the actual mixed-corner Peirce gates.
Each gate is constructed as a native unit using its proved two-sided inverse;
the noncommutative group-word reduction is then transported to the ring by
the canonical monoid homomorphism from units. No commutation of different
gate labels is assumed. -/
theorem epistemicCornerShear_bracketWord_prod {α : Type*}
    (params : α → B × B) (t : BinaryTree α) :
    ((InfoGeometry.Algebra.NestedGroupWords.bracketWord t).map
      (fun s => cond s.2
        (epistemicCornerShear P (params s.1).1 (params s.1).2)
        (epistemicCornerShearInv P (params s.1).1 (params s.1).2))).prod = 1 := by
  have hInverse (a : α) :
      epistemicCornerShear P (params a).1 (params a).2 *
          epistemicCornerShearInv P (params a).1 (params a).2 = 1 ∧
      epistemicCornerShearInv P (params a).1 (params a).2 *
          epistemicCornerShear P (params a).1 (params a).2 = 1 := by
    rcases master_epistemic_compiler_synthesis hP (params a).1 (params a).2 0 0 0 with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRight, hLeft, _⟩
    exact ⟨hRight, hLeft⟩
  let gate : α → Bˣ := fun a =>
    ⟨epistemicCornerShear P (params a).1 (params a).2,
      epistemicCornerShearInv P (params a).1 (params a).2,
      (hInverse a).1, (hInverse a).2⟩
  have h := congrArg (Units.coeHom B)
    (InfoGeometry.Algebra.NestedGroupWords.bracketWord_prod gate t)
  simpa only [map_list_prod, map_one, List.map_map, Function.comp_def,
    Bool.apply_cond, Units.coeHom_apply, gate, Units.inv_mk] using h

end InfoGeometry.OperatorAlgebra.PeirceSpine
