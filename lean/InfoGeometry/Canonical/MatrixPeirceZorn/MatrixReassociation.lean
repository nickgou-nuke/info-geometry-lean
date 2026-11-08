/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.MatrixPeirceZorn.MatrixReflection
import Mathlib.Algebra.Free
import Mathlib.Logic.Relation

/-!
# Reassociation of parenthesized matrix-valued expressions

Expressions use mathlib's `FreeMagma`; their evaluation uses the explicitly
named Zorn product. A context has exactly one hole, so its action on values is
an additive homomorphism. Local associators therefore propagate through every
context, and accumulated corrections telescope along arbitrary finite paths.
-/

namespace InfoGeometry.Canonical.MatrixPeirceZorn.Zorn.Reassociation

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Term (n : Type*) := FreeMagma (Carrier n)

def evaluate : Term n → Carrier n
  | .of X => X
  | .mul s t => mul (evaluate s) (evaluate t)

omit [DecidableEq n] in
@[simp] theorem evaluate_of (X : Carrier n) : evaluate (.of X) = X := rfl

omit [DecidableEq n] in
@[simp] theorem evaluate_mul (s t : Term n) :
    evaluate (s * t) = mul (evaluate s) (evaluate t) := rfl

/-- A parenthesized expression containing exactly one distinguished hole. -/
inductive Context (n : Type*)
  | hole : Context n
  | left : Context n → Term n → Context n
  | right : Term n → Context n → Context n

namespace Context

def plug : Context n → Term n → Term n
  | .hole, t => t
  | .left C s, t => plug C t * s
  | .right s C, t => s * plug C t

def action : Context n → Carrier n →+ Carrier n
  | .hole => AddMonoidHom.id _
  | .left C t =>
      ({ toFun := fun X => mul X (evaluate t)
         map_zero' := zero_mul (evaluate t)
         map_add' := fun X Y => add_mul X Y (evaluate t) } :
        Carrier n →+ Carrier n).comp (action C)
  | .right s C => (mulHom (evaluate s)).comp (action C)

@[simp] theorem evaluate_plug (C : Context n) (t : Term n) :
    evaluate (C.plug t) = C.action (evaluate t) := by
  induction C with
  | hole => rfl
  | left C s ih =>
    change mul (evaluate (C.plug t)) (evaluate s) =
      mul (C.action (evaluate t)) (evaluate s)
    rw [ih]
  | right s C ih =>
    change mul (evaluate s) (evaluate (C.plug t)) =
      mul (evaluate s) (C.action (evaluate t))
    rw [ih]

theorem evaluate_plug_sub (C : Context n) (s t : Term n) :
    evaluate (C.plug s) - evaluate (C.plug t) =
      C.action (evaluate s - evaluate t) := by
  simp only [evaluate_plug, map_sub]

end Context

omit [DecidableEq n] in
theorem rotation_defect (s t u : Term n) :
    evaluate ((s * t) * u) - evaluate (s * (t * u)) =
      associator (evaluate s) (evaluate t) (evaluate u) := rfl

theorem contextual_rotation_defect (C : Context n) (s t u : Term n) :
    evaluate (C.plug ((s * t) * u)) - evaluate (C.plug (s * (t * u))) =
      C.action (associator (evaluate s) (evaluate t) (evaluate u)) := by
  rw [C.evaluate_plug_sub, rotation_defect]

/-- An oriented rotation records its position and the three ordered subexpressions. -/
structure Rotation (n : Type*) where
  context : Context n
  first : Term n
  second : Term n
  third : Term n

namespace Rotation

def source (r : Rotation n) : Term n :=
  r.context.plug ((r.first * r.second) * r.third)

def target (r : Rotation n) : Term n :=
  r.context.plug (r.first * (r.second * r.third))

def correction (r : Rotation n) : Carrier n :=
  r.context.action (associator (evaluate r.first) (evaluate r.second) (evaluate r.third))

theorem sound (r : Rotation n) :
    evaluate r.source - evaluate r.target = r.correction :=
  contextual_rotation_defect r.context r.first r.second r.third

end Rotation

def Step (s t : Term n) : Prop :=
  ∃ r : Rotation n, r.source = s ∧ r.target = t

/-- A rotation adds its exact contextual associator to the accumulated correction. -/
def CorrectedStep (p q : Term n × Carrier n) : Prop :=
  ∃ r : Rotation n, p.1 = r.source ∧ q.1 = r.target ∧ q.2 = p.2 + r.correction

theorem corrected_step_invariant {p q : Term n × Carrier n} (h : CorrectedStep p q) :
    evaluate p.1 + p.2 = evaluate q.1 + q.2 := by
  rcases h with ⟨r, hp, hq, hc⟩
  rw [hp, hq, hc, ← r.sound]
  abel

theorem corrected_path_invariant {p q : Term n × Carrier n}
    (h : Relation.ReflTransGen CorrectedStep p q) :
    evaluate p.1 + p.2 = evaluate q.1 + q.2 := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (corrected_step_invariant h)

/-- Every path of rotations admits an exact accumulated matrix-valued correction. -/
theorem path_has_correction {s t : Term n} (h : Relation.ReflTransGen Step s t)
    (A : Carrier n) :
    ∃ B : Carrier n, Relation.ReflTransGen CorrectedStep (s, A) (t, B) := by
  induction h with
  | refl => exact ⟨A, .refl⟩
  | @tail u v _ huv ih =>
      rcases ih with ⟨B, hB⟩
      rcases huv with ⟨r, hr, ht⟩
      refine ⟨B + r.correction, hB.tail ?_⟩
      exact ⟨r, hr.symm, ht.symm, rfl⟩

theorem corrected_path_total {s t : Term n} {A : Carrier n}
    (h : Relation.ReflTransGen CorrectedStep (s, 0) (t, A)) :
    A = evaluate s - evaluate t := by
  have h' := corrected_path_invariant h
  simp only [add_zero] at h'
  exact eq_sub_of_add_eq (by simpa only [add_comm] using h'.symm)

/-- Different rotation paths between the same endpoints have the same total correction. -/
theorem path_correction_unique {s t : Term n} {A B : Carrier n}
    (hA : Relation.ReflTransGen CorrectedStep (s, 0) (t, A))
    (hB : Relation.ReflTransGen CorrectedStep (s, 0) (t, B)) : A = B :=
  (corrected_path_total hA).trans (corrected_path_total hB).symm

theorem corrected_loop_zero {s : Term n} {A : Carrier n}
    (h : Relation.ReflTransGen CorrectedStep (s, 0) (s, A)) : A = 0 := by
  simpa using corrected_path_total h

omit [DecidableEq n] in
theorem evaluate_signedExchange (t : Term n) :
    evaluate (FreeMagma.map signedExchange t) = signedExchange (evaluate t) := by
  induction t using FreeMagma.recOnMul with
  | ih1 X => rfl
  | ih2 s t hs ht =>
      change mul (evaluate (FreeMagma.map signedExchange s))
        (evaluate (FreeMagma.map signedExchange t)) =
        signedExchange (mul (evaluate s) (evaluate t))
      rw [hs, ht, signedExchange_mul]

omit [DecidableEq n] in
theorem reflected_difference (s t : Term n) :
    evaluate (FreeMagma.map signedExchange s) -
        evaluate (FreeMagma.map signedExchange t) =
      signedExchange (evaluate s - evaluate t) := by
  rw [evaluate_signedExchange, evaluate_signedExchange, signedExchange_sub]

/-- The exact reflected-channel correction remains valid at every expression position. -/
theorem contextual_reflected_reassociation (C : Context n) (u w v : Vec n) :
    evaluate (C.plug ((FreeMagma.of (upper u) * FreeMagma.of (lower w)) *
        FreeMagma.of (upper v))) =
      evaluate (C.plug (FreeMagma.of (upper u) *
        (FreeMagma.of (lower w) * FreeMagma.of (upper v)))) -
      C.action (associator (upper u) (exchange (lower w)) (exchange (upper v))) -
      C.action (associator (exchange (upper u)) (exchange (lower w)) (upper v)) := by
  simpa only [Context.evaluate_plug, evaluate_mul, evaluate_of, map_sub] using
    congrArg C.action (corrected_reassociation u w v)

end InfoGeometry.Canonical.MatrixPeirceZorn.Zorn.Reassociation
