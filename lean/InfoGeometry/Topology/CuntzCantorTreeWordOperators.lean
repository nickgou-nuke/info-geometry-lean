import InfoGeometry.Topology.CantorBoundaryCuntzFamily
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Finite word operators on the Cantor-boundary Cuntz carrier

The concrete head/tail Cuntz family gives the one-step branches.  This owner
packages their finite words and proves only the finite concatenation/readout
laws needed for a rooted-tree realization.  No braid action, topology, or
infinite path measure is introduced here.
-/

noncomputable section

namespace InfoGeometry.Topology.CantorBoundaryCuntzFamily

abbrev Boundary := C4Boundary
abbrev BoundaryFunctions := C4Functions
abbrev BoundaryEnd := C4Functions →ₗ[ℂ] C4Functions

/-- The creation operator associated to a finite word. -/
def cuntzWordS : List (Fin 4) → BoundaryEnd
  | [] => 1
  | i :: w => cuntzS i * cuntzWordS w

@[simp] theorem cuntzWordS_nil : cuntzWordS ([] : List (Fin 4)) = 1 := rfl

/-- The tail remaining after consuming a finite word. -/
def tailAfter : List (Fin 4) → Boundary → Boundary
  | [], b => b
  | _ :: w, b => tailAfter w (tailN b)

/-- Predicate that a boundary sequence begins with a finite word. -/
def wordHeadMatches : List (Fin 4) → Boundary → Prop
  | [], _ => True
  | i :: w, b => headN b = i ∧ wordHeadMatches w (tailN b)

theorem cuntzWordS_append (u v : List (Fin 4)) :
    cuntzWordS (u ++ v) = cuntzWordS u * cuntzWordS v := by
  induction u with
  | nil => simp [cuntzWordS]
  | cons i u ih =>
      simp only [List.cons_append, cuntzWordS]
      rw [ih]
      simp [mul_assoc]

/-- Evaluation of a word operator: successive head tests consume the word. -/
theorem cuntzWordS_apply_cons
    (i : Fin 4) (w : List (Fin 4))
    (f : BoundaryFunctions) (b : Boundary) :
    cuntzWordS (i :: w) f b =
      if headN b = i then cuntzWordS w f (tailN b) else 0 := by
  simp [cuntzWordS, cuntzS]

theorem cuntzWordS_apply_nil (f : BoundaryFunctions) (b : Boundary) :
    cuntzWordS ([] : List (Fin 4)) f b = f b := by
  rfl

attribute [local instance] Classical.propDecidable

theorem cuntzWordS_apply
    (w : List (Fin 4)) (f : BoundaryFunctions) (b : Boundary) :
    cuntzWordS w f b =
      if wordHeadMatches w b then f (tailAfter w b) else 0 := by
  classical
  induction w generalizing b with
  | nil => simp [cuntzWordS, wordHeadMatches, tailAfter]
  | cons i w ih =>
      rw [cuntzWordS_apply_cons]
      by_cases h : headN b = i
      · simp [wordHeadMatches, tailAfter, h, ih]
      · simp [wordHeadMatches, h]

end InfoGeometry.Topology.CantorBoundaryCuntzFamily

end noncomputable section
