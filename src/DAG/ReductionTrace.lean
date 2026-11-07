import Mathlib

/-!
# Proof-relevant reduction traces

This is the generic dynamic carrier for a computation relation.  It does not
identify any particular relation with beta reduction; an object-language owner
supplies that relation explicitly.
-/

namespace DAG

inductive ReductionTrace {α : Type} (step : α → α → Type) :
    α → List α → α → Type where
  | refl (a : α) : ReductionTrace step a [] a
  | cons {a b c : α} {xs : List α} :
      step a b → ReductionTrace step b xs c →
      ReductionTrace step a (b :: xs) c

def ReductionTrace.single {α : Type} {step : α → α → Type}
    {a b : α} (h : step a b) :
    ReductionTrace step a [b] b :=
  .cons h (.refl b)

def ReductionTrace.refl_trace {α : Type} {step : α → α → Type}
    (a : α) : ReductionTrace step a [] a :=
  .refl a

noncomputable def ReductionTrace.trans {α : Type} {step : α → α → Type}
    {a b c : α} {xs ys : List α}
    (h₁ : ReductionTrace step a xs b)
    (h₂ : ReductionTrace step b ys c) :
    ReductionTrace step a (xs ++ ys) c := by
  induction h₁ with
  | refl => simpa using h₂
  | cons hab htail ih =>
      simpa [List.cons_append] using ReductionTrace.cons hab (ih h₂)

theorem ReductionTrace.to_reflTransGen {α : Type} {step : α → α → Type}
    {a b : α} {xs : List α}
    (h : ReductionTrace step a xs b) :
    Relation.ReflTransGen (fun x y => Nonempty (step x y)) a b := by
  induction h with
  | refl => exact .refl
  | cons hab htail ih => exact .head ⟨hab⟩ ih

end DAG
