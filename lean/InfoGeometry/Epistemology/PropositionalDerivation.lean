import Mathlib.Data.List.Basic

/-!
# Propositional natural deduction and semantic soundness

Derivations are built from inference rules, not from assumed validity fields.
This is a propositional calculus; it is not an implementation of Lean's kernel.
-/

namespace InfoGeometry.Epistemology.PropositionalDerivation

inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | bottom : Formula Atom
  | imp : Formula Atom → Formula Atom → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | disj : Formula Atom → Formula Atom → Formula Atom
  deriving DecidableEq, Repr

def Formula.eval {Atom : Type*} (v : Atom → Prop) : Formula Atom → Prop
  | .atom a => v a
  | .bottom => False
  | .imp A B => A.eval v → B.eval v
  | .conj A B => A.eval v ∧ B.eval v
  | .disj A B => A.eval v ∨ B.eval v

/-- Natural deduction with explicit contexts and discharged assumptions. -/
inductive Derives {Atom : Type*} : List (Formula Atom) → Formula Atom → Prop where
  | assumption {Γ A} : A ∈ Γ → Derives Γ A
  | impIntro {Γ A B} : Derives (A :: Γ) B → Derives Γ (.imp A B)
  | impElim {Γ A B} : Derives Γ (.imp A B) → Derives Γ A → Derives Γ B
  | conjIntro {Γ A B} : Derives Γ A → Derives Γ B → Derives Γ (.conj A B)
  | conjLeft {Γ A B} : Derives Γ (.conj A B) → Derives Γ A
  | conjRight {Γ A B} : Derives Γ (.conj A B) → Derives Γ B
  | disjLeft {Γ A B} : Derives Γ A → Derives Γ (.disj A B)
  | disjRight {Γ A B} : Derives Γ B → Derives Γ (.disj A B)
  | disjElim {Γ A B C} : Derives Γ (.disj A B) →
      Derives (A :: Γ) C → Derives (B :: Γ) C → Derives Γ C
  | bottomElim {Γ A} : Derives Γ .bottom → Derives Γ A

def Satisfies {Atom : Type*} (v : Atom → Prop) (Γ : List (Formula Atom)) : Prop :=
  ∀ A ∈ Γ, A.eval v

theorem satisfies_cons {Atom : Type*} {v : Atom → Prop}
    {Γ : List (Formula Atom)} {A : Formula Atom}
    (hA : A.eval v) (hΓ : Satisfies v Γ) : Satisfies v (A :: Γ) := by
  intro B hB
  rcases List.mem_cons.mp hB with h | h
  · subst B
    exact hA
  · exact hΓ B h

/-- Every inference rule preserves truth under all valuations satisfying
the undischarged assumptions. -/
theorem sound {Atom : Type*} {Γ : List (Formula Atom)} {A : Formula Atom}
    (h : Derives Γ A) (v : Atom → Prop) : Satisfies v Γ → A.eval v := by
  induction h with
  | assumption hmem => exact fun hΓ => hΓ _ hmem
  | impIntro h ih => exact fun hΓ hA => ih (satisfies_cons hA hΓ)
  | impElim h₁ h₂ ih₁ ih₂ => exact fun hΓ => ih₁ hΓ (ih₂ hΓ)
  | conjIntro h₁ h₂ ih₁ ih₂ => exact fun hΓ => ⟨ih₁ hΓ, ih₂ hΓ⟩
  | conjLeft h ih => exact fun hΓ => (ih hΓ).1
  | conjRight h ih => exact fun hΓ => (ih hΓ).2
  | disjLeft h ih => exact fun hΓ => Or.inl (ih hΓ)
  | disjRight h ih => exact fun hΓ => Or.inr (ih hΓ)
  | disjElim h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    intro hΓ
    rcases ih₁ hΓ with hA | hB
    · exact ih₂ (satisfies_cons hA hΓ)
    · exact ih₃ (satisfies_cons hB hΓ)
  | bottomElim h ih => exact fun hΓ => False.elim (ih hΓ)

theorem closed_sound {Atom : Type*} {A : Formula Atom}
    (h : Derives [] A) (v : Atom → Prop) : A.eval v :=
  sound h v (by simp [Satisfies])

/-- The calculus is consistent: no closed derivation of false exists. -/
theorem not_derives_bottom (Atom : Type*) :
    ¬ Derives ([] : List (Formula Atom)) .bottom := by
  intro h
  exact closed_sound h (fun _ => False)

/-- Identity is obtained by assumption discharge, not by a validity premise. -/
theorem derives_identity {Atom : Type*} (A : Formula Atom) :
    Derives [] (.imp A A) :=
  .impIntro (.assumption (by simp))

end InfoGeometry.Epistemology.PropositionalDerivation
