import Mathlib

/-!
# Multi-energy observational identifiability

This module is independent of the instrument and molecule carrier.
Equality of all energy-indexed forward observations defines a setoid.
Its quotient is the space of observationally distinguishable states.

No chemical identifiability is assumed: it is a separate hypothesis
about a chosen equivalence relation on candidate structures.
-/

namespace InfoGeometry.MassSpectrometry

universe u v w

/-- A deterministic multi-energy observation model. -/
structure MultiEnergyForwardModel (M : Type u) (Energy : Type v)
    (Observation : Type w) where
  observe : Energy → M → Observation

namespace MultiEnergyForwardModel

variable {M : Type u} {Energy : Type v} {Observation : Type w}
variable (F : MultiEnergyForwardModel M Energy Observation)

/-- Two candidates cannot be distinguished at any measured energy. -/
def ObservationallyEquivalent (a b : M) : Prop :=
  ∀ e, F.observe e a = F.observe e b

theorem observationallyEquivalent_refl (a : M) :
    F.ObservationallyEquivalent a a := by
  intro e
  rfl

theorem observationallyEquivalent_symm {a b : M}
    (h : F.ObservationallyEquivalent a b) :
    F.ObservationallyEquivalent b a := by
  intro e
  exact (h e).symm

theorem observationallyEquivalent_trans {a b c : M}
    (hab : F.ObservationallyEquivalent a b)
    (hbc : F.ObservationallyEquivalent b c) :
    F.ObservationallyEquivalent a c := by
  intro e
  exact (hab e).trans (hbc e)

/-- The equivalence relation induced by the complete experiment family. -/
def observationalSetoid : Setoid M where
  r := F.ObservationallyEquivalent
  iseqv := ⟨F.observationallyEquivalent_refl,
    fun _ _ => F.observationallyEquivalent_symm,
    fun _ _ _ => F.observationallyEquivalent_trans⟩

/-- Candidates modulo all observational indistinguishabilities. -/
abbrev IdentifiableStates := Quotient F.observationalSetoid

/-- The canonical map from a candidate into its observable equivalence class. -/
def observableClass (a : M) : F.IdentifiableStates :=
  Quotient.mk F.observationalSetoid a

/-- Equality of observable classes is precisely observational equivalence. -/
theorem observableClass_eq_iff (a b : M) :
    F.observableClass a = F.observableClass b ↔
      F.ObservationallyEquivalent a b := by
  exact Quotient.eq

/-- The complete multi-energy data, as an indexed family. -/
def signature (a : M) : Energy → Observation :=
  fun e => F.observe e a

theorem signature_eq_iff (a b : M) :
    F.signature a = F.signature b ↔
      F.ObservationallyEquivalent a b := by
  constructor
  · intro h e
    exact congrFun h e
  · intro h
    funext e
    exact h e

/-- Separability of distinct candidates by at least one energy. -/
def SeparatesCandidates : Prop :=
  ∀ a b : M, a ≠ b → ∃ e, F.observe e a ≠ F.observe e b

/-- Exact identification of candidates is equivalent to separation. -/
theorem separatesCandidates_iff_injective :
    F.SeparatesCandidates ↔ Function.Injective F.signature := by
  constructor
  · intro h a b hab
    by_contra hne
    obtain ⟨e, he⟩ := h a b hne
    exact he (congrFun hab e)
  · intro h a b hab
    by_contra hno
    push_neg at hno
    apply hab
    apply h
    funext e
    exact hno e

/-- Separation relative to a pre-existing chemical equivalence. -/
def IdentifiableUpTo (chemical : Setoid M) : Prop :=
  ∀ a b : M, F.ObservationallyEquivalent a b → chemical.r a b

/-- Exact criterion for data to distinguish chemical equivalence classes. -/
theorem identifiableUpTo_iff (chemical : Setoid M) :
    F.IdentifiableUpTo chemical ↔
      ∀ a b : M, F.signature a = F.signature b → chemical.r a b := by
  constructor
  · intro h a b hab
    exact h a b ((F.signature_eq_iff a b).mp hab)
  · intro h a b hab
    exact h a b ((F.signature_eq_iff a b).mpr hab)

/-- If the forward experiment is chemically invariant, it factors through
chemical equivalence classes. -/
def chemicalSignature (chemical : Setoid M)
    (invariant : ∀ a b, chemical.r a b →
      F.signature a = F.signature b) :
    Quotient chemical → (Energy → Observation) :=
  Quotient.lift F.signature invariant

/-- Under chemical invariance, identifiability up to chemical equivalence
is exactly injectivity of the induced quotient observation map. -/
theorem identifiableUpTo_iff_chemicalSignature_injective
    (chemical : Setoid M)
    (invariant : ∀ a b, chemical.r a b →
      F.signature a = F.signature b) :
    F.IdentifiableUpTo chemical ↔
      Function.Injective (F.chemicalSignature chemical invariant) := by
  constructor
  · intro h x y heq
    induction x using Quotient.ind with
    | _ a =>
      induction y using Quotient.ind with
      | _ b =>
        apply Quotient.sound
        apply h a b
        apply (F.signature_eq_iff a b).mp
        exact heq
  · intro h a b hab
    have heq : F.chemicalSignature chemical invariant
        (Quotient.mk chemical a) =
        F.chemicalSignature chemical invariant
        (Quotient.mk chemical b) :=
      (F.signature_eq_iff a b).mpr hab
    exact Quotient.exact (h heq)

end MultiEnergyForwardModel

end InfoGeometry.MassSpectrometry
