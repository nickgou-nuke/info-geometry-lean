import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.OperatorAlgebra

/-! Concrete finite data for a log-addressable decision procedure. -/
structure log_addressable_decision_data where
  n : ℕ
  c : ℕ
  codeCount : ℕ
  Candidate : Type
  languageAccepts : Bool
  verify : Candidate → Bool
  decode : Fin codeCount → Candidate
  hcodeCount : codeCount ≤ n ^ c
  complete : languageAccepts = true → ∃ w : Candidate, verify w = true
  sound : (∃ w : Candidate, verify w = true) → languageAccepts = true
  addressable : ∀ w : Candidate, verify w = true → ∃ r : Fin codeCount, decode r = w

namespace log_addressable_decision_data

def log_addressable_decision_enumerate_codes
    (D : log_addressable_decision_data) : Finset (Fin D.codeCount) :=
  Finset.univ

/-! The explicit decision procedure scans every short code and checks its decoded candidate. -/
def log_addressable_decision_accepts
    (D : log_addressable_decision_data) : Prop :=
  ∃ r ∈ D.log_addressable_decision_enumerate_codes,
    D.verify (D.decode r) = true

def holds (D : log_addressable_decision_data) : Prop :=
  (D.languageAccepts = true ↔ D.log_addressable_decision_accepts) ∧
    D.codeCount ≤ D.n ^ D.c

end log_addressable_decision_data

open log_addressable_decision_data

/-! Code enumeration decides the language instance under the stated data. -/
theorem log_addressable_decision_holds
    (D : log_addressable_decision_data) : D.holds := by
  refine ⟨?_, D.hcodeCount⟩
  constructor
  · intro hAccepts
    rcases D.complete hAccepts with ⟨w, hw⟩
    rcases D.addressable w hw with ⟨r, hr⟩
    refine ⟨r, by simp [log_addressable_decision_enumerate_codes], ?_⟩
    simpa [hr] using hw
  · rintro ⟨r, -, hr⟩
    exact D.sound ⟨D.decode r, hr⟩

end Omega.OperatorAlgebra
