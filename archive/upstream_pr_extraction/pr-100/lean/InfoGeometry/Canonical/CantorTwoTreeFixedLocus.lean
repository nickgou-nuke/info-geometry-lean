import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/-!
# Cantor two-tree involution and critical fixed locus

This file formalizes only the concrete finite/algebraic content present in the
repository: bitwise complement on the existing Cantor boundary carrier, the
corresponding swap of two boundary trees, and the independent complex fixed
locus theorem.  No Stone--Gelfand equivalence or binary-word-to-complex
infinite series is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorTwoTreeFixedLocus

open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/-- Bitwise complement, representing the binary branch exchange. -/
def tomitaWordConjugation
    (w : (ℕ → Bool)) : (ℕ → Bool) :=
  fun n => !w n

@[simp] theorem tomitaWordConjugation_apply
    (w : (ℕ → Bool)) (n : ℕ) :
    tomitaWordConjugation w n = !w n :=
  rfl

theorem tomitaWordConjugation_involutive
    (w : (ℕ → Bool)) :
    tomitaWordConjugation (tomitaWordConjugation w) = w := by
  funext n
  cases h : w n <;> simp [tomitaWordConjugation, h]

theorem tomitaWordConjugation_ne_self
    (w : (ℕ → Bool)) :
    tomitaWordConjugation w ≠ w := by
  intro h
  have h0 := congrFun h 0
  cases hw : w 0 <;> simp [tomitaWordConjugation, hw] at h0

/-- Tomita exchange of the two trees together with branch complement. -/
def tomitaTwoTreeConjugation
    (T : (ℕ → Bool) × (ℕ → Bool)) :
    (ℕ → Bool) × (ℕ → Bool) :=
  (tomitaWordConjugation T.2, tomitaWordConjugation T.1)

theorem tomitaTwoTreeConjugation_involutive
    (T : (ℕ → Bool) × (ℕ → Bool)) :
    tomitaTwoTreeConjugation (tomitaTwoTreeConjugation T) = T := by
  cases T with
  | mk left right =>
      simp [tomitaTwoTreeConjugation, tomitaWordConjugation_involutive]

theorem tomitaTwoTreeConjugation_fixed_pair
    (w : (ℕ → Bool)) :
    tomitaTwoTreeConjugation
        (w, tomitaWordConjugation w) =
      (w, tomitaWordConjugation w) := by
  simp [tomitaTwoTreeConjugation, tomitaWordConjugation_involutive]

/-- The antiunitary scalar reflection used by the critical-line owner. -/
def antiReflection (s : ℂ) : ℂ :=
  1 - star s

theorem antiReflection_fixed_locus (s : ℂ) :
    antiReflection s = s ↔ s.re = 1 / 2 := by
  simpa [antiReflection, eq_comm] using critical_line_fixed_locus_iff s

theorem twoTree_critical_fixed_locus
    (T : (ℕ → Bool) × (ℕ → Bool)) (s : ℂ) :
    (tomitaTwoTreeConjugation T = T ∧ antiReflection s = s) ↔
      (tomitaTwoTreeConjugation T = T ∧ s.re = 1 / 2) := by
  rw [antiReflection_fixed_locus]

end InfoGeometry.Canonical.CantorTwoTreeFixedLocus
