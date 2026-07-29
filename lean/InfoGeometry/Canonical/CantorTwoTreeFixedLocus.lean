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

abbrev Word := InfiniteBinaryWordSpace

/-- Bitwise complement, representing the binary branch exchange. -/
def tomitaWordConjugation (w : Word) : Word :=
  fun n => !w n

@[simp] theorem tomitaWordConjugation_apply (w : Word) (n : ℕ) :
    tomitaWordConjugation w n = !w n :=
  rfl

theorem tomitaWordConjugation_involutive (w : Word) :
    tomitaWordConjugation (tomitaWordConjugation w) = w := by
  funext n
  cases h : w n <;> simp [tomitaWordConjugation, h]

/-- Two independent symbolic boundary trees. -/
abbrev TwoTree := Word × Word

/-- Tomita exchange of the two trees together with branch complement. -/
def tomitaTwoTreeConjugation (T : TwoTree) : TwoTree :=
  (tomitaWordConjugation T.2, tomitaWordConjugation T.1)

theorem tomitaTwoTreeConjugation_involutive (T : TwoTree) :
    tomitaTwoTreeConjugation (tomitaTwoTreeConjugation T) = T := by
  cases T with
  | mk left right =>
      simp [tomitaTwoTreeConjugation, tomitaWordConjugation_involutive]

/-- The antiunitary scalar reflection used by the critical-line owner. -/
def antiReflection (s : ℂ) : ℂ :=
  1 - star s

theorem antiReflection_fixed_locus (s : ℂ) :
    antiReflection s = s ↔ s.re = 1 / 2 := by
  simpa [antiReflection, eq_comm] using critical_line_fixed_locus_iff s

theorem twoTree_critical_fixed_locus (T : TwoTree) (s : ℂ) :
    (tomitaTwoTreeConjugation T = T ∧ antiReflection s = s) ↔
      (tomitaTwoTreeConjugation T = T ∧ s.re = 1 / 2) := by
  rw [antiReflection_fixed_locus]

end InfoGeometry.Canonical.CantorTwoTreeFixedLocus
