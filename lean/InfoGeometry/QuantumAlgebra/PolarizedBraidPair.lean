import Mathlib.Algebra.Group.Action.Defs
import InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

/-!
# Polarized braid-pair interface

This owner packages two monoid actions on the positive and negative chiral
sheets together with the native mixed Zorn contraction.  It makes no claim
about a concrete braid-group realization of the supplied monoid equivalence.
-/

noncomputable section

namespace InfoGeometry.QuantumAlgebra.PolarizedBraidPair

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix
open InfoGeometry.Canonical.SplitOctonionChiralPhaseSpace

structure Data
    (BPlus BMinus : Type*) [Monoid BPlus] [Monoid BMinus] where
  mirror : BPlus ≃* BMinus
  actPlus : BPlus → Vec → Vec
  actMinus : BMinus → Vec → Vec
  actPlus_one : ∀ q : Vec, actPlus 1 q = q
  actPlus_mul : ∀ (a b : BPlus) (q : Vec),
    actPlus (a * b) q = actPlus a (actPlus b q)
  actMinus_one : ∀ p : Vec, actMinus 1 p = p
  actMinus_mul : ∀ (a b : BMinus) (p : Vec),
    actMinus (a * b) p = actMinus a (actMinus b p)

namespace Data

variable {BPlus BMinus : Type*} [Monoid BPlus] [Monoid BMinus]
variable (P : Data BPlus BMinus)

def polarizedAction (a : BPlus) (b : BMinus) (z : Phase) : Phase :=
  (P.actPlus a z.1, P.actMinus b z.2)

@[simp] theorem polarizedAction_one (z : Phase) :
    P.polarizedAction (1 : BPlus) (1 : BMinus) z = z := by
  rcases z with ⟨q, p⟩
  simp [polarizedAction, P.actPlus_one, P.actMinus_one]

theorem polarizedAction_mul
    (a₁ a₂ : BPlus) (b₁ b₂ : BMinus) (z : Phase) :
    P.polarizedAction (a₁ * a₂) (b₁ * b₂) z =
      P.polarizedAction a₁ b₁ (P.polarizedAction a₂ b₂ z) := by
  rcases z with ⟨q, p⟩
  simp [polarizedAction, P.actPlus_mul, P.actMinus_mul]

def mirrorElement (a : BPlus) : BMinus := P.mirror a

@[simp] theorem mirrorElement_one :
    P.mirrorElement (1 : BPlus) = 1 := by
  simp [mirrorElement]

@[simp] theorem mirrorElement_mul (a b : BPlus) :
    P.mirrorElement (a * b) = P.mirrorElement a * P.mirrorElement b := by
  simp [mirrorElement]

end Data

def mixedChiralContraction (q p : Vec) : ℝ :=
  (upperZorn q * lowerZorn p).a

theorem mixedChiralContraction_eq_pairing (q p : Vec) :
    mixedChiralContraction q p = chiralPairing q p := by
  rw [mixedChiralContraction, upperZorn_mul_lowerZorn]
  simp [ZornMatrix.smul, E11]

theorem mixedChiralContraction_basis (i j : Fin 3) :
    mixedChiralContraction (Vec3.basis i) (Vec3.basis j) =
      if i = j then 1 else 0 := by
  rw [mixedChiralContraction_eq_pairing]
  fin_cases i <;> fin_cases j <;>
    simp [chiralPairing, Vec3.dot, Vec3.basis]

end InfoGeometry.QuantumAlgebra.PolarizedBraidPair
