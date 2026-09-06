import Mathlib
import InfoGeometry.Arithmetic.IdeleClassZetaSymmetry

/-!
# Finite trace shadow of the Connes idele-class picture

Connes' paper uses an adelic quotient, Hilbert-space representations, and
distribution traces.  Those analytic objects are not constructed here.  This
owner isolates the finite algebraic shadow that is already meaningful in
Mathlib: a finite permutation action has a trace readout equal to its fixed
point count, while the positive logarithmic scale layer has an exponential
character.

No adelic quotient, completion, unbounded generator, trace-class theorem, or
Riemann-hypothesis statement is asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ConnesFiniteTraceBridge

open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry
open InfoGeometry.Arithmetic.IdeleClassZetaSymmetry.IdeleClassLayer

variable {X G : Type*} [Fintype X] [DecidableEq X]

/-- The finite fixed-point count of a permutation. -/
def fixedPointCount (σ : Equiv.Perm X) : ℕ :=
  ∑ x : X, if σ x = x then 1 else 0

/-- The diagonal trace readout of a finite permutation operator. -/
def permutationTrace (σ : Equiv.Perm X) : ℂ :=
  ∑ x : X, if σ x = x then 1 else 0

theorem permutationTrace_eq_fixedPointCount (σ : Equiv.Perm X) :
    permutationTrace σ = (fixedPointCount σ : ℂ) := by
  simp [permutationTrace, fixedPointCount]

theorem permutationTrace_one :
    permutationTrace (Equiv.refl X) = (Fintype.card X : ℂ) := by
  simp [permutationTrace]

section Action

variable [Monoid G]

/-- Trace readout of a finite monoid action. -/
def actionTrace (ρ : G →* Equiv.Perm X) (g : G) : ℂ :=
  permutationTrace (ρ g)

theorem actionTrace_one (ρ : G →* Equiv.Perm X) :
    actionTrace ρ 1 = (Fintype.card X : ℂ) := by
  simpa [actionTrace] using permutationTrace_one (X := X)

end Action

section LogScale

variable [Group G]

/-- The logarithmic-scale character of the idele-class layer shadow. -/
def ideleScaleCharacter (A : IdeleClassLayer G) (s : ℂ) : ℂ :=
  Complex.exp (-s * (A.logScale : ℂ))

theorem ideleScaleCharacter_compose
    (A B : IdeleClassLayer G) (s : ℂ) :
    ideleScaleCharacter (IdeleClassLayer.compose A B) s =
      ideleScaleCharacter A s * ideleScaleCharacter B s := by
  simp [ideleScaleCharacter, IdeleClassLayer.compose, mul_add]
  rw [← Complex.exp_add]

theorem ideleScaleCharacter_identity (s : ℂ) :
    ideleScaleCharacter (IdeleClassLayer.identity : IdeleClassLayer G) s = 1 := by
  simp [ideleScaleCharacter, IdeleClassLayer.identity]

theorem ideleScaleCharacter_inverse
    (A : IdeleClassLayer G) (s : ℂ) :
    ideleScaleCharacter (IdeleClassLayer.inverse A) s =
      (ideleScaleCharacter A s)⁻¹ := by
  simp [ideleScaleCharacter, IdeleClassLayer.inverse, Complex.exp_neg]

end LogScale

end InfoGeometry.Arithmetic.ConnesFiniteTraceBridge
