import Mathlib
import InfoGeometry.Arithmetic.SplitMajoranaPrimon
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter

Finite Möbius-graded thermal character over the certified prime register.

This module stays in the finite combinatorial layer. It re-exports the finite
Dirichlet/Witten product identity from `SplitMajoranaPrimon` under the
`PrimeMajoranaWittenCharacter` naming surface so the older arithmetic files can
delegate cleanly.

No infinite Euler product, analytic continuation, Pfaffian determinant, or RH
claim is asserted here.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter

open InfoGeometry.Arithmetic.SplitMajoranaPrimon

/-- Finite Witten character over a certified prime register. -/
def finiteWittenCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  SplitMajoranaPrimon.dirichletWittenCharacter P q

/-- Finite Möbius-graded thermal character over a certified prime register. -/
def mobiusGradedThermalCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) : ℝ :=
  finiteWittenCharacter P q

/-- The finite Witten character equals the finite Euler product. -/
theorem finiteWittenCharacter_eq_product
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      SplitMajoranaPrimon.finiteEulerProduct P q := by
  simpa [finiteWittenCharacter] using
    (SplitMajoranaPrimon.dirichletWittenCharacter_eq_eulerProduct P q)

/-- The finite Witten character equals the finite Möbius-graded thermal character. -/
theorem finiteWittenCharacter_eq_mobiusGradedThermalCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q = mobiusGradedThermalCharacter P q := by
  rfl

/-- The finite Witten character agrees with the finite Dirichlet Witten character. -/
theorem finiteWittenCharacter_eq_dirichletWittenCharacter
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      SplitMajoranaPrimon.dirichletWittenCharacter P q := by
  rfl

/-- Owner target for the finite Witten character surface. -/
@[owner_target_tag]
def PrimeMajoranaWittenCharacterOwnerTarget : Prop :=
  ∀ (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ),
    finiteWittenCharacter P q =
      SplitMajoranaPrimon.finiteEulerProduct P q ∧
    finiteWittenCharacter P q =
      mobiusGradedThermalCharacter P q ∧
    finiteWittenCharacter P q =
      SplitMajoranaPrimon.dirichletWittenCharacter P q

/-- The finite Witten character owner target is proved. -/
theorem primeMajoranaWittenCharacterOwnerTarget :
    PrimeMajoranaWittenCharacterOwnerTarget := by
  intro P q
  exact ⟨finiteWittenCharacter_eq_product P q,
    finiteWittenCharacter_eq_mobiusGradedThermalCharacter P q,
    finiteWittenCharacter_eq_dirichletWittenCharacter P q⟩

end InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter
