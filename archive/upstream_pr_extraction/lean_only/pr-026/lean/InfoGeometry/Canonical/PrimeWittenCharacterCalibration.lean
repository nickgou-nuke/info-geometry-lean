import Mathlib.Tactic
import InfoGeometry.Arithmetic.PrimeWittenCharacter
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Canonical.PrimeWittenCharacterCalibration

Canonical wrapper for the finite Witten-character owner.

This file adds no analytic content. It only re-exports the finite
Witten-character identities under a canonical owner-facing namespace.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeWittenCharacterCalibration

open InfoGeometry.Arithmetic.PrimeWittenCharacter

/-- Canonical re-export of the finite Witten character / Euler-product theorem. -/
theorem canonicalFiniteWittenCharacter_eq_eulerProduct
    {P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister}
    (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q :=
  finiteWittenCharacter_eq_eulerProduct P q

/-- Canonical re-export of the finite Witten character / Möbius-thermal theorem. -/
theorem canonicalFiniteWittenCharacter_eq_mobiusGradedThermalCharacter
    {P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister}
    (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter P q :=
  finiteWittenCharacter_eq_mobiusGradedThermalCharacter P q

/-- Canonical re-export of the finite Witten character / Dirichlet-Witten theorem. -/
theorem canonicalFiniteWittenCharacter_eq_dirichletWittenCharacter
    {P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister}
    (q : ℕ → ℝ) :
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q :=
  finiteWittenCharacter_eq_dirichletWittenCharacter P q

/-- Canonical owner target for the finite Witten-character surface. -/
@[owner_target_tag]
def CanonicalPrimeWittenCharacterOwnerTarget : Prop :=
  ∀ (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister) (q : ℕ → ℝ),
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.finiteEulerProduct P q ∧
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.PrimeMajoranaWittenCharacter.mobiusGradedThermalCharacter P q ∧
    finiteWittenCharacter P q =
      InfoGeometry.Arithmetic.SplitMajoranaPrimon.dirichletWittenCharacter P q

/-- The canonical owner target is proved. -/
theorem canonicalPrimeWittenCharacterOwnerTarget :
    CanonicalPrimeWittenCharacterOwnerTarget := by
  intro P q
  exact ⟨finiteWittenCharacter_eq_eulerProduct P q,
    finiteWittenCharacter_eq_mobiusGradedThermalCharacter P q,
    finiteWittenCharacter_eq_dirichletWittenCharacter P q⟩

end InfoGeometry.Canonical.PrimeWittenCharacterCalibration
