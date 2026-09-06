import InfoGeometry.Canonical.ChiralZornMaxwellReadout
import Mathlib.Data.Complex.Basic

/-!
# Chiral Zorn invariant readouts

This owner defines the finite chiral contractions corresponding to the
helicity density `A · B` and spin-density channel `E × A`.  Conservation,
gauge invariance, and Noether statements require a separate differential or
variational carrier and are intentionally not inferred here.
-/

namespace InfoGeometry.Canonical.ChiralZornMaxwellInvariants

open InfoGeometry.Canonical.ChiralZornMaxwellReadout

abbrev ChiralVec3 := ChiralZornMaxwellReadout.ChiralVec3

noncomputable def chiralHelicityDensity (a b : ChiralVec3) : ℂ :=
  chiralDot a b

noncomputable def chiralSpinDensity (e a : ChiralVec3) : ChiralVec3 := fun i =>
  if i = (0 : Fin 3) then
    Complex.I * (e 0 * a 2 - e 2 * a 0)
  else if i = (1 : Fin 3) then
    Complex.I * (e 2 * a 1 - e 1 * a 2)
  else
    e 0 * a 1 - e 1 * a 0

@[simp] theorem chiralHelicityDensity_apply (a b : ChiralVec3) :
    chiralHelicityDensity a b =
      ((1 : ℂ) / 2) * (a 0 * b 1 + a 1 * b 0) + a 2 * b 2 := by
  rfl

@[simp] theorem chiralSpinDensity_zero (e a : ChiralVec3) :
    chiralSpinDensity e a 0 =
      Complex.I * (e 0 * a 2 - e 2 * a 0) := by
  simp [chiralSpinDensity]

@[simp] theorem chiralSpinDensity_one (e a : ChiralVec3) :
    chiralSpinDensity e a 1 =
      Complex.I * (e 2 * a 1 - e 1 * a 2) := by
  simp [chiralSpinDensity]

@[simp] theorem chiralSpinDensity_two (e a : ChiralVec3) :
    chiralSpinDensity e a 2 = e 0 * a 1 - e 1 * a 0 := by
  simp [chiralSpinDensity]

theorem chiralSpinDensity_antisymmetric (e a : ChiralVec3) :
    chiralSpinDensity e a =
      fun i => -chiralSpinDensity a e i := by
  funext i
  fin_cases i <;> simp [chiralSpinDensity] <;> ring

end InfoGeometry.Canonical.ChiralZornMaxwellInvariants
