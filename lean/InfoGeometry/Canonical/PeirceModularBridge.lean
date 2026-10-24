/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.ParabolicModularRepresentation
import InfoGeometry.Canonical.PeirceWeylSynthesis

/-! Connect the new ring-only relations to the existing MP/Weyl/trace owners. -/
namespace InfoGeometry.Canonical.PeirceModularBridge

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra
open InfoGeometry.Core.PeirceWeylUnits
open InfoGeometry.Core.ParabolicShearRelations
open InfoGeometry.Core.ParabolicModularRepresentation

variable {A : Type*} [Ring A] [StarRing A] {d b : A}

/-- No second MP or support structure is introduced by this adapter. -/
theorem double_cube_eq_weyl_square (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    doubleShear d b ^ 3 = weylElement d b * weylElement d b := by
  rw [double_cube hd (h.inverse_sq_eq_zero hd) h.aba_eq_a h.bab_eq_b,
    weyl_square h hd]
  unfold supportSign harmonicSupport activeSupport exactSupport coexactSupport
  abel

/-- The representation's quartic unit is precisely the existing native Weyl unit. -/
theorem tripleUnit_eq_weylUnit (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    tripleUnit hd (h.inverse_sq_eq_zero hd) = weylUnit h hd := by
  apply Units.ext
  change (1 + d) * (1 - b) * (1 + d) = weylElement d b
  exact unipotent_triple hd h.aba_eq_a

/-- Correct ordered relationship: the supported third root is obtained using T, not T inverse. -/
theorem weyl_mul_forward_shear (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    weylElement d b * (1 + d) = harmonicSupport d b + thirdRoot d b := by
  have hwd : weylElement d b * d = -(b * d) := by
    simp only [weylElement, majoranaMinus, add_mul, sub_mul,
      h.harmonicSupport_mul_eq_zero hd, hd, zero_sub, zero_add]
  rw [mul_add, mul_one, hwd]
  unfold weylElement majoranaMinus thirdRoot coexactSupport
  abel

/-- Full-support Phi-six is a special case; in general the polynomial sees the harmonic part. -/
theorem double_cyclotomic_defect (h : IsMoorePenroseInverse d b) (hd : d * d = 0) :
    doubleShear d b ^ 2 - doubleShear d b + 1 = harmonicSupport d b := by
  rw [pow_two, double_quadratic_defect hd (h.inverse_sq_eq_zero hd) h.aba_eq_a h.bab_eq_b]
  unfold harmonicSupport exactSupport coexactSupport
  abel

end InfoGeometry.Canonical.PeirceModularBridge
