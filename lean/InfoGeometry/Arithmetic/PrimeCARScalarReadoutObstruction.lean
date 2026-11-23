/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.PrimeMajoranaCAR

/-!
# Obstruction to integer-valued multiplicative CAR readouts

The CAR relation is incompatible with a unital ring homomorphism into `ℤ`:
commutativity of the target turns `ιε + ει = 1` into `2(ει) = 1`.
Consequently, an operator-to-occupation map into integers must be a state or
diagonal readout, not a multiplicative ring homomorphism on the full CAR ring.
-/

namespace InfoGeometry.Arithmetic.PrimeCARScalarReadoutObstruction

open InfoGeometry.Arithmetic.PrimeMajoranaCAR

/-- The integer-valued ring-hom readout hypothesis used by the abstract
CAR/Boolean bridge is impossible for any genuine `ExteriorCARPair`. -/
theorem no_CAR_integer_multiplicative_readout
    {Op : Type*} [Ring Op] (E : ExteriorCARPair Op)
    (χ : Op →+* ℤ) : False := by
  have h := congrArg χ E.iota_eps_add_eps_iota
  rw [map_add, map_mul, map_mul, map_one] at h
  have htwo : 2 * (χ E.iota * χ E.eps) = 1 := by
    calc
      2 * (χ E.iota * χ E.eps) =
          χ E.iota * χ E.eps + χ E.iota * χ E.eps := by ring
      _ = χ E.iota * χ E.eps + χ E.eps * χ E.iota := by ring
      _ = 1 := h
  omega

/-- No unital ring homomorphism from a ring containing an exterior CAR pair to
the integers can exist. -/
theorem no_integer_ring_hom_of_exteriorCARPair
    {Op : Type*} [Ring Op] (E : ExteriorCARPair Op) :
    ¬ Nonempty (Op →+* ℤ) := by
  rintro ⟨χ⟩
  exact no_CAR_integer_multiplicative_readout E χ

end InfoGeometry.Arithmetic.PrimeCARScalarReadoutObstruction
