/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveNilpotentFlows
import InfoGeometry.Streaming.UnipotentMemoryShift

/-!
# Native parabolic unit-group representations

Contract: central scalars in an arbitrary associative `R`-algebra, and an
explicit square-zero generator. Reuse the existing unipotent unit constructor
and reflexive-pair flow identities. The additive parameter group is encoded
by Mathlib's `Multiplicative`; no topology or faithfulness is assumed.
-/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The additive scalar group acts by parabolic units. -/
def parabolicUnitsHom {d : A} (hd : d * d = 0) : Multiplicative R →* Aˣ where
  toFun s := Streaming.UnipotentMemoryShift.unipotentUnit (s.toAdd • d)
    (by simp only [smul_mul_smul, hd, smul_zero])
  map_one' := by
    apply Units.ext
    change 1 + (0 : R) • d = 1
    simp
  map_mul' s t := by
    apply Units.ext
    change unipotent (s.toAdd + t.toAdd) d =
      unipotent s.toAdd d * unipotent t.toAdd d
    exact (unipotent_add hd _ _).symm

/-- The kernel consists exactly of parameters annihilating the generator. -/
theorem parabolicUnitsHom_eq_one_iff {d : A} (hd : d * d = 0)
    (s : Multiplicative R) :
    parabolicUnitsHom hd s = 1 ↔ s.toAdd • d = 0 := by
  constructor
  · intro h
    have hv := congrArg (fun u : Aˣ => (u : A)) h
    change 1 + s.toAdd • d = 1 at hv
    exact add_left_cancel (hv.trans (add_zero (1 : A)).symm)
  · intro h
    apply Units.ext
    change 1 + s.toAdd • d = 1
    rw [h, add_zero]

variable {d B : A} (hd : d * d = 0) (hB : B * B = 0)
  (hr : d * B * d = d) (hs : B * d * B = B)

include hs in
/-- The Weyl unit exchanges the two native parabolic representations. -/
theorem weylUnit_conjugates_parabolic (s : R) :
    weylUnit hd hB hr * parabolicUnitsHom hd (Multiplicative.ofAdd s) *
      (weylUnit hd hB hr)⁻¹ =
        parabolicUnitsHom hB (Multiplicative.ofAdd (-s)) := by
  apply Units.ext
  change weyl d B * unipotent s d * weylInv d B = unipotent (-s) B
  exact weyl_swap_unipotent hd hB hr hs s

/-- The three-factor relation holds in the native group of units. -/
theorem parabolic_triple_eq_weylUnit :
    parabolicUnitsHom hd (Multiplicative.ofAdd (1 : R)) *
      parabolicUnitsHom hB (Multiplicative.ofAdd (-1 : R)) *
      parabolicUnitsHom hd (Multiplicative.ofAdd (1 : R)) = weylUnit hd hB hr := by
  apply Units.ext
  change (1 + (1 : R) • d) * (1 + (-1 : R) • B) * (1 + (1 : R) • d) = weyl d B
  simpa only [one_smul, neg_one_smul, ← sub_eq_add_neg] using weyl_factorization hd hr

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
