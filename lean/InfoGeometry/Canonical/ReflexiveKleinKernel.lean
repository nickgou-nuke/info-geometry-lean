/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ReflexiveKleinRepresentation
import InfoGeometry.Canonical.KleinNativeSemidirectProductBridge

/-!
# A genuine kernel obstruction for the reflexive-pair Klein representation

The abstract glide has infinite order, as detected by the right coordinate
of the existing native semidirect-product realization. Its image in the
reflexive-pair representation has fourth power one. Thus this representation
is never faithful; satisfying the Klein relation does not identify its image
with the presented group or an affine deck group.
-/

namespace InfoGeometry.Canonical.KleinPresentedGroup

open KleinNativeSemidirectProductBridge

/-- The integer glide coordinate separates all powers of the presented glide. -/
theorem glide_zpow_eq_one_iff (n : ℤ) :
    (toKlein genA) ^ n = 1 ↔ n = 0 := by
  constructor
  · intro h
    have he := congrArg nativeKleinPresentationRep h
    rw [map_zpow, nativeKleinPresentationRep_generators.1, map_one] at he
    have hh := congrArg
      (SemidirectProduct.rightHom : NativeKleinSemidirect →* Multiplicative ℤ) he
    rw [map_zpow, map_one] at hh
    change (Multiplicative.ofAdd (1 : ℤ)) ^ n = 1 at hh
    simpa using congrArg Multiplicative.toAdd hh
  · rintro rfl
    exact zpow_zero _

end InfoGeometry.Canonical.KleinPresentedGroup

namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows

open KleinPresentedGroup

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {d B : A} (hd : d * d = 0) (hB : B * B = 0)
  (hr : d * B * d = d) (hs : B * d * B = B)

/-- An explicit nonidentity element of the kernel, for every scalar unit. -/
theorem reflexiveKleinRep_nontrivial_kernel (t : Rˣ) :
    (toKlein genA) ^ (4 : ℕ) ≠ 1 ∧
      (toKlein genA) ^ (4 : ℕ) ∈ (reflexiveKleinRep hd hB hr hs t).ker := by
  constructor
  · intro h
    have hz := (glide_zpow_eq_one_iff 4).mp (by simpa using h)
    norm_num at hz
  · exact reflexiveKleinRep_genA_fourth hd hB hr hs t

/-- No choice of reflexive pair or invertible scalar makes this representation faithful. -/
theorem reflexiveKleinRep_not_injective (t : Rˣ) :
    ¬ Function.Injective (reflexiveKleinRep hd hB hr hs t) := by
  intro hi
  obtain ⟨hne, hker⟩ := reflexiveKleinRep_nontrivial_kernel hd hB hr hs t
  exact hne (hi (hker.trans (map_one _).symm))

end InfoGeometry.Canonical.ReflexiveNilpotentFlows
