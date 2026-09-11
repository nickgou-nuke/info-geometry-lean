import Mathlib.Data.ZMod.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinNativeSemidirectProductBridge

/-!
# Orientation character of the native Klein semidirect product

The projection to the acting copy of `Multiplicative ℤ`, followed by reduction
modulo two, is the algebraic orientation character.  This owner proves the
homomorphism and its values on the canonical translation and glide.  It does
not identify its kernel with a topological fundamental-group cover.
-/

noncomputable section

namespace InfoGeometry.Canonical.KleinOrientationCharacterBridge

open InfoGeometry.Canonical.KleinNativeSemidirectProductBridge

abbrev OrientationTarget := Multiplicative (ZMod 2)

def parityHom : Multiplicative ℤ →* OrientationTarget :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))

def orientationCharacter : NativeKleinSemidirect →* OrientationTarget :=
  parityHom.comp SemidirectProduct.rightHom

@[simp] theorem orientationCharacter_inl (n : Multiplicative ℤ) :
    orientationCharacter (SemidirectProduct.inl n) = 1 := by
  simp [orientationCharacter]

@[simp] theorem orientationCharacter_inr (g : Multiplicative ℤ) :
    orientationCharacter (SemidirectProduct.inr g) = parityHom g := by
  simp [orientationCharacter]

theorem orientationCharacter_translation :
    orientationCharacter nativeKleinTranslation = 1 := by
  simp [nativeKleinTranslation]

theorem orientationCharacter_glide :
    orientationCharacter nativeKleinGlide =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  simp [nativeKleinGlide, orientationCharacter, parityHom]

theorem orientationCharacter_glide_sq :
    orientationCharacter (nativeKleinGlide ^ 2) = 1 := by
  rw [map_pow, orientationCharacter_glide]
  decide

/--
The kernel of the orientation character is exactly the even-parity sector of
the acting semidirect coordinate.  This is an algebraic kernel statement only
and does not identify it with a topological covering space.
-/
theorem orientationCharacter_eq_one_iff_right_coordinate_mod_two_zero
    (x : NativeKleinSemidirect) :
    orientationCharacter x = 1 ↔
      (x.right.toAdd : ZMod 2) = 0 := by
  change parityHom x.right = 1 ↔ _
  change Multiplicative.ofAdd (x.right.toAdd : ZMod 2) = 1 ↔ _
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simpa using h'
  · intro h
    apply Multiplicative.ext
    simpa using h

theorem mem_orientationCharacter_ker_iff_right_coordinate_mod_two_zero
    (x : NativeKleinSemidirect) :
    x ∈ orientationCharacter.ker ↔
      (x.right.toAdd : ZMod 2) = 0 := by
  change orientationCharacter x = 1 ↔ _
  exact orientationCharacter_eq_one_iff_right_coordinate_mod_two_zero x

theorem inl_mem_orientationCharacter_ker (n : Multiplicative ℤ) :
    SemidirectProduct.inl n ∈ orientationCharacter.ker := by
  rw [mem_orientationCharacter_ker_iff_right_coordinate_mod_two_zero]
  simp

theorem inr_mem_orientationCharacter_ker_iff_even (n : Multiplicative ℤ) :
    SemidirectProduct.inr n ∈ orientationCharacter.ker ↔
      Even n.toAdd := by
  rw [mem_orientationCharacter_ker_iff_right_coordinate_mod_two_zero]
  change (n.toAdd : ZMod 2) = 0 ↔ Even n.toAdd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    exact Int.even_iff.mpr ((Int.dvd_iff_emod_eq_zero.mp h))
  · intro h
    exact Int.dvd_iff_emod_eq_zero.mpr (Int.even_iff.mp h)

theorem nativeKlein_mem_center_iff_left_eq_zero_and_orientation_one
    (x : NativeKleinSemidirect) :
    x ∈ Subgroup.center NativeKleinSemidirect ↔
      x.left = Multiplicative.ofAdd 0 ∧ orientationCharacter x = 1 := by
  constructor
  · intro hx
    have hcenter := (nativeKlein_mem_center_iff x).mp hx
    refine ⟨hcenter.1, ?_⟩
    rw [orientationCharacter_eq_one_iff_right_coordinate_mod_two_zero]
    have hact : integerInversionAction x.right = 1 := by
      ext a
      simpa using hcenter.2 a
    have heven : Even x.right.toAdd :=
      (integerInversionAction_ofAdd_eq_one_iff_even x.right.toAdd).mp hact
    have hmodZ : x.right.toAdd % 2 = 0 := Int.even_iff.mp heven
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd x.right.toAdd 2).2
    exact (Int.dvd_iff_emod_eq_zero).2 hmodZ
  · rintro ⟨hleft, hchar⟩
    apply (nativeKlein_mem_center_iff x).mpr
    refine ⟨hleft, ?_⟩
    have hmod : (x.right.toAdd : ZMod 2) = 0 :=
      (orientationCharacter_eq_one_iff_right_coordinate_mod_two_zero x).mp hchar
    have hmodZ : x.right.toAdd % 2 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd x.right.toAdd 2).1
      exact hmod
    have heven : Even x.right.toAdd := Int.even_iff.mpr hmodZ
    have hact : integerInversionAction x.right = 1 := by
      change integerInversionAction (Multiplicative.ofAdd x.right.toAdd) = 1
      exact (integerInversionAction_ofAdd_eq_one_iff_even x.right.toAdd).mpr heven
    intro a
    exact congrArg (fun u : MulAut (Multiplicative ℤ) => u a) hact

theorem nativeKlein_mem_center_iff_glide_square_zpow
    (x : NativeKleinSemidirect) :
    x ∈ Subgroup.center NativeKleinSemidirect ↔
      ∃ k : ℤ, x = (nativeKleinGlide ^ 2) ^ k := by
  constructor
  · intro hx
    have hcenter :=
      (nativeKlein_mem_center_iff_left_eq_zero_and_orientation_one x).mp hx
    have hmod : (x.right.toAdd : ZMod 2) = 0 :=
      (orientationCharacter_eq_one_iff_right_coordinate_mod_two_zero x).mp
        hcenter.2
    have hmodZ : x.right.toAdd % 2 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd x.right.toAdd 2).1
      exact hmod
    have heven : Even x.right.toAdd := Int.even_iff.mpr hmodZ
    obtain ⟨k, hk⟩ := heven
    refine ⟨k, ?_⟩
    calc
      x = SemidirectProduct.inr x.right := by
        apply SemidirectProduct.ext
        · rw [hcenter.1]
          simp
        · rfl
      _ = SemidirectProduct.inr (Multiplicative.ofAdd (2 * k)) := by
        have hr : x.right = Multiplicative.ofAdd (k + k) := by
          apply Multiplicative.ext
          simpa using hk
        rw [hr]
        congr 1
        ring
      _ = (nativeKleinGlide ^ 2) ^ k :=
        (nativeKlein_glide_square_zpow_eq_inr k).symm
  · rintro ⟨k, rfl⟩
    have hc : nativeKleinGlide ^ 2 ∈ Subgroup.center NativeKleinSemidirect :=
      nativeKlein_glide_square_mem_center
    exact Subgroup.zpow_mem (Subgroup.center NativeKleinSemidirect) hc k

end InfoGeometry.Canonical.KleinOrientationCharacterBridge
