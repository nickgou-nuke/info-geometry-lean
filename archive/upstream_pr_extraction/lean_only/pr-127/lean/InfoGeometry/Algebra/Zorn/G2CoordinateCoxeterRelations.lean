/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
import InfoGeometry.Algebra.Zorn.G2ZModCoercionLemmas

/-!
# Coxeter relations on the concrete full-root permutation carrier

These are relations of the actual coordinate permutations.  They are kept
separate from the cyclotomic carrier because that carrier is not
equivariantly calibrated to the concrete G₂ reflections.
-/

namespace InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction

theorem coordinate_c_pow_six : cRoot ^ 6 = 1 := cRoot_pow_six

theorem coordinate_s1_sq : s1Root ^ 2 = 1 := s1Root_sq

theorem coordinate_s2_sq : s2Root ^ 2 = 1 := s2Root_sq

theorem coordinate_s1_conj_c :
    s1Root * cRoot * s1Root = cRoot⁻¹ := by
  decide

theorem coordinate_s1_conj_c_pow (n : ℕ) :
    s1Root * cRoot ^ n * s1Root = (cRoot⁻¹) ^ n := by
  have hs : s1Root⁻¹ = s1Root := by
    have hsquare : s1Root * s1Root = 1 := by
      simpa [pow_two] using coordinate_s1_sq
    calc
      s1Root⁻¹ = s1Root⁻¹ * 1 := by simp
      _ = s1Root⁻¹ * (s1Root * s1Root) := by rw [hsquare]
      _ = (s1Root⁻¹ * s1Root) * s1Root := by rw [mul_assoc]
      _ = s1Root := by simp
  simpa only [hs, coordinate_s1_conj_c] using
    (conj_pow (a := s1Root) (b := cRoot) (i := n)).symm

theorem coordinate_s1_conj_c_inv_pow (n : ℕ) :
    s1Root * (cRoot⁻¹) ^ n * s1Root = cRoot ^ n := by
  have hs : s1Root⁻¹ = s1Root := by
    have hsquare : s1Root * s1Root = 1 := by
      simpa [pow_two] using coordinate_s1_sq
    calc
      s1Root⁻¹ = s1Root⁻¹ * 1 := by simp
      _ = s1Root⁻¹ * (s1Root * s1Root) := by rw [hsquare]
      _ = (s1Root⁻¹ * s1Root) * s1Root := by rw [mul_assoc]
      _ = s1Root := by simp
  have h : s1Root * cRoot⁻¹ * s1Root = cRoot := by
    have hinv := congrArg Inv.inv coordinate_s1_conj_c
    simpa [mul_assoc] using hinv
  simpa only [hs, h] using
    (conj_pow (a := s1Root) (b := cRoot⁻¹) (i := n)).symm

theorem coordinate_s1_mul_c_pow (n : ℕ) :
    s1Root * cRoot ^ n = (cRoot⁻¹) ^ n * s1Root := by
  calc
    s1Root * cRoot ^ n =
        (s1Root * cRoot ^ n * s1Root) * s1Root := by
          have hsquare : s1Root * s1Root = 1 := by
            simpa [pow_two] using coordinate_s1_sq
          simp [mul_assoc, hsquare]
    _ = (cRoot⁻¹) ^ n * s1Root := by
      rw [coordinate_s1_conj_c_pow]

theorem coordinate_s1_mul_c_inv_pow (n : ℕ) :
    s1Root * (cRoot⁻¹) ^ n = cRoot ^ n * s1Root := by
  calc
    s1Root * (cRoot⁻¹) ^ n =
        (s1Root * (cRoot⁻¹) ^ n * s1Root) * s1Root := by
          have hsquare : s1Root * s1Root = 1 := by
            simpa [pow_two] using coordinate_s1_sq
          simp [mul_assoc, hsquare]
    _ = cRoot ^ n * s1Root := by
      rw [coordinate_s1_conj_c_inv_pow]

theorem coordinate_c_pow_mod (n : ℕ) :
    cRoot ^ (n % 6) = cRoot ^ n := by
  symm
  exact pow_eq_pow_mod n coordinate_c_pow_six

theorem coordinate_c_inv_pow_mod (n : ℕ) :
    (cRoot ^ n)⁻¹ = cRoot ^ ((6 - n % 6) % 6) := by
  apply inv_eq_of_mul_eq_one_right
  by_cases h : n % 6 = 0
  · rw [← coordinate_c_pow_mod n, h]
    simp
  · have hsum : n % 6 + (6 - n % 6) % 6 = 6 := by omega
    calc
      cRoot ^ n * cRoot ^ ((6 - n % 6) % 6) =
          cRoot ^ (n % 6) * cRoot ^ (6 - n % 6) := by
            rw [coordinate_c_pow_mod n]
            rw [coordinate_c_pow_mod (6 - n % 6)]
      _ = cRoot ^ (n % 6 + (6 - n % 6)) := by rw [pow_add]
      _ = cRoot ^ 6 := by
        congr 1
        omega
      _ = 1 := coordinate_c_pow_six

theorem coordinate_c_pow_zmod_add (k l : ZMod 6) :
    cRoot ^ (k + l).val = cRoot ^ k.val * cRoot ^ l.val := by
  calc
    cRoot ^ (k + l).val = cRoot ^ ((k.val + l.val) % 6) := by
      congr 1
    _ = cRoot ^ (k.val + l.val) :=
      coordinate_c_pow_mod (k.val + l.val)
    _ = cRoot ^ k.val * cRoot ^ l.val := by rw [pow_add]

theorem coordinate_c_pow_zmod_sub (k l : ZMod 6) :
    cRoot ^ (l - k).val = cRoot ^ l.val * (cRoot ^ k.val)⁻¹ := by
  rw [coordinate_c_inv_pow_mod k.val, ← pow_add]
  have hcast : l - k =
      (l.val + (6 - k.val) % 6 : ℕ) := by
    rw [← ZMod.natCast_zmod_val l, ← ZMod.natCast_zmod_val k]
    simp only [ZMod.val_natCast]
    simp only [Nat.cast_add]
    rw [ZMod.natCast_mod]
    have hk : k.val % 6 = k.val := Nat.mod_eq_of_lt k.isLt
    rw [hk]
    rw [G2ZModCoercionLemmas.natCast_sub_mod_six]
    simp only [sub_eq_add_neg]
    rw [← ZMod.natCast_zmod_val k]
    simp only [ZMod.val_natCast]
    rw [hk]
  have hmod : (l - k).val ≡
      l.val + (6 - k.val % 6) % 6 [MOD 6] := by
    have hcast' : l - k =
        ((l.val + (6 - k.val % 6) % 6 : ℕ) : ZMod 6) := by
      rw [hcast]
      congr 1
      have hk : k.val % 6 = k.val := Nat.mod_eq_of_lt k.isLt
      simp [hk]
    apply (ZMod.natCast_eq_natCast_iff _ _ 6).mp
    rw [ZMod.natCast_zmod_val]
    exact hcast'
  exact pow_eq_pow_of_modEq hmod coordinate_c_pow_six

end InfoGeometry.Algebra.Zorn.G2CoordinateCoxeterRelations
