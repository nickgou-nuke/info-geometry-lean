import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Basic
import InfoGeometry.Volume.Base

/-!
# Scale and sign of nonzero real scalars

The determinant of a real linear equivalence lands in `ℝˣ`. This file splits
that scalar character into its positive absolute value and its sign. It does
not add a universal chiral phase: such a character needs extra geometric or
representation data.
-/

namespace InfoGeometry.Volume.RealUnitScaleParity

open SignType

/-- Absolute value as a multiplicative endomorphism of the real unit group. -/
noncomputable def absUnits : ℝˣ →* ℝˣ where
  toFun u := Units.mk0 |(u : ℝ)| (abs_ne_zero.mpr u.ne_zero)
  map_one' := by
    apply Units.ext
    simp
  map_mul' u v := by
    apply Units.ext
    simp [abs_mul]

/-- The sign of a real unit, packaged as a unit of `SignType`. -/
noncomputable def signUnits : ℝˣ →* SignTypeˣ :=
  Units.map signHom.toMonoidHom

/-- The positive scale component of a real unit. -/
noncomputable def scaleComponent (u : ℝˣ) : Units.posSubgroup ℝ :=
  ⟨absUnits u, by
    change 0 < |(u : ℝ)|
    exact abs_pos.mpr u.ne_zero⟩

/-- The scale/sign homomorphism on nonzero real scalars. -/
noncomputable def scaleParityHom : ℝˣ →* Units.posSubgroup ℝ × SignTypeˣ where
  toFun u := (scaleComponent u, signUnits u)
  map_one' := by
    apply Prod.ext
    · apply Subtype.ext
      apply Units.ext
      simp [scaleComponent, absUnits]
    · apply Units.ext
      simp [signUnits]
  map_mul' u v := by
    apply Prod.ext
    · apply Subtype.ext
      apply Units.ext
      simp [scaleComponent, absUnits, abs_mul]
    · apply Units.ext
      simp [signUnits]

/-- Convert the `SignType` unit back to a real unit. -/
noncomputable def signToReal : SignTypeˣ →* ℝˣ :=
  Units.map SignType.castHom.toMonoidHom

/-- Reconstruct a real unit from its positive scale and sign. -/
noncomputable def scaleParityInv
    (p : Units.posSubgroup ℝ × SignTypeˣ) : ℝˣ :=
  p.1.1 * signToReal p.2

/-- The positive scale and sign recover every nonzero real scalar. -/
theorem scaleParityInv_left (u : ℝˣ) :
    scaleParityInv (scaleParityHom u) = u := by
  apply Units.ext
  change |(u : ℝ)| *
      (SignType.castHom (SignType.sign (u : ℝ))) = (u : ℝ)
  rw [mul_comm]
  exact sign_mul_abs (u : ℝ)

/-- A positive scale and a nonzero sign determine their real unit uniquely. -/
theorem scaleParityInv_right (p : Units.posSubgroup ℝ × SignTypeˣ) :
    scaleParityHom (scaleParityInv p) = p := by
  rcases p with ⟨⟨r, hr⟩, s⟩
  rcases s with ⟨s, sinv, hs₁, hs₂⟩
  have hrpos : 0 < (r : ℝ) := hr
  cases s with
  | zero => simp at hs₁
  | neg =>
      apply Prod.ext
      · apply Subtype.ext
        apply Units.ext
        change |(r : ℝ) * (-1 : ℝ)| = (r : ℝ)
        rw [mul_neg_one, abs_neg, abs_of_pos hrpos]
      · apply Units.ext
        dsimp [scaleParityHom, scaleParityInv, signUnits, signToReal]
        change sign ((r : ℝ) * (-1 : ℝ)) = -1
        rw [mul_neg_one]
        exact sign_neg (neg_neg_of_pos hrpos)
  | pos =>
      apply Prod.ext
      · apply Subtype.ext
        apply Units.ext
        change |(r : ℝ) * (1 : ℝ)| = (r : ℝ)
        rw [mul_one, abs_of_pos hrpos]
      · apply Units.ext
        dsimp [scaleParityHom, scaleParityInv, signUnits, signToReal]
        change sign ((r : ℝ) * (1 : ℝ)) = 1
        rw [mul_one]
        exact sign_pos hrpos

/-- Canonical multiplicative scale/sign decomposition of the nonzero reals. -/
noncomputable def scaleParityEquiv :
    ℝˣ ≃* Units.posSubgroup ℝ × SignTypeˣ where
  toFun := scaleParityHom
  invFun := scaleParityInv
  left_inv := scaleParityInv_left
  right_inv := scaleParityInv_right
  map_mul' := scaleParityHom.map_mul

/-- The negative sign as a unit of `SignType`. -/
def negativeSignUnit : SignTypeˣ := Units.mk0 neg (by decide)

/-- The two nonzero sign values form the cyclic group of order two. -/
noncomputable def signTypeUnitEquivZModTwo :
    SignTypeˣ ≃* Multiplicative (ZMod 2) where
  toFun s := if s.val = pos then 1 else Multiplicative.ofAdd 1
  invFun z := if z.toAdd = 0 then 1 else negativeSignUnit
  left_inv s := by
    rcases s with ⟨s, sinv, hs₁, hs₂⟩
    cases s with
    | zero => simp at hs₁
    | neg =>
        simp [negativeSignUnit]
        apply Units.ext
        rfl
    | pos =>
        simp
        apply Units.ext
        rfl
  right_inv z := by
    fin_cases z <;> simp [negativeSignUnit]
  map_mul' s t := by
    rcases s with ⟨s, sinv, hs₁, hs₂⟩
    rcases t with ⟨t, tinv, ht₁, ht₂⟩
    cases s <;> cases t <;>
      simp_all [zero_eq_zero]
    all_goals try contradiction
    all_goals
      rw [← ofAdd_add]
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [h11]
      simp

/-- The full real scalar determinant character splits as positive scale times
the cyclic parity group `Z₂`. -/
noncomputable def realUnitScaleParityEquiv :
    ℝˣ ≃* Units.posSubgroup ℝ × Multiplicative (ZMod 2) :=
  scaleParityEquiv.trans
    (MulEquiv.prodCongr (MulEquiv.refl (Units.posSubgroup ℝ))
      signTypeUnitEquivZModTwo)

/-- The determinant character of real linear automorphisms, split into its
positive scale and orientation sign. -/
noncomputable def determinantScaleParityHom {V : Type*}
    [AddCommGroup V] [Module ℝ V] :
    (V ≃ₗ[ℝ] V) →* Units.posSubgroup ℝ × Multiplicative (ZMod 2) :=
  realUnitScaleParityEquiv.toMonoidHom.comp Base.VolumeHom

/-- The determinant scale/sign character has precisely the determinant-one
automorphisms as its kernel. Thus the two output coordinates together retain
exactly the information in the real volume character. -/
theorem determinantScaleParityHom_eq_one_iff {V : Type*}
    [AddCommGroup V] [Module ℝ V] (f : V ≃ₗ[ℝ] V) :
    determinantScaleParityHom f = 1 ↔ Base.VolumeHom f = 1 := by
  constructor
  · intro h
    apply realUnitScaleParityEquiv.injective
    simpa [determinantScaleParityHom] using h
  · intro h
    simp [determinantScaleParityHom, h]

end InfoGeometry.Volume.RealUnitScaleParity
