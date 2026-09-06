import Mathlib
import InfoGeometry.Canonical.SupertwistorThreeCliffordBridge

namespace InfoGeometry.Canonical

/-!
# Generational CKM Mixing Bridge

This module formalizes the cyclic permutation operator $S_3$ acting on the three chiral 
color planes. In the context of the Standard Model, this operator is the geometric 
origin of the generation mixing (the Cabibbo-Kobayashi-Maskawa / CKM matrix). 
The operator shifts the color channels $\mathcal{A}_1 \to \mathcal{A}_2 \to \mathcal{A}_3 \to \mathcal{A}_1$.
-/

/-- The cyclic generation shift operator acting on the three chiral sectors. -/
def generational_ckm_shift {K : Type*} (v : ThreeChiralCoordinates K) : ThreeChiralCoordinates K :=
  fun i => v (i + 1)

/-- The inverse shift. -/
def generational_ckm_unshift {K : Type*} (v : ThreeChiralCoordinates K) : ThreeChiralCoordinates K :=
  fun i => v (i - 1)

/-- Theorem: A single shift and unshift is the identity. -/
theorem ckm_shift_unshift_id {K : Type*} (v : ThreeChiralCoordinates K) :
    generational_ckm_shift (generational_ckm_unshift v) = v := by
  ext i j
  simp [generational_ckm_shift, generational_ckm_unshift]

/-- Theorem: A single unshift and shift is the identity. -/
theorem ckm_unshift_shift_id {K : Type*} (v : ThreeChiralCoordinates K) :
    generational_ckm_unshift (generational_ckm_shift v) = v := by
  ext i j
  simp [generational_ckm_shift, generational_ckm_unshift]

/-- Theorem: Applying the generation shift operator 3 times yields the identity (Z_3 cyclic symmetry). -/
theorem ckm_shift_order_three {K : Type*} (v : ThreeChiralCoordinates K) :
    generational_ckm_shift (generational_ckm_shift (generational_ckm_shift v)) = v := by
  ext i j
  change v (i + 1 + 1 + 1) j = v i j
  have h : i + 1 + 1 + 1 = i := by
    fin_cases i <;> decide
  rw [h]

/-- The linear equivalence representing the cyclic Z_3 mixing of the three generations. -/
def generational_ckm_equiv {K : Type*} [CommRing K] : 
    ThreeChiralCoordinates K ≃ₗ[K] ThreeChiralCoordinates K where
  toFun := generational_ckm_shift
  invFun := generational_ckm_unshift
  left_inv := ckm_unshift_shift_id
  right_inv := ckm_shift_unshift_id
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

end InfoGeometry.Canonical
