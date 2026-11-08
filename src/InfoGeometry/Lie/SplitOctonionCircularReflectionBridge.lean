import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CanonicalChiralZornEquivariance
import InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
import InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation

/-!
# Reflection on the circular split-octonion carrier

The existing canonical colour reflection is the multiplication-preserving
reflection of the Zorn algebra.  This file transports it through the already
defined circular coordinate equivalence and records its fixed-point carrier.
It deliberately keeps canonical conjugation separate: that operation reverses
the nonassociative product and is not a multiplicative automorphism.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionCircularReflectionBridge

open InfoGeometry.Canonical
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout
open InfoGeometry.Lie.SplitOctonionPeirceExteriorBridge
open InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation

abbrev Carrier := CanonicalZorn
abbrev Coord := InfoGeometry.Algebra.FiniteSpin.Vec8R

/-! The existing Peirce coordinate carrier is definitionally the circular
coordinate carrier.  We expose its exchange operator here as the sector
exchange used by the circular readout. -/

abbrev circularSectorExchange : Coord →ₗ[ℝ] Coord := chiralExchange

theorem circularSectorExchange_involutive (x : Coord) :
    circularSectorExchange (circularSectorExchange x) = x := by
  exact chiralExchange_sq x

theorem circularSectorExchange_anticommutes_peirceGrading (x : Coord) :
    circularSectorExchange (peirceGrading x) =
      -peirceGrading (circularSectorExchange x) := by
  exact chiralExchange_grading_anticomm x

def circularColorReflection : Coord ≃ₗ[ℝ] Coord :=
  circularCoordinateLinearEquiv.symm.trans
    (canonicalColorReflectionLinearAut.trans circularCoordinateLinearEquiv)

@[simp] theorem circularColorReflection_apply (x : Coord) :
    circularColorReflection x =
      circularCoordinateLinearEquiv
        (canonicalColorReflectionLinearAut
          (circularCoordinateLinearEquiv.symm x)) := rfl

theorem circularColorReflection_involutive (x : Coord) :
    circularColorReflection (circularColorReflection x) = x := by
  rw [circularColorReflection_apply, circularColorReflection_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [show canonicalColorReflectionLinearAut
      (canonicalColorReflectionLinearAut
        (circularCoordinateLinearEquiv.symm x)) =
      circularCoordinateLinearEquiv.symm x by
    change canonicalColorReflection
        (canonicalColorReflection (circularCoordinateLinearEquiv.symm x)) = _
    exact canonicalColorReflection_involutive _]
  exact circularCoordinateLinearEquiv.apply_symm_apply x

theorem circularColorReflection_square :
    circularColorReflection * circularColorReflection =
      (1 : Coord ≃ₗ[ℝ] Coord) := by
  apply LinearEquiv.ext
  intro x
  change circularColorReflection (circularColorReflection x) = x
  exact circularColorReflection_involutive x

theorem circularColorReflection_preserves_multiplication (X Y : Carrier) :
    canonicalColorReflectionLinearAut (X * Y) =
      canonicalColorReflectionLinearAut X *
        canonicalColorReflectionLinearAut Y := by
  change canonicalColorReflection (X * Y) =
    canonicalColorReflection X * canonicalColorReflection Y
  exact canonicalColorReflection_map_mul X Y

/-! Canonical conjugation is a second, distinct reflection operator.  It is
linear and involutive, but reverses the product; recording it explicitly keeps
the anti-automorphism separate from the colour automorphism above. -/

def circularConjugation : Coord →ₗ[ℝ] Coord where
  toFun x := circularCoordinateLinearEquiv
    (canonicalConjLinear (circularCoordinateLinearEquiv.symm x))
  map_add' x y := by
    simpa only [map_add] using congrArg circularCoordinateLinearEquiv
      (canonicalConjLinear.map_add
        (circularCoordinateLinearEquiv.symm x)
        (circularCoordinateLinearEquiv.symm y))
  map_smul' c x := by
    simpa only [RingHom.id_apply, map_smul] using congrArg circularCoordinateLinearEquiv
      (canonicalConjLinear.map_smul c
        (circularCoordinateLinearEquiv.symm x))

@[simp] theorem circularConjugation_apply (x : Coord) :
    circularConjugation x = circularCoordinateLinearEquiv
      (canonicalConjLinear (circularCoordinateLinearEquiv.symm x)) := rfl

theorem circularConjugation_involutive (x : Coord) :
    circularConjugation (circularConjugation x) = x := by
  rw [circularConjugation_apply, circularConjugation_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [show canonicalConjLinear (canonicalConjLinear
      (circularCoordinateLinearEquiv.symm x)) =
      circularCoordinateLinearEquiv.symm x by
    change canonicalConj (canonicalConj (circularCoordinateLinearEquiv.symm x)) = _
    exact canonicalConj_involutive _]
  exact circularCoordinateLinearEquiv.apply_symm_apply x

theorem circularConjugation_reverses_multiplication (X Y : Carrier) :
    canonicalConjLinear (X * Y) =
      canonicalConjLinear Y * canonicalConjLinear X := by
  change canonicalConj (X * Y) = canonicalConj Y * canonicalConj X
  exact canonicalConj_mul X Y

def canonicalConjugationFixed : Submodule ℝ Carrier :=
  LinearMap.ker (canonicalConjLinear - LinearMap.id)

theorem mem_canonicalConjugationFixed_iff (X : Carrier) :
    X ∈ canonicalConjugationFixed ↔ canonicalConjLinear X = X := by
  change (canonicalConjLinear X - X = 0) ↔ _
  rw [sub_eq_zero]

theorem canonicalConjugationFixed_zero :
    (0 : Carrier) ∈ canonicalConjugationFixed := by
  exact (canonicalConjugationFixed : Submodule ℝ Carrier).zero_mem

theorem canonicalConjugationFixed_closed_under_add
    {X Y : Carrier} (hX : X ∈ canonicalConjugationFixed)
    (hY : Y ∈ canonicalConjugationFixed) :
    X + Y ∈ canonicalConjugationFixed := by
  exact (canonicalConjugationFixed : Submodule ℝ Carrier).add_mem hX hY

theorem canonicalConjugationFixed_closed_under_smul
    (c : ℝ) {X : Carrier} (hX : X ∈ canonicalConjugationFixed) :
    c • X ∈ canonicalConjugationFixed := by
  exact (canonicalConjugationFixed : Submodule ℝ Carrier).smul_mem c hX

def circularConjugationFixed : Submodule ℝ Coord :=
  LinearMap.ker (circularConjugation - LinearMap.id)

theorem mem_circularConjugationFixed_iff (x : Coord) :
    x ∈ circularConjugationFixed ↔ circularConjugation x = x := by
  simp [circularConjugationFixed, sub_eq_zero]

theorem circularConjugationFixed_iff_canonicalFixed (x : Coord) :
    x ∈ circularConjugationFixed ↔
      circularCoordinateLinearEquiv.symm x ∈ canonicalConjugationFixed := by
  rw [mem_circularConjugationFixed_iff,
    mem_canonicalConjugationFixed_iff]
  rw [circularConjugation_apply]
  constructor
  · intro h
    apply circularCoordinateLinearEquiv.injective
    simpa using h
  · intro h
    calc
      circularCoordinateLinearEquiv
          (canonicalConjLinear (circularCoordinateLinearEquiv.symm x)) =
          circularCoordinateLinearEquiv
            (circularCoordinateLinearEquiv.symm x) :=
        congrArg circularCoordinateLinearEquiv h
      _ = x := circularCoordinateLinearEquiv.apply_symm_apply x

theorem circularConjugation_intertwines_circularL_R
    (a : Carrier) (x : Coord) :
    circularConjugation (circularL a x) =
      circularR (canonicalConjLinear a)
        (circularConjugation x) := by
  rw [circularConjugation_apply, circularConjugation_apply,
    circularL_apply, circularR_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [circularConjugation_reverses_multiplication]

theorem circularConjugation_intertwines_circularR_L
    (a : Carrier) (x : Coord) :
    circularConjugation (circularR a x) =
      circularL (canonicalConjLinear a) (circularConjugation x) := by
  rw [circularConjugation_apply, circularConjugation_apply,
    circularR_apply, circularL_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [circularConjugation_reverses_multiplication]

theorem circularConjugation_comp_circularL
    (a : Carrier) :
    circularConjugation.comp (circularL a) =
      (circularR (canonicalConjLinear a)).comp circularConjugation := by
  apply LinearMap.ext
  intro x
  exact circularConjugation_intertwines_circularL_R a x

theorem circularConjugation_comp_circularR
    (a : Carrier) :
    circularConjugation.comp (circularR a) =
      (circularL (canonicalConjLinear a)).comp circularConjugation := by
  apply LinearMap.ext
  intro x
  exact circularConjugation_intertwines_circularR_L a x

theorem circularColorReflection_intertwines_circularL
    (a : Carrier) (x : Coord) :
    circularColorReflection (circularL a x) =
      circularL (canonicalColorReflectionLinearAut a)
        (circularColorReflection x) := by
  rw [circularColorReflection_apply, circularColorReflection_apply,
    circularL_apply, circularL_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [circularColorReflection_preserves_multiplication]

theorem circularColorReflection_intertwines_circularR
    (a : Carrier) (x : Coord) :
    circularColorReflection (circularR a x) =
      circularR (canonicalColorReflectionLinearAut a)
        (circularColorReflection x) := by
  rw [circularColorReflection_apply, circularColorReflection_apply,
    circularR_apply, circularR_apply]
  simp only [LinearEquiv.symm_apply_apply]
  rw [circularColorReflection_preserves_multiplication]

theorem circularColorReflection_comp_circularL
    (a : Carrier) :
    circularColorReflection.toLinearMap.comp (circularL a) =
      (circularL (canonicalColorReflectionLinearAut a)).comp
        circularColorReflection.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact circularColorReflection_intertwines_circularL a x

theorem circularColorReflection_comp_circularR
    (a : Carrier) :
    circularColorReflection.toLinearMap.comp (circularR a) =
      (circularR (canonicalColorReflectionLinearAut a)).comp
        circularColorReflection.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact circularColorReflection_intertwines_circularR a x

def canonicalColorReflectionFixed : Submodule ℝ Carrier :=
  LinearMap.ker (canonicalColorReflectionLinearAut.toLinearMap - LinearMap.id)

theorem mem_canonicalColorReflectionFixed_iff (X : Carrier) :
    X ∈ canonicalColorReflectionFixed ↔
      canonicalColorReflectionLinearAut X = X := by
  change (canonicalColorReflectionLinearAut X - X = 0) ↔ _
  rw [sub_eq_zero]

theorem canonicalColorReflectionFixed_mul_closed
    {X Y : Carrier} (hX : X ∈ canonicalColorReflectionFixed)
    (hY : Y ∈ canonicalColorReflectionFixed) :
    X * Y ∈ canonicalColorReflectionFixed := by
  rw [mem_canonicalColorReflectionFixed_iff] at hX hY ⊢
  rw [circularColorReflection_preserves_multiplication, hX, hY]

theorem canonicalColorReflectionFixed_one :
    (1 : Carrier) ∈ canonicalColorReflectionFixed := by
  rw [mem_canonicalColorReflectionFixed_iff]
  change canonicalColorReflection (1 : Carrier) = 1
  simp [canonicalColorReflection, canonicalChiralMulEquiv,
    InfoGeometry.Physics.Octonion.ChiralZornMatrix.reflectMulEquiv_apply,
    InfoGeometry.Physics.Octonion.ChiralZornMatrix.reflect]
  rfl

def circularColorReflectionFixed : Submodule ℝ Coord :=
  LinearMap.ker (circularColorReflection.toLinearMap - LinearMap.id)

theorem mem_circularColorReflectionFixed_iff (x : Coord) :
    x ∈ circularColorReflectionFixed ↔ circularColorReflection x = x := by
  simp [circularColorReflectionFixed, sub_eq_zero]

def circularColorConjugationFixed : Submodule ℝ Coord :=
  circularColorReflectionFixed ⊓ circularConjugationFixed

theorem circularColorConjugationFixed_le_color :
    circularColorConjugationFixed ≤ circularColorReflectionFixed := by
  exact inf_le_left

theorem circularColorConjugationFixed_le_conjugation :
    circularColorConjugationFixed ≤ circularConjugationFixed := by
  exact inf_le_right

theorem mem_circularColorConjugationFixed_iff (x : Coord) :
    x ∈ circularColorConjugationFixed ↔
      circularColorReflection x = x ∧ circularConjugation x = x := by
  change (x ∈ circularColorReflectionFixed ∧
    x ∈ circularConjugationFixed) ↔ _
  rw [mem_circularColorReflectionFixed_iff, mem_circularConjugationFixed_iff]

theorem circularFixed_iff_canonicalFixed (x : Coord) :
    x ∈ circularColorReflectionFixed ↔
      circularCoordinateLinearEquiv.symm x ∈ canonicalColorReflectionFixed := by
  rw [mem_circularColorReflectionFixed_iff,
    mem_canonicalColorReflectionFixed_iff]
  rw [circularColorReflection_apply]
  constructor
  · intro h
    apply circularCoordinateLinearEquiv.injective
    simpa using h
  · intro h
    calc
      circularCoordinateLinearEquiv
          (canonicalColorReflectionLinearAut
            (circularCoordinateLinearEquiv.symm x)) =
          circularCoordinateLinearEquiv
            (circularCoordinateLinearEquiv.symm x) :=
        congrArg circularCoordinateLinearEquiv h
      _ = x := circularCoordinateLinearEquiv.apply_symm_apply x

def circularSectorExchangeFixed : Submodule ℝ Coord :=
  LinearMap.ker (circularSectorExchange - LinearMap.id)

theorem mem_circularSectorExchangeFixed_iff (x : Coord) :
    x ∈ circularSectorExchangeFixed ↔ circularSectorExchange x = x := by
  simp [circularSectorExchangeFixed, sub_eq_zero]

def circularCommonFixed : Submodule ℝ Coord :=
  circularColorReflectionFixed ⊓ circularSectorExchangeFixed

theorem circularCommonFixed_le_reflectionFixed :
    circularCommonFixed ≤ circularColorReflectionFixed := by
  exact inf_le_left

theorem circularCommonFixed_le_sectorExchangeFixed :
    circularCommonFixed ≤ circularSectorExchangeFixed := by
  exact inf_le_right

theorem mem_circularCommonFixed_iff (x : Coord) :
    x ∈ circularCommonFixed ↔
      circularColorReflection x = x ∧ circularSectorExchange x = x := by
  change (x ∈ circularColorReflectionFixed ∧
    x ∈ circularSectorExchangeFixed) ↔ _
  rw [mem_circularColorReflectionFixed_iff,
    mem_circularSectorExchangeFixed_iff]

theorem circularColorReflectionFixed_zero :
    (0 : Coord) ∈ circularColorReflectionFixed := by
  exact (circularColorReflectionFixed : Submodule ℝ Coord).zero_mem

theorem circularColorReflectionFixed_closed_under_add
    {x y : Coord} (hx : x ∈ circularColorReflectionFixed)
    (hy : y ∈ circularColorReflectionFixed) :
    x + y ∈ circularColorReflectionFixed := by
  exact (circularColorReflectionFixed : Submodule ℝ Coord).add_mem hx hy

theorem circularColorReflectionFixed_closed_under_smul
    (c : ℝ) {x : Coord} (hx : x ∈ circularColorReflectionFixed) :
    c • x ∈ circularColorReflectionFixed := by
  exact (circularColorReflectionFixed : Submodule ℝ Coord).smul_mem c hx

theorem circularSectorExchangeFixed_zero :
    (0 : Coord) ∈ circularSectorExchangeFixed := by
  exact (circularSectorExchangeFixed : Submodule ℝ Coord).zero_mem

theorem circularSectorExchangeFixed_closed_under_add
    {x y : Coord} (hx : x ∈ circularSectorExchangeFixed)
    (hy : y ∈ circularSectorExchangeFixed) :
    x + y ∈ circularSectorExchangeFixed := by
  exact (circularSectorExchangeFixed : Submodule ℝ Coord).add_mem hx hy

theorem circularSectorExchangeFixed_closed_under_smul
    (c : ℝ) {x : Coord} (hx : x ∈ circularSectorExchangeFixed) :
    c • x ∈ circularSectorExchangeFixed := by
  exact (circularSectorExchangeFixed : Submodule ℝ Coord).smul_mem c hx

theorem circularCommonFixed_closed_under_add
    {x y : Coord} (hx : x ∈ circularCommonFixed)
    (hy : y ∈ circularCommonFixed) :
    x + y ∈ circularCommonFixed := by
  exact (circularCommonFixed : Submodule ℝ Coord).add_mem hx hy

theorem circularCommonFixed_closed_under_smul
    (c : ℝ) {x : Coord} (hx : x ∈ circularCommonFixed) :
    c • x ∈ circularCommonFixed := by
  exact (circularCommonFixed : Submodule ℝ Coord).smul_mem c hx

end InfoGeometry.Lie.SplitOctonionCircularReflectionBridge
