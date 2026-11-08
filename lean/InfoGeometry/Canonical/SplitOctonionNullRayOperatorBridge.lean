/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.SplitOctonionNullConeProjectiveTopology
import InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge

/-!
# Projective upper and lower null rays as regular multiplication operators

The upper and lower off-diagonal null branches are sent to endomorphisms of
the explicit real Zorn carrier by left regular multiplication.  The source
Zorn matrix and the operator carrier have distinct Lean representations, so
`splitZornToRegularCarrier` records their coordinate identification.  This
map is used to transport the branch representatives, and their left-regular
operators are compatible with scalar rescaling.  No multiplicativity of the
regular action is asserted.
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Physics.ZornMatrixSU3
open InfoGeometry.Canonical.ZornVectorMatrixExplicit
open InfoGeometry.Canonical.ZornRealRegularMultiplicationSpectralBridge
open InfoGeometry.OperatorAlgebra.KreinIsotropicCone

abbrev SplitZornRegularOperator := Module.End ℝ ZornCoord

def splitZornToRegularCarrier (X : SplitZornMatrix) : ZornCoord :=
  zornMk X.a X.b X.x X.y

theorem upperNull_smul (r : ℝ) (u : Fin 3 → ℝ) :
    upperNull (r • u) = r • upperNull u := by
  apply InfoGeometry.Physics.ZornMatrixSU3.ext <;>
    simp [upperNull]

theorem lowerNull_smul (r : ℝ) (u : Fin 3 → ℝ) :
    lowerNull (r • u) = r • lowerNull u := by
  apply InfoGeometry.Physics.ZornMatrixSU3.ext <;>
    simp [lowerNull]

def splitZornLeftRegular (X : SplitZornMatrix) : SplitZornRegularOperator :=
  leftRegular (splitZornToRegularCarrier X)

theorem splitZornLeftRegular_smul (r : ℝ) (X : SplitZornMatrix) :
    splitZornLeftRegular (r • X) = r • splitZornLeftRegular X := by
  apply LinearMap.ext
  intro Y
  change zornMul (r • splitZornToRegularCarrier X) Y =
    r • zornMul (splitZornToRegularCarrier X) Y
  exact zornMul_smul_left r (splitZornToRegularCarrier X) Y

theorem splitZornLeftRegular_injective :
    Function.Injective splitZornLeftRegular := by
  intro X Y h
  have hOne := congrArg (fun T : SplitZornRegularOperator => T zornOne) h
  have hCoord : splitZornToRegularCarrier X = splitZornToRegularCarrier Y := by
    simpa [splitZornLeftRegular, leftRegular_apply,
      zornMul_one_right] using hOne
  cases X with
  | mk a b x y =>
    cases Y with
    | mk a' b' x' y' =>
      simp [splitZornToRegularCarrier, zornMk] at hCoord
      simp [hCoord]

theorem leftRegular_comp_eq_zero_of_mul_self_eq_zero
    (X : ZornCoord) (hX : zornMul X X = 0) :
    (leftRegular X).comp (leftRegular X) = 0 := by
  apply LinearMap.ext
  intro Y
  change zornMul X (zornMul X Y) = 0
  rw [zornMul_left_alternative, hX, zornMul_zero_left]

abbrev SplitZornNilpotentOperatorRayRep :=
  {T : SplitZornRegularOperator // T ≠ 0 ∧ T.comp T = 0}

instance splitZornOperatorRaySetoid : Setoid SplitZornNilpotentOperatorRayRep where
  r X Y := SameProjectiveRay X.1 Y.1
  iseqv := {
    refl := fun X => SameProjectiveRay.refl X.1
    symm := fun h => SameProjectiveRay.symm h
    trans := fun hXY hYZ => SameProjectiveRay.trans hXY hYZ }

abbrev SplitZornNilpotentOperatorRay :=
  Quotient splitZornOperatorRaySetoid

def splitZornOperatorRayProjection :
    SplitZornNilpotentOperatorRayRep → SplitZornNilpotentOperatorRay :=
  Quotient.mk'

theorem splitZornOperatorRayProjection_eq_iff
    (X Y : SplitZornNilpotentOperatorRayRep) :
    splitZornOperatorRayProjection X = splitZornOperatorRayProjection Y ↔
      SameProjectiveRay X.1 Y.1 := by
  change Quotient.mk' X = Quotient.mk' Y ↔ _
  exact Quotient.eq_iff_equiv

def upperNullOperatorRepresentative
    (u : {u : Fin 3 → ℝ // u ≠ 0}) : SplitZornNilpotentOperatorRayRep := by
  let X : SplitZornMatrix := upperNull u.1
  have hX : splitZornToRegularCarrier X = upperVectorZorn u.1 := by
    rfl
  refine ⟨splitZornLeftRegular X, ?_, ?_⟩
  · intro hzero
    apply u.2
    have hval := congrArg (fun T : SplitZornRegularOperator => T zornOne) hzero
    have hcoord : splitZornToRegularCarrier X = 0 := by
      simpa [splitZornLeftRegular, leftRegular_apply,
        zornMul_one_right] using hval
    have hu : upperVectorZorn u.1 = 0 := by simpa [hX] using hcoord
    have hx := congrArg zornX hu
    simpa [upperVectorZorn, zornMk, zornX] using hx
  · change leftRegular (splitZornToRegularCarrier X) ∘ₗ
      leftRegular (splitZornToRegularCarrier X) = 0
    rw [hX]
    exact leftRegular_comp_eq_zero_of_mul_self_eq_zero
      (upperVectorZorn u.1) (upperVectorZorn_square_zero u.1)

def lowerNullOperatorRepresentative
    (u : {u : Fin 3 → ℝ // u ≠ 0}) : SplitZornNilpotentOperatorRayRep := by
  let X : SplitZornMatrix := lowerNull u.1
  have hX : splitZornToRegularCarrier X = lowerVectorZorn u.1 := by
    rfl
  refine ⟨splitZornLeftRegular X, ?_, ?_⟩
  · intro hzero
    apply u.2
    have hval := congrArg (fun T : SplitZornRegularOperator => T zornOne) hzero
    have hcoord : splitZornToRegularCarrier X = 0 := by
      simpa [splitZornLeftRegular, leftRegular_apply,
        zornMul_one_right] using hval
    have hu : lowerVectorZorn u.1 = 0 := by simpa [hX] using hcoord
    have hy := congrArg zornY hu
    simpa [lowerVectorZorn, zornMk, zornY] using hy
  · change leftRegular (splitZornToRegularCarrier X) ∘ₗ
      leftRegular (splitZornToRegularCarrier X) = 0
    rw [hX]
    exact leftRegular_comp_eq_zero_of_mul_self_eq_zero
      (lowerVectorZorn u.1) (lowerVectorZorn_square_zero u.1)

def upperNullOperatorRay
    (u : {u : Fin 3 → ℝ // u ≠ 0}) : SplitZornNilpotentOperatorRay :=
  splitZornOperatorRayProjection (upperNullOperatorRepresentative u)

def lowerNullOperatorRay
    (u : {u : Fin 3 → ℝ // u ≠ 0}) : SplitZornNilpotentOperatorRay :=
  splitZornOperatorRayProjection (lowerNullOperatorRepresentative u)

theorem upperNullOperatorRay_eq_iff (u v : {u : Fin 3 → ℝ // u ≠ 0}) :
    upperNullOperatorRay u = upperNullOperatorRay v ↔
      ∃ r : ℝ, r ≠ 0 ∧ v.1 = r • u.1 := by
  change splitZornOperatorRayProjection (upperNullOperatorRepresentative u) =
    splitZornOperatorRayProjection (upperNullOperatorRepresentative v) ↔ _
  rw [splitZornOperatorRayProjection_eq_iff]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    change splitZornLeftRegular (upperNull v.1) =
      r • splitZornLeftRegular (upperNull u.1) at h
    rw [← splitZornLeftRegular_smul] at h
    have hvu := splitZornLeftRegular_injective h
    have hx := congrArg (fun Z : SplitZornMatrix => Z.x) hvu
    simpa [upperNull_smul, upperNull] using hx
  · rintro ⟨r, hr, hv⟩
    refine ⟨r, hr, ?_⟩
    change splitZornLeftRegular (upperNull v.1) =
      r • splitZornLeftRegular (upperNull u.1)
    rw [hv]
    rw [upperNull_smul]
    rw [← splitZornLeftRegular_smul]

theorem lowerNullOperatorRay_eq_iff (u v : {u : Fin 3 → ℝ // u ≠ 0}) :
    lowerNullOperatorRay u = lowerNullOperatorRay v ↔
      ∃ r : ℝ, r ≠ 0 ∧ v.1 = r • u.1 := by
  change splitZornOperatorRayProjection (lowerNullOperatorRepresentative u) =
    splitZornOperatorRayProjection (lowerNullOperatorRepresentative v) ↔ _
  rw [splitZornOperatorRayProjection_eq_iff]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, ?_⟩
    change splitZornLeftRegular (lowerNull v.1) =
      r • splitZornLeftRegular (lowerNull u.1) at h
    rw [← splitZornLeftRegular_smul] at h
    have hvu := splitZornLeftRegular_injective h
    have hy := congrArg (fun Z : SplitZornMatrix => Z.y) hvu
    simpa [lowerNull_smul, lowerNull] using hy
  · rintro ⟨r, hr, hv⟩
    refine ⟨r, hr, ?_⟩
    change splitZornLeftRegular (lowerNull v.1) =
      r • splitZornLeftRegular (lowerNull u.1)
    rw [hv]
    rw [lowerNull_smul]
    rw [← splitZornLeftRegular_smul]

end InfoGeometry.Canonical
