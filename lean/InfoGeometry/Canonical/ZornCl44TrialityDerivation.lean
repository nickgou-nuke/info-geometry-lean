/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCl44Triality
import InfoGeometry.Canonical.ZornSignedConvention
import InfoGeometry.Lie.CanonicalZornDerivation

/-!
# A concrete diagonal infinitesimal triality derivation

The difference of the quaternion-plane and split-plane bivectors has identical
vector and two spinor actions. Its Leibniz law follows by subtracting the two
universal triality identities. The resulting nonzero operator belongs to the
existing canonical Zorn derivation Lie algebra.

This proves a concrete element of that Lie algebra, without asserting an
unconstructed outer triality action or a new classification theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44TrialityDerivation

open ZornMatrix ZornClifford ZornCl44Triality ZornSignedConvention
open InfoGeometry.Lie.CanonicalZornDerivation

attribute [local simp] Matrix.vecHead Matrix.vecTail

/-- The normalized `12`-plane vector action from the two opposite norm sectors. -/
def rotation12 : Module.End ℝ (ZornMatrix ℝ) :=
  vectorBivector (quaternionAxis 0) (quaternionAxis 1) -
    vectorBivector (splitAxis 0) (splitAxis 1)

/-- Exact coordinate action: both spatial slots undergo the same rotation. -/
theorem rotation12_coordinates (z : ZornMatrix ℝ) :
    rotation12 z =
      ⟨0, 0, ![z.x 1, -z.x 0, 0], ![z.y 1, -z.y 0, 0]⟩ := by
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        simp [rotation12, vectorBivector_apply, zornBilin_apply, quaternionAxis,
          splitAxis, chiralUpperBasis, chiralLowerBasis, dot] <;> ring)
    | (simp [rotation12, vectorBivector_apply, zornBilin_apply, quaternionAxis,
        splitAxis, chiralUpperBasis, chiralLowerBasis, dot] <;> ring)

/-- The positive spinor action of the bivector difference equals its vector action. -/
theorem spinBivPlus_difference_eq_rotation12 :
    spinBivPlus (quaternionAxis 0) (quaternionAxis 1) -
      spinBivPlus (splitAxis 0) (splitAxis 1) = rotation12 := by
  apply LinearMap.ext
  intro z
  rw [rotation12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        simp [spinBivPlus, Module.End.mul_apply, quaternionAxis, splitAxis,
          chiralUpperBasis, chiralLowerBasis, zornConj, ZornMatrix.mul, dot, cross] <;> ring)
    | (simp [spinBivPlus, Module.End.mul_apply, quaternionAxis, splitAxis,
        chiralUpperBasis, chiralLowerBasis, zornConj, ZornMatrix.mul, dot, cross] <;> ring)

/-- The negative spinor action agrees with the same normalized vector action. -/
theorem spinBivMinus_difference_eq_rotation12 :
    spinBivMinus (quaternionAxis 0) (quaternionAxis 1) -
      spinBivMinus (splitAxis 0) (splitAxis 1) = rotation12 := by
  apply LinearMap.ext
  intro z
  rw [rotation12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        simp [spinBivMinus, Module.End.mul_apply, quaternionAxis, splitAxis,
          chiralUpperBasis, chiralLowerBasis, zornConj, ZornMatrix.mul, dot, cross] <;> ring)
    | (simp [spinBivMinus, Module.End.mul_apply, quaternionAxis, splitAxis,
        chiralUpperBasis, chiralLowerBasis, zornConj, ZornMatrix.mul, dot, cross] <;> ring)

/-- Subtracting the two Cartan identities yields the ordinary derivation law. -/
theorem rotation12_leibniz (v s : ZornMatrix ℝ) :
    rotation12 (v * s) = rotation12 v * s + v * rotation12 s := by
  rw [← spinBivPlus_difference_eq_rotation12]
  simp only [LinearMap.sub_apply]
  rw [cartan_infinitesimal_triality, cartan_infinitesimal_triality]
  have hplus (x : ZornMatrix ℝ) :
      spinBivPlus (quaternionAxis 0) (quaternionAxis 1) x -
          spinBivPlus (splitAxis 0) (splitAxis 1) x = rotation12 x :=
    congrArg (fun D : Module.End ℝ (ZornMatrix ℝ) => D x)
      spinBivPlus_difference_eq_rotation12
  rw [hplus, hplus]
  have hminus :
      spinBivMinus (quaternionAxis 0) (quaternionAxis 1) s -
          spinBivMinus (splitAxis 0) (splitAxis 1) s = rotation12 s :=
    congrArg (fun D : Module.End ℝ (ZornMatrix ℝ) => D s)
      spinBivMinus_difference_eq_rotation12
  have hright := (leftMulLinear v).map_sub
    (spinBivMinus (quaternionAxis 0) (quaternionAxis 1) s)
    (spinBivMinus (splitAxis 0) (splitAxis 1) s)
  rw [hminus] at hright
  have hleft := (rightMulLinear s).map_sub
    (vectorBivector (quaternionAxis 0) (quaternionAxis 1) v)
    (vectorBivector (splitAxis 0) (splitAxis 1) v)
  change rotation12 v * s =
    vectorBivector (quaternionAxis 0) (quaternionAxis 1) v * s -
      vectorBivector (splitAxis 0) (splitAxis 1) v * s at hleft
  change v * rotation12 s =
    v * spinBivMinus (quaternionAxis 0) (quaternionAxis 1) s -
      v * spinBivMinus (splitAxis 0) (splitAxis 1) s at hright
  rw [hleft, hright]
  abel

theorem rotation12_mem_derivations : rotation12 ∈ canonicalZornDerivations :=
  rotation12_leibniz

/-- The concrete operator as an element of the existing derivation Lie algebra. -/
def rotation12Derivation : canonicalZornDerivations :=
  ⟨rotation12, rotation12_mem_derivations⟩

theorem rotation12_one : rotation12 (1 : ZornMatrix ℝ) = 0 := by
  rw [rotation12_coordinates]
  apply ZornMatrix.ext <;> simp

theorem rotation12_splitUnit : rotation12 splitUnit = 0 := by
  rw [rotation12_coordinates]
  apply ZornMatrix.ext <;> simp [splitUnit, zornPlus, zornMinus]

/-- The normalization is `-e₂`, without an additional factor of one half. -/
theorem rotation12_quaternionAxis_zero : rotation12 (quaternionAxis 0) = -quaternionAxis 1 := by
  rw [rotation12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        simp [quaternionAxis, chiralUpperBasis, chiralLowerBasis])
    | simp [quaternionAxis, chiralUpperBasis, chiralLowerBasis]

theorem rotation12_quaternionAxis_one : rotation12 (quaternionAxis 1) = quaternionAxis 0 := by
  rw [rotation12_coordinates]
  apply ZornMatrix.ext
  all_goals first
    | (funext i; fin_cases i <;>
        simp [quaternionAxis, chiralUpperBasis, chiralLowerBasis])
    | simp [quaternionAxis, chiralUpperBasis, chiralLowerBasis]

theorem rotation12_ne_zero : rotation12 ≠ 0 := by
  intro h
  have hv := congrArg (fun D : Module.End ℝ (ZornMatrix ℝ) =>
    (D (quaternionAxis 0)).x 1) h
  rw [rotation12_quaternionAxis_zero] at hv
  norm_num [quaternionAxis, chiralUpperBasis, chiralLowerBasis] at hv

/-- The normalized diagonal triality operator acts on both chiral halves. -/
theorem spinBivector_difference_apply (s : DiracSpinor16 (R := ℝ)) :
    (spinBivector (quaternionAxis 0) (quaternionAxis 1) -
      spinBivector (splitAxis 0) (splitAxis 1)) s =
      (rotation12 s.1, rotation12 s.2) := by
  have hp := congrArg (fun D : Module.End ℝ (ZornMatrix ℝ) => D s.1)
    spinBivPlus_difference_eq_rotation12
  have hm := congrArg (fun D : Module.End ℝ (ZornMatrix ℝ) => D s.2)
    spinBivMinus_difference_eq_rotation12
  exact Prod.ext hp hm

theorem diracGamma_one_square : diracGamma (1 : ZornMatrix ℝ) * diracGamma 1 = 1 := by
  rw [diracGamma_square, norm_one, one_smul]

theorem diracGamma_quaternionAxis_square (i : Fin 3) :
    diracGamma (quaternionAxis i) * diracGamma (quaternionAxis i) = 1 := by
  rw [diracGamma_square, norm_quaternionAxis, one_smul]

theorem diracGamma_splitUnit_square :
    diracGamma splitUnit * diracGamma splitUnit = -1 := by
  rw [diracGamma_square, norm_splitUnit, neg_smul, one_smul]

theorem diracGamma_splitAxis_square (i : Fin 3) :
    diracGamma (splitAxis i) * diracGamma (splitAxis i) = -1 := by
  rw [diracGamma_square, norm_splitAxis, neg_smul, one_smul]

/-- The four positive-norm and four negative-norm generators, in input order. -/
def signedFrame : Fin 8 → ZornMatrix ℝ :=
  ![1, quaternionAxis 0, quaternionAxis 1, quaternionAxis 2,
    splitUnit, splitAxis 0, splitAxis 1, splitAxis 2]

set_option maxHeartbeats 800000 in
/-- The full Gram matrix, including every off-diagonal entry. -/
theorem signedFrame_bilin (i j : Fin 8) :
    zornBilin (signedFrame i) (signedFrame j) =
      if i = j then (if i.val < 4 then (1 : ℝ) else -1) else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [signedFrame, zornBilin_apply, quaternionAxis, splitAxis, splitUnit,
      chiralUpperBasis, chiralLowerBasis, zornPlus, zornMinus, dot]

/-- Every distinct pair in the signed frame anticommutes as genuine operators. -/
theorem signedFrame_gamma_anticommute (i j : Fin 8) (h : i ≠ j) :
    diracGamma (signedFrame i) * diracGamma (signedFrame j) +
      diracGamma (signedFrame j) * diracGamma (signedFrame i) = 0 := by
  rw [diracGamma_anticommutator, signedFrame_bilin, if_neg h]
  simp

end InfoGeometry.Canonical.ZornCl44TrialityDerivation
