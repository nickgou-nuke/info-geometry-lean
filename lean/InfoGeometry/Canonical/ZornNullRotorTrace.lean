/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornNullPairDensity
import InfoGeometry.Canonical.PeirceRotorChordal

/-! Actual endomorphism traces of the native null-pair rotor orbit.
The displacement square is algebraic; no positive metric is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornNullRotorTrace
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ZornNullPeirceWeyl
open PeirceRotorAction PeirceRotorChordal

theorem nullRotor_trace (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1)
    (c s : ℝ) :
    LinearMap.trace ℝ ZornCoord (movingPlus c s (ketBra X X) (ketBra Y Y)) =
      c*c+s*s := by
  rw [movingPlus_expansion (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)
    (nullPair_reflexive X Y h) (nullPair_reflexive Y X (by rwa [polarPair_symm]))]
  simp only [ketBra_mul, polarPair_symm Y X, h, one_smul, map_sub, map_add,
    map_smul, ketBra_trace, hX, hY, smul_eq_mul, mul_one, add_zero, mul_zero, sub_zero]

theorem nullRotor_displacement_trace (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1)
    (c s : ℝ) (hc : c*c+s*s=1) :
    LinearMap.trace ℝ ZornCoord
      ((movingPlus c s (ketBra X X) (ketBra Y Y) - ketBra X X * ketBra Y Y) *
       (movingPlus c s (ketBra X X) (ketBra Y Y) - ketBra X X * ketBra Y Y)) =
      2*(s*s) := by
  rw [movingPlus_displacement_square (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)
    (nullPair_reflexive X Y h) (nullPair_reflexive Y X (by rwa [polarPair_symm])) c s hc,
    map_smul, nullPair_support_trace X Y h]
  exact mul_comm _ _

theorem nullRotor_sandwich_trace (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1)
    (c s : ℝ) :
    LinearMap.trace ℝ ZornCoord
      ((ketBra X X * ketBra Y Y) * movingPlus c s (ketBra X X) (ketBra Y Y) *
        (ketBra X X * ketBra Y Y)) = c*c := by
  rw [plus_movingPlus_sandwich (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)
    (nullPair_reflexive X Y h) (nullPair_reflexive Y X (by rwa [polarPair_symm])),
    map_smul, ketBra_mul, h, one_smul, ketBra_trace, polarPair_symm Y X, h]
  exact mul_one _

end InfoGeometry.Canonical.ZornNullRotorTrace
