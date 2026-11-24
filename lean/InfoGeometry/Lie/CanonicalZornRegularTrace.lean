/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornRegularExactDet
import Mathlib.LinearAlgebra.Trace

/-!
# Polarized contraction and trace of the native Zorn regular action

The operators are the existing left regular endomorphisms of the canonical
real Zorn algebra. The trace calculation uses the matrix already read from
the existing Cartesian basis; no second multiplication table is introduced.

`QuadraticMap.polar` is the unhalved polarization. Consequently the trace of
`L_X L_conj(Y)` is four times this polarization, equivalently eight times the
associated symmetric bilinear pairing.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornRegularTrace

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge (realZornTrace)
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
  (CanonicalZorn leftRegularRepresentation)
open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge (canonicalToCoord)
open InfoGeometry.Lie.CanonicalZornRegularNorm
open InfoGeometry.Lie.CanonicalZornRegularExactDet (leftRegular_cartesian_matrix)

/-- Polarization of the left/conjugate-left contraction on the full carrier. -/
theorem leftRegular_mul_conj_polarized (X Y : CanonicalZorn) :
    leftRegularRepresentation X * leftRegularRepresentation (zornConj Y) +
        leftRegularRepresentation Y * leftRegularRepresentation (zornConj X) =
      QuadraticMap.polar (zornNorm (R := ℝ)) X Y •
        (1 : Module.End ℝ CanonicalZorn) := by
  change _ = (zornNormFun (X + Y) - zornNormFun X - zornNormFun Y) •
    (1 : Module.End ℝ CanonicalZorn)
  calc
    _ = leftRegularRepresentation (X + Y) *
          leftRegularRepresentation (zornConj (X + Y)) -
        leftRegularRepresentation X * leftRegularRepresentation (zornConj X) -
        leftRegularRepresentation Y * leftRegularRepresentation (zornConj Y) := by
          simp only [zornConj_add, map_add, mul_add, add_mul]
          abel
    _ = _ := by
      rw [leftRegular_mul_conj, leftRegular_mul_conj, leftRegular_mul_conj,
        sub_smul, sub_smul]

/-- The conjugate-left/left contraction has the same polarization. -/
theorem conj_mul_leftRegular_polarized (X Y : CanonicalZorn) :
    leftRegularRepresentation (zornConj X) * leftRegularRepresentation Y +
        leftRegularRepresentation (zornConj Y) * leftRegularRepresentation X =
      QuadraticMap.polar (zornNorm (R := ℝ)) X Y •
        (1 : Module.End ℝ CanonicalZorn) := by
  change _ = (zornNormFun (X + Y) - zornNormFun X - zornNormFun Y) •
    (1 : Module.End ℝ CanonicalZorn)
  calc
    _ = leftRegularRepresentation (zornConj (X + Y)) *
          leftRegularRepresentation (X + Y) -
        leftRegularRepresentation (zornConj X) * leftRegularRepresentation X -
        leftRegularRepresentation (zornConj Y) * leftRegularRepresentation Y := by
          simp only [zornConj_add, map_add, mul_add, add_mul]
          abel
    _ = _ := by
      rw [conj_mul_leftRegular, conj_mul_leftRegular, conj_mul_leftRegular,
        sub_smul, sub_smul]

/-- The endomorphism trace is four times the reduced Zorn trace. -/
theorem trace_leftRegular (X : CanonicalZorn) :
    LinearMap.trace ℝ CanonicalZorn (leftRegularRepresentation X) =
      4 * realZornTrace X := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm),
    leftRegular_cartesian_matrix]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_eight, realZornTrace]; ring

/-- Trace of a conjugate regular product, in the native unhalved convention. -/
theorem trace_leftRegular_mul_conj (X Y : CanonicalZorn) :
    LinearMap.trace ℝ CanonicalZorn
        (leftRegularRepresentation X * leftRegularRepresentation (zornConj Y)) =
      4 * QuadraticMap.polar (zornNorm (R := ℝ)) X Y := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm),
    LinearMap.toMatrix_mul, leftRegular_cartesian_matrix,
    leftRegular_cartesian_matrix]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_eight,
    zornConj, QuadraticMap.polar, zornNorm_apply, zornNormFun,
    ZornMatrix.dot]; ring

/-- Cyclic trace gives the opposite-order conjugate product. -/
theorem trace_conj_mul_leftRegular (X Y : CanonicalZorn) :
    LinearMap.trace ℝ CanonicalZorn
        (leftRegularRepresentation (zornConj X) * leftRegularRepresentation Y) =
      4 * QuadraticMap.polar (zornNorm (R := ℝ)) X Y := by
  rw [LinearMap.trace_mul_comm, trace_leftRegular_mul_conj,
    QuadraticMap.polar_comm _ Y X]

end InfoGeometry.Lie.CanonicalZornRegularTrace
