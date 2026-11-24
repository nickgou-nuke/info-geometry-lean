/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornRegularNorm
import InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Cartesian Witt coordinates of the native Zorn regular action

The existing coordinate equivalences identify a pair of real four-vectors
with the canonical Zorn carrier. Its reduced norm is the existing Witt
cross-pairing, and its left regular action is the existing native linear map.
The two coordinate sectors satisfy their own quadratic operator equations;
their mixed anticommutator retains both nonscalar terms.

Incidence means membership in the kernel of the existing covector. This is a
proper three-dimensional hyperplane when the covector parameter is nonzero.
These are Cartesian chiral coordinates; no identification with a separate
circular frame or faithful representation of the full Clifford algebra is
asserted.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornWittRegularBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionWittVectorCovectorBridge
open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge
open InfoGeometry.Lie.CanonicalZornRegularNorm

/-- The canonical Zorn realization obtained by composing the two existing
coordinate equivalences. -/
def wittZornEquiv :
    ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ≃ₗ[ℝ] InfoGeometry.Canonical.ZornMatrix ℝ :=
  toCoord.trans canonicalToCoord.symm

/-- The two four-vectors occupy the two native scalar/vector coordinate sectors. -/
theorem wittZornEquiv_coordinates (x p : Fin 4 → ℝ) :
    wittZornEquiv (x, p) =
      { a := x 0, b := p 0,
        x := fun i : Fin 3 => x i.succ,
        y := fun i : Fin 3 => p i.succ } := by
  apply ZornMatrix.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

/-- The native reduced norm is exactly the established vector/covector pairing. -/
@[simp] theorem zornNormFun_wittZornEquiv (x p : Fin 4 → ℝ) :
    zornNormFun (wittZornEquiv (x, p)) = wittPairing x p := by
  rw [wittZornEquiv_coordinates]
  rfl

/-- A primal coordinate sector obeys its trace-scaled quadratic operator law. -/
theorem leftRegular_primal_square (x : Fin 4 → ℝ) :
    leftRegularRepresentation (wittZornEquiv (x, 0)) *
        leftRegularRepresentation (wittZornEquiv (x, 0)) =
      x 0 • leftRegularRepresentation (wittZornEquiv (x, 0)) := by
  have hnorm : zornNormFun (wittZornEquiv (x, 0)) = 0 := by
    simp [wittPairing]
  have htrace : realZornTrace (wittZornEquiv (x, 0)) = x 0 := by
    rw [wittZornEquiv_coordinates]
    simp [realZornTrace]
  have hquad := realZorn_quadratic (wittZornEquiv (x, 0))
  change wittZornEquiv (x, 0) * wittZornEquiv (x, 0) +
      zornNormFun (wittZornEquiv (x, 0)) • (1 : InfoGeometry.Canonical.ZornMatrix ℝ) =
    realZornTrace (wittZornEquiv (x, 0)) • wittZornEquiv (x, 0) at hquad
  rw [hnorm, zero_smul, add_zero, htrace] at hquad
  rw [leftRegular_square, hquad, map_smul]

/-- A dual coordinate sector obeys the analogous trace-scaled operator law. -/
theorem leftRegular_dual_square (p : Fin 4 → ℝ) :
    leftRegularRepresentation (wittZornEquiv (0, p)) *
        leftRegularRepresentation (wittZornEquiv (0, p)) =
      p 0 • leftRegularRepresentation (wittZornEquiv (0, p)) := by
  have hnorm : zornNormFun (wittZornEquiv (0, p)) = 0 := by
    simp [wittPairing]
  have htrace : realZornTrace (wittZornEquiv (0, p)) = p 0 := by
    rw [wittZornEquiv_coordinates]
    simp [realZornTrace]
  have hquad := realZorn_quadratic (wittZornEquiv (0, p))
  change wittZornEquiv (0, p) * wittZornEquiv (0, p) +
      zornNormFun (wittZornEquiv (0, p)) • (1 : InfoGeometry.Canonical.ZornMatrix ℝ) =
    realZornTrace (wittZornEquiv (0, p)) • wittZornEquiv (0, p) at hquad
  rw [hnorm, zero_smul, add_zero, htrace] at hquad
  rw [leftRegular_square, hquad, map_smul]

/-- The mixed relation includes the two trace terms. When both zeroth
coordinates vanish, only the scalar pairing term remains. -/
theorem leftRegular_primal_dual_anticommutator (x p : Fin 4 → ℝ) :
    leftRegularRepresentation (wittZornEquiv (x, 0)) *
        leftRegularRepresentation (wittZornEquiv (0, p)) +
      leftRegularRepresentation (wittZornEquiv (0, p)) *
        leftRegularRepresentation (wittZornEquiv (x, 0)) =
      x 0 • leftRegularRepresentation (wittZornEquiv (0, p)) +
        p 0 • leftRegularRepresentation (wittZornEquiv (x, 0)) -
          wittPairing x p • 1 := by
  have hprod :
      wittZornEquiv (x, 0) * wittZornEquiv (0, p) +
          wittZornEquiv (0, p) * wittZornEquiv (x, 0) =
        x 0 • wittZornEquiv (0, p) + p 0 • wittZornEquiv (x, 0) -
          wittPairing x p • (1 : InfoGeometry.Canonical.ZornMatrix ℝ) := by
    simp only [wittZornEquiv_coordinates]
    apply ZornMatrix.ext
    · simp [ZornMatrix.mul, ZornMatrix.dot, wittPairing]
      ring
    · simp [ZornMatrix.mul, ZornMatrix.dot, wittPairing]
      ring
    · funext i
      fin_cases i <;>
        simp [ZornMatrix.mul, ZornMatrix.cross, wittPairing]
    · funext i
      fin_cases i <;>
        simp [ZornMatrix.mul, ZornMatrix.cross, wittPairing]
  rw [leftRegular_anticommutator, hprod]
  simp only [map_sub, map_add, map_smul, leftRegular_one]

/-- The operator unit criterion is the nonvanishing of the native pairing. -/
theorem isUnit_leftRegular_wittZornEquiv (x p : Fin 4 → ℝ) :
    IsUnit (leftRegularRepresentation (wittZornEquiv (x, p))) ↔
      wittPairing x p ≠ 0 := by
  rw [isUnit_leftRegular_iff, zornNormFun_wittZornEquiv]

/-- Singular left multiplication expresses incidence with the existing
covector kernel. At `p = 0` this kernel is the whole four-dimensional space. -/
theorem not_isUnit_leftRegular_iff_mem_ker (x p : Fin 4 → ℝ) :
    ¬ IsUnit (leftRegularRepresentation (wittZornEquiv (x, p))) ↔
      x ∈ LinearMap.ker (toDualPlus p) := by
  simp only [isUnit_leftRegular_wittZornEquiv, not_not,
    LinearMap.mem_ker, toDualPlus_apply]

/-- The determinant is computed in the actual existing Cartesian coordinate
basis. Its vanishing is the same covector incidence condition. -/
theorem det_leftRegular_iff_mem_ker (x p : Fin 4 → ℝ) :
    Matrix.det
        (LinearMap.toMatrix
          ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
          ((Pi.basisFun ℝ (Fin 8)).map canonicalToCoord.symm)
          (leftRegularRepresentation (wittZornEquiv (x, p)))) = 0 ↔
      x ∈ LinearMap.ker (toDualPlus p) := by
  rw [det_leftRegular_eq_zero_iff, zornNormFun_wittZornEquiv]
  rfl

/-- A nonzero covector parameter defines a genuine three-dimensional
hyperplane, by the native duality equivalence and rank-nullity theorem. -/
theorem finrank_ker_toDualPlus (p : Fin 4 → ℝ) (hp : p ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (toDualPlus p)) = 3 := by
  have hf : toDualPlus p ≠ 0 := by
    intro h
    apply hp
    apply wittDualityEquiv.injective
    change toDualPlus p = wittDualityEquiv 0
    rw [h, map_zero]
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  change Module.finrank ℝ (LinearMap.ker (toDualPlus p)) + 1 =
    Module.finrank ℝ (Fin 4 → ℝ) at hdim
  rw [Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- A concrete upper/lower pair does not commute as endomorphisms of the
full native carrier. Evaluation at the unit detects the distinct poles. -/
theorem leftRegular_primal_dual_noncommute :
    leftRegularRepresentation
        (wittZornEquiv (Pi.single (1 : Fin 4) 1, 0)) *
      leftRegularRepresentation
        (wittZornEquiv (0, Pi.single (1 : Fin 4) 1)) ≠
    leftRegularRepresentation
        (wittZornEquiv (0, Pi.single (1 : Fin 4) 1)) *
      leftRegularRepresentation
        (wittZornEquiv (Pi.single (1 : Fin 4) 1, 0)) := by
  intro h
  have hunit := congrArg
    (fun T : Module.End ℝ (InfoGeometry.Canonical.ZornMatrix ℝ) => (T 1).a) h
  change
    (wittZornEquiv (Pi.single (1 : Fin 4) 1, 0) *
      (wittZornEquiv (0, Pi.single (1 : Fin 4) 1) * 1)).a =
    (wittZornEquiv (0, Pi.single (1 : Fin 4) 1) *
      (wittZornEquiv (Pi.single (1 : Fin 4) 1, 0) * 1)).a at hunit
  simp only [InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge.mul_one] at hunit
  norm_num [wittZornEquiv_coordinates, ZornMatrix.mul,
    ZornMatrix.dot, Pi.single_apply] at hunit

/-- The exact failure of multiplicativity on the three native chiral sums.
For the cut convention `zornMinus - zornPlus`, the coefficient is negative. -/
theorem leftRegular_chiral_sum_defect :
    let s : Fin 3 → ZornMatrix ℝ := fun i =>
      ZornMatrix.chiralUpperBasis i + ZornMatrix.chiralLowerBasis i
    (leftRegularRepresentation (s 0) * leftRegularRepresentation (s 1) -
        leftRegularRepresentation (s 0 * s 1)) (s 2) =
      (-2 : ℝ) • (ZornMatrix.zornMinus - ZornMatrix.zornPlus) := by
  let s : Fin 3 → ZornMatrix ℝ := fun i =>
    ZornMatrix.chiralUpperBasis i + ZornMatrix.chiralLowerBasis i
  change (leftRegularRepresentation (s 0) * leftRegularRepresentation (s 1) -
      leftRegularRepresentation (s 0 * s 1)) (s 2) = _
  change s 0 * (s 1 * s 2) - (s 0 * s 1) * s 2 = _
  apply ZornMatrix.ext
  · norm_num [s, ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
      ZornMatrix.zornMinus, ZornMatrix.zornPlus, Pi.single_apply]
  · norm_num [s, ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
      ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
      ZornMatrix.zornMinus, ZornMatrix.zornPlus, Pi.single_apply]
  · funext i
    fin_cases i <;>
      norm_num [s, ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
        ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
        ZornMatrix.zornMinus, ZornMatrix.zornPlus, Pi.single_apply]
  · funext i
    fin_cases i <;>
      norm_num [s, ZornMatrix.chiralUpperBasis, ZornMatrix.chiralLowerBasis,
        ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross,
        ZornMatrix.zornMinus, ZornMatrix.zornPlus, Pi.single_apply]


end InfoGeometry.Lie.CanonicalZornWittRegularBridge
