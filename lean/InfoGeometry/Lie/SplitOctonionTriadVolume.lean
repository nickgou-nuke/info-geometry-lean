/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.ThreeDHurwitz
import InfoGeometry.Lie.SplitOctonionCliffordAction
import InfoGeometry.Lie.SplitOctonionCircularOperatorReadout

/-!
# The positive split-octonion operator triad and its volume

The positive three-space consists of imaginary Zorn elements with zero diagonal
and equal vector entries. Its basis is the existing `ellAxis` triple. A native
quadratic isometry restricts the existing split-octonion Clifford representation
to `Cl(3,0)`. The image of its volume squares to `-1`, commutes with the three
represented generators, and changes their squares from `1` to `-1`.

All products below are compositions of real-linear operators on the full
eight-dimensional split-octonion carrier. No multiplicativity of the map from
octonion elements to left-multiplication operators is asserted. Centrality is
stated for the selected triad, not for the full endomorphism algebra.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionTriadVolume

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Clifford.ThreeDHurwitz
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionCircularBasis
open InfoGeometry.Lie.SplitOctonionCircularOperatorReadout

/-- The positive three-space inside the existing imaginary split octonions. -/
def ellEmbedding : Space3 →ₗ[ℝ] Imaginary where
  toFun v := imaginaryCoordLinearEquiv.symm
    (0, ![v.1, v.2.1, v.2.2], ![v.1, v.2.1, v.2.2])
  map_add' v w := by
    apply imaginaryCoordLinearEquiv.injective
    simp only [map_add, LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · simp
    · apply Prod.ext <;> (funext i; fin_cases i <;> rfl)
  map_smul' r v := by
    apply imaginaryCoordLinearEquiv.injective
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · simp
    · apply Prod.ext <;> (funext i; fin_cases i <;> rfl)

theorem ellEmbedding_quadratic (v : Space3) :
    leftCliffordQuadratic (ellEmbedding v) = Qdiag3 1 1 1 v := by
  rw [leftCliffordQuadratic_eq_neg_det]
  simp [ellEmbedding, imaginaryCoordLinearEquiv,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ, realCrossProduct3,
    InfoGeometry.Canonical.ZornMatrix.dot, Qdiag3, pow_two]

/-- This is a native quadratic isometry, with its compatibility proved above. -/
def ellCliffordIsometry : Qdiag3 1 1 1 →qᵢ leftCliffordQuadratic :=
  { ellEmbedding with map_app' := ellEmbedding_quadratic }

/-- Restriction of the existing seven-generator Clifford representation along
the positive three-space; no second left-regular representation is introduced. -/
def ellCliffordRepresentation :
    Cl3 1 1 1 →ₐ[ℝ] Module.End ℝ CanonicalZorn :=
  splitOctonionLeftCliffordRepresentation.comp
    (CliffordAlgebra.map ellCliffordIsometry)

@[simp] theorem ellCliffordRepresentation_ι (v : Space3) :
    ellCliffordRepresentation (CliffordAlgebra.ι (Qdiag3 1 1 1) v) =
      imaginaryLeftMul (ellEmbedding v) := by
  simp only [ellCliffordRepresentation, AlgHom.comp_apply, CliffordAlgebra.map_apply_ι,
    splitOctonionLeftCliffordRepresentation_ι]
  rfl

/-- The three represented positive generators, ordered by the quaternion axes. -/
def triad (i : Fin 3) : Module.End ℝ CanonicalZorn :=
  ellCliffordRepresentation
    (CliffordAlgebra.ι (Qdiag3 1 1 1) (![e0, e1, e2] i))

/-- The represented generators are precisely the existing left multiplications
by `ell eᵢ`, rather than products of separately represented octonion elements. -/
theorem triad_eq_leftMultiplication (i : Fin 3) :
    triad i = L (cartesianZornLinearEquiv (ellAxis i)) := by
  rw [triad, ellCliffordRepresentation_ι]
  apply LinearMap.ext
  intro X
  change (ellEmbedding (![e0, e1, e2] i)).1 * X =
    cartesianZornLinearEquiv (ellAxis i) * X
  congr 1
  fin_cases i <;> ext j <;>
    simp [ellEmbedding, imaginaryCoordLinearEquiv, e0, e1, e2,
      cartesianZornLinearEquiv, ellAxis, axis]
  all_goals fin_cases j <;> simp

@[simp] theorem triad_sq (i : Fin 3) : triad i * triad i = 1 := by
  unfold triad
  rw [← map_mul, CliffordAlgebra.ι_sq_scalar]
  have hq : Qdiag3 1 1 1 (![e0, e1, e2] i) = 1 := by
    fin_cases i <;> norm_num [Qdiag3, e0, e1, e2]
  rw [hq, map_one, map_one]

theorem triad_anticommutator (i j : Fin 3) (hij : i ≠ j) :
    triad i * triad j + triad j * triad i = 0 := by
  have hpolar : QuadraticMap.polar (Qdiag3 1 1 1)
      (![e0, e1, e2] i) (![e0, e1, e2] j) = 0 := by
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticMap.polar, Qdiag3, e0, e1, e2] at hij ⊢
  have h := congrArg ellCliffordRepresentation
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := Qdiag3 1 1 1)
      (![e0, e1, e2] i) (![e0, e1, e2] j))
  simpa [triad, hpolar] using h

/-- The oriented volume of the positive operator triad. -/
def triadVolume : Module.End ℝ CanonicalZorn := triad 0 * triad 1 * triad 2

/-- The existing generic Clifford volume-square theorem descends through the
native representation to the full split-octonion module. -/
@[simp] theorem triadVolume_sq : triadVolume * triadVolume = -1 := by
  have h := congrArg ellCliffordRepresentation (pseudoscalar_sq 1 1 1)
  simpa [triadVolume, triad, g0, g1, g2] using h

theorem triadVolume_commutes (i : Fin 3) : Commute triadVolume (triad i) := by
  have h10 : triad 1 * triad 0 = -(triad 0 * triad 1) :=
    eq_neg_of_add_eq_zero_left (triad_anticommutator 1 0 (by decide))
  have h20 : triad 2 * triad 0 = -(triad 0 * triad 2) :=
    eq_neg_of_add_eq_zero_left (triad_anticommutator 2 0 (by decide))
  have h21 : triad 2 * triad 1 = -(triad 1 * triad 2) :=
    eq_neg_of_add_eq_zero_left (triad_anticommutator 2 1 (by decide))
  fin_cases i
  · change (triad 0 * triad 1 * triad 2) * triad 0 =
      triad 0 * (triad 0 * triad 1 * triad 2)
    calc
      (triad 0 * triad 1 * triad 2) * triad 0 =
          triad 0 * triad 1 * (triad 2 * triad 0) := by rw [mul_assoc]
      _ = triad 0 * triad 1 * (-(triad 0 * triad 2)) := by rw [h20]
      _ = -(triad 0 * (triad 1 * triad 0) * triad 2) := by noncomm_ring
      _ = -(triad 0 * (-(triad 0 * triad 1)) * triad 2) := by rw [h10]
      _ = triad 0 * (triad 0 * triad 1 * triad 2) := by noncomm_ring
  · change (triad 0 * triad 1 * triad 2) * triad 1 =
      triad 1 * (triad 0 * triad 1 * triad 2)
    calc
      (triad 0 * triad 1 * triad 2) * triad 1 =
          triad 0 * triad 1 * (triad 2 * triad 1) := by rw [mul_assoc]
      _ = triad 0 * triad 1 * (-(triad 1 * triad 2)) := by rw [h21]
      _ = (-(triad 0 * triad 1)) * triad 1 * triad 2 := by noncomm_ring
      _ = (triad 1 * triad 0) * triad 1 * triad 2 := by rw [h10]
      _ = triad 1 * (triad 0 * triad 1 * triad 2) := by simp [mul_assoc]
  · change (triad 0 * triad 1 * triad 2) * triad 2 =
      triad 2 * (triad 0 * triad 1 * triad 2)
    calc
      (triad 0 * triad 1 * triad 2) * triad 2 =
          triad 0 * (triad 1 * triad 2) * triad 2 := by simp [mul_assoc]
      _ = -(triad 0 * (triad 2 * triad 1) * triad 2) := by rw [h21]; simp
      _ = (-(triad 0 * triad 2)) * triad 1 * triad 2 := by noncomm_ring
      _ = (triad 2 * triad 0) * triad 1 * triad 2 := by rw [h20]
      _ = triad 2 * (triad 0 * triad 1 * triad 2) := by simp [mul_assoc]

/-- Multiplication by the volume sends the positive generators to the actual
ordered bivectors, with the orientation sign on the middle component. -/
theorem triadVolume_mul_triad_eq_bivectors (i : Fin 3) :
    triadVolume * triad i =
      ![triad 1 * triad 2, -(triad 0 * triad 2), triad 0 * triad 1] i := by
  fin_cases i
  · change triadVolume * triad 0 = triad 1 * triad 2
    rw [(triadVolume_commutes 0).eq]
    simp only [triadVolume, ← mul_assoc, triad_sq, one_mul]
  · change triadVolume * triad 1 = -(triad 0 * triad 2)
    have h21 : triad 2 * triad 1 = -(triad 1 * triad 2) :=
      eq_neg_of_add_eq_zero_left (triad_anticommutator 2 1 (by decide))
    calc
      triadVolume * triad 1 = triad 0 * triad 1 * (triad 2 * triad 1) := by
        simp only [triadVolume, mul_assoc]
      _ = -(triad 0 * (triad 1 * triad 1) * triad 2) := by
        rw [h21]
        noncomm_ring
      _ = -(triad 0 * triad 2) := by rw [triad_sq, mul_one]
  · change triadVolume * triad 2 = triad 0 * triad 1
    simp only [triadVolume, mul_assoc (triad 0 * triad 1), triad_sq, mul_one]

/-- The commuting volume changes each positive generator into a negative one. -/
theorem triadVolume_mul_triad_sq (i : Fin 3) :
    (triadVolume * triad i) * (triadVolume * triad i) = -1 := by
  calc
    (triadVolume * triad i) * (triadVolume * triad i) =
        (triadVolume * triad i) ^ 2 := (pow_two _).symm
    _ = triadVolume ^ 2 * triad i ^ 2 := (triadVolume_commutes i).mul_pow 2
    _ = -1 := by simp only [pow_two, triadVolume_sq, triad_sq, mul_one]

/-- Circular readout is the existing algebra equivalence, so it preserves the
ordered volume product without asserting any octonion associativity. -/
theorem circular_triadVolume_eq_product :
    circularOperatorReadout triadVolume =
      circularL (cartesianZornLinearEquiv (ellAxis 0)) *
        circularL (cartesianZornLinearEquiv (ellAxis 1)) *
        circularL (cartesianZornLinearEquiv (ellAxis 2)) := by
  simp only [triadVolume, map_mul, triad_eq_leftMultiplication, circularL]

theorem circular_triad_sq (i : Fin 3) :
    circularL (cartesianZornLinearEquiv (ellAxis i)) *
      circularL (cartesianZornLinearEquiv (ellAxis i)) = 1 := by
  have h := congrArg circularOperatorReadout (triad_sq i)
  simpa only [map_mul, map_one, triad_eq_leftMultiplication, circularL] using h

theorem circular_triadVolume_sq :
    circularOperatorReadout triadVolume * circularOperatorReadout triadVolume = -1 := by
  simpa only [map_mul, map_neg, map_one] using
    congrArg circularOperatorReadout triadVolume_sq

theorem circular_triadVolume_commutes (i : Fin 3) :
    Commute (circularOperatorReadout triadVolume)
      (circularL (cartesianZornLinearEquiv (ellAxis i))) := by
  change _ * _ = _ * _
  simpa only [map_mul, triad_eq_leftMultiplication, circularL] using
    congrArg circularOperatorReadout (triadVolume_commutes i).eq

theorem circular_triadVolume_mul_triad_sq (i : Fin 3) :
    (circularOperatorReadout triadVolume *
      circularL (cartesianZornLinearEquiv (ellAxis i))) *
      (circularOperatorReadout triadVolume *
        circularL (cartesianZornLinearEquiv (ellAxis i))) = -1 := by
  simpa only [map_mul, map_neg, map_one, triad_eq_leftMultiplication, circularL] using
    congrArg circularOperatorReadout (triadVolume_mul_triad_sq i)

end InfoGeometry.Lie.SplitOctonionTriadVolume
