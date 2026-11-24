/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornWittRegularBridge
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension
import Mathlib.LinearAlgebra.Trace

/-! # Trace and null kernels of native Zorn left multiplication

The operator trace pairs two conjugate left actions by four times the
unnormalized polar form of the existing quadratic norm. For every nonzero
null element, conjugate left multiplication has range equal to the left
kernel, and this kernel has dimension four.

The dimension argument uses an actual projection and Mathlib's projection
trace theorem. It applies also to null elements with nonzero reduced trace;
their left operators are not asserted to be square-zero. No determinant
formula or new presentation of the split-octonion algebra is required.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornNullKernel

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionWittPairingTransportBridge
open InfoGeometry.Lie.CanonicalZornRegularNorm

local notation "L" => leftRegularRepresentation
local notation "P" => QuadraticMap.polarBilin (zornNorm (R := ℝ))
local notation "tr" => LinearMap.trace ℝ (ZornMatrix ℝ)

/-- The full eight-dimensional left action has four copies of each scalar
diagonal entry in the existing Cartesian coordinate basis. -/
theorem leftRegular_trace (X : ZornMatrix ℝ) :
    tr (L X) = 4 * (X.a + X.b) := by
  rw [← LinearMap.trace_conj' (L X) canonicalToCoord]
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 8))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    Pi.basisFun_apply, Pi.basisFun_repr, LinearEquiv.conj_apply_apply]
  change (∑ i : Fin 8,
      canonicalToCoord (X * canonicalToCoord.symm (Pi.single i 1)) i) =
    4 * (X.a + X.b)
  norm_num [Fin.sum_univ_succ, canonicalToCoord, ZornMatrix.mul_def,
    ZornMatrix.mul, ZornMatrix.dot, ZornMatrix.cross, Pi.single_apply]
  ring

/-- Polarizing the native conjugate contraction gives the unnormalized
quadratic polar form, without a factor of one half. -/
theorem leftRegular_conj_polarized (X Y : ZornMatrix ℝ) :
    L X * L (zornConj Y) + L Y * L (zornConj X) =
      P X Y • (1 : Module.End ℝ (ZornMatrix ℝ)) := by
  have hsum := leftRegular_mul_conj (X + Y)
  simp only [zornConj_add, map_add, add_mul, mul_add] at hsum
  have hx := leftRegular_mul_conj X
  have hy := leftRegular_mul_conj Y
  change L X * L (zornConj Y) + L Y * L (zornConj X) =
    (zornNormFun (X + Y) - zornNormFun X - zornNormFun Y) •
      (1 : Module.End ℝ (ZornMatrix ℝ))
  rw [sub_smul, sub_smul, ← hsum, ← hx, ← hy]
  abel

/-- The reverse polarized contraction will supply an explicit preimage for
each vector in a null left kernel. -/
theorem conj_leftRegular_polarized (X Y : ZornMatrix ℝ) :
    L (zornConj X) * L Y + L (zornConj Y) * L X =
      P X Y • (1 : Module.End ℝ (ZornMatrix ℝ)) := by
  have hsum := conj_mul_leftRegular (X + Y)
  simp only [zornConj_add, map_add, add_mul, mul_add] at hsum
  have hx := conj_mul_leftRegular X
  have hy := conj_mul_leftRegular Y
  change L (zornConj X) * L Y + L (zornConj Y) * L X =
    (zornNormFun (X + Y) - zornNormFun X - zornNormFun Y) •
      (1 : Module.End ℝ (ZornMatrix ℝ))
  rw [sub_smul, sub_smul, ← hsum, ← hx, ← hy]
  abel

/-- The actual operator trace is four times the native unnormalized norm
polar form, equivalently eight times its normalized symmetric form. -/
theorem trace_leftRegular_mul_conj (X Y : ZornMatrix ℝ) :
    tr (L X * L (zornConj Y)) = 4 * P X Y := by
  let : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    canonicalToCoord.symm.finiteDimensional
  have hconj (Z : ZornMatrix ℝ) :
      L (zornConj Z) = (Z.a + Z.b) • 1 - L Z := by
    have hz : zornConj Z = (Z.a + Z.b) • (1 : ZornMatrix ℝ) - Z :=
      InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalConj_eq_trace_sub Z
    rw [hz, map_sub, map_smul, leftRegular_one]
  have hpair : tr (L X * L (zornConj Y)) = tr (L Y * L (zornConj X)) := by
    rw [hconj Y, hconj X]
    simp only [mul_sub, mul_smul_comm, mul_one, map_sub, map_smul,
      smul_eq_mul, leftRegular_trace]
    rw [LinearMap.trace_mul_comm ℝ (L X) (L Y)]
    ring
  have hsum := congrArg tr (leftRegular_conj_polarized X Y)
  rw [map_add, map_smul, LinearMap.trace_one,
    InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalZorn_finrank] at hsum
  change tr (L X * L (zornConj Y)) + tr (L Y * L (zornConj X)) =
    P X Y * 8 at hsum
  rw [← hpair] at hsum
  have hscalar : (tr (L X * L (zornConj Y)) - 4 * P X Y : ℝ) = 0 := by
    linarith [hsum]
  exact sub_eq_zero.mp hscalar

private theorem exists_polar_eq_one {X : ZornMatrix ℝ} (hX : X ≠ 0) :
    ∃ Y : ZornMatrix ℝ, P X Y = 1 := by
  classical
  have hn : ¬ ∀ Y : ZornMatrix ℝ, P X Y = 0 := by
    intro h
    apply hX
    apply InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalPolar_nondegenerate X
    intro Y
    change P X Y = 0
    exact h Y
  obtain ⟨Y, hY⟩ := not_forall.mp hn
  refine ⟨(P X Y)⁻¹ • Y, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hY]

/-- For any nonzero null element, the conjugate left range is exactly the
left kernel. This does not require the element to have reduced trace zero. -/
theorem range_conj_eq_ker_leftRegular (X : ZornMatrix ℝ)
    (hX : X ≠ 0) (hN : zornNorm X = 0) :
    LinearMap.range (L (zornConj X)) = LinearMap.ker (L X) := by
  have hnull : L X * L (zornConj X) = 0 := by
    rw [leftRegular_mul_conj]
    change zornNorm X • (1 : Module.End ℝ (ZornMatrix ℝ)) = 0
    rw [hN, zero_smul]
  obtain ⟨Y, hY⟩ := exists_polar_eq_one hX
  have hhom : L (zornConj X) * L Y + L (zornConj Y) * L X = 1 := by
    rw [conj_leftRegular_polarized, hY, one_smul]
  apply le_antisymm
  · rintro Z ⟨W, rfl⟩
    change (L X * L (zornConj X)) W = 0
    rw [hnull, LinearMap.zero_apply]
  · intro Z hZ
    have hZ0 := LinearMap.mem_ker.mp hZ
    refine ⟨L Y Z, ?_⟩
    have h := congrArg (fun T : Module.End ℝ (ZornMatrix ℝ) => T Z) hhom
    change L (zornConj X) (L Y Z) + L (zornConj Y) (L X Z) = Z at h
    rw [hZ0, map_zero, add_zero] at h
    exact h

/-- The full left kernel of every nonzero null Zorn element has dimension
four. The proof uses a projection of trace four and native rank-nullity. -/
theorem finrank_ker_leftRegular_eq_four (X : ZornMatrix ℝ)
    (hX : X ≠ 0) (hN : zornNorm X = 0) :
    Module.finrank ℝ (LinearMap.ker (L X)) = 4 := by
  let : FiniteDimensional ℝ (ZornMatrix ℝ) :=
    canonicalToCoord.symm.finiteDimensional
  obtain ⟨Y, hY⟩ := exists_polar_eq_one hX
  have hnull : L X * L (zornConj X) = 0 := by
    rw [leftRegular_mul_conj]
    change zornNorm X • (1 : Module.End ℝ (ZornMatrix ℝ)) = 0
    rw [hN, zero_smul]
  have hhom : L (zornConj X) * L Y + L (zornConj Y) * L X = 1 := by
    rw [conj_leftRegular_polarized, hY, one_smul]
  have hsub : L (zornConj Y) * L X = 1 - L (zornConj X) * L Y :=
    eq_sub_of_add_eq' hhom
  let T : Module.End ℝ (ZornMatrix ℝ) := L X * L (zornConj Y)
  have hTL : T * L X = L X := by
    change (L X * L (zornConj Y)) * L X = L X
    rw [mul_assoc, hsub, mul_sub, mul_one, ← mul_assoc, hnull, zero_mul, sub_zero]
  have hT : IsIdempotentElem T := by
    change T * T = T
    calc
      T * T = (T * L X) * L (zornConj Y) := by
        change T * (L X * L (zornConj Y)) = (T * L X) * L (zornConj Y)
        rw [mul_assoc]
      _ = L X * L (zornConj Y) := by rw [hTL]
      _ = T := rfl
  have hrange : LinearMap.range T = LinearMap.range (L X) := by
    apply le_antisymm
    · rintro Z ⟨W, rfl⟩
      exact ⟨L (zornConj Y) W, rfl⟩
    · rintro Z ⟨W, rfl⟩
      refine ⟨L X W, ?_⟩
      exact congrArg (fun F : Module.End ℝ (ZornMatrix ℝ) => F W) hTL
  have htr : tr T = 4 := by
    change tr (L X * L (zornConj Y)) = 4
    rw [trace_leftRegular_mul_conj, hY, mul_one]
  have hdimT : Module.finrank ℝ (LinearMap.range T) = 4 := by
    have hp := hT.isProj_range.trace
    rw [htr] at hp
    exact_mod_cast hp.symm
  have hrank : Module.finrank ℝ (LinearMap.range (L X)) = 4 := by
    rw [← hrange]
    exact hdimT
  have hrn := LinearMap.finrank_range_add_finrank_ker (L X)
  rw [hrank,
    InfoGeometry.Lie.SplitOctonionImaginaryAction.canonicalZorn_finrank] at hrn
  omega

/-- Norm multiplicativity makes this entire four-dimensional kernel null,
using its established realization as a conjugate left range. -/
theorem zornNorm_eq_zero_of_mem_ker_leftRegular (X : ZornMatrix ℝ)
    (hX : X ≠ 0) (hN : zornNorm X = 0) {Z : ZornMatrix ℝ}
    (hZ : Z ∈ LinearMap.ker (L X)) : zornNorm Z = 0 := by
  have hr : Z ∈ LinearMap.range (L (zornConj X)) := by
    rw [range_conj_eq_ker_leftRegular X hX hN]
    exact hZ
  obtain ⟨W, rfl⟩ := hr
  have hn := zornNormFun_sub_conj_eq_commutator X
  rw [mul_comm X.a X.b, sub_self] at hn
  have hconj : zornNorm (zornConj X) = zornNorm X :=
    (sub_eq_zero.mp hn).symm
  have hmul : zornNorm (zornConj X * W) =
      zornNorm (zornConj X) * zornNorm W :=
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionDatum.detZ_mul
      (zornConj X) W
  change zornNorm (zornConj X * W) = 0
  rw [hmul, hconj, hN, zero_mul]

end InfoGeometry.Lie.CanonicalZornNullKernel
