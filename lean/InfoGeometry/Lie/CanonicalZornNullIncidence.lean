/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornRegularTrace
import InfoGeometry.Lie.SplitOctonionAnnihilatorDimension

/-!
# Full null-cone incidence for the canonical Zorn left regular action

For every nonzero null element of the real canonical Zorn algebra, the image
of conjugate-left multiplication is exactly the kernel of left multiplication.
Both spaces have dimension four. No imaginary or trace-zero hypothesis is
required.

A polar partner gives an actual Mathlib projection onto this kernel. The
dimension follows from its operator trace and the native projection trace
theorem. The result concerns these linear subspaces; it does not construct a
projective quadric, twistor variety, or Grassmannian classification.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornNullIncidence

open InfoGeometry.Canonical.ZornClifford
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
  (CanonicalZorn leftRegularRepresentation)
open InfoGeometry.Lie.SplitOctonionImaginaryAction
  (canonicalPolar_nondegenerate canonicalZorn_finrank)
open InfoGeometry.Lie.CanonicalZornRegularNorm
open InfoGeometry.Lie.CanonicalZornRegularTrace

/-- Every nonzero canonical Zorn element admits a unit polar partner. -/
theorem exists_polar_eq_one (X : CanonicalZorn) (hX : X ≠ 0) :
    ∃ Y : CanonicalZorn,
      QuadraticMap.polar (zornNorm (R := ℝ)) X Y = 1 := by
  classical
  obtain ⟨Y, hY⟩ : ∃ Y : CanonicalZorn,
      QuadraticMap.polar (zornNorm (R := ℝ)) X Y ≠ 0 := by
    by_contra h
    push Not at h
    exact hX (canonicalPolar_nondegenerate X h)
  refine ⟨(QuadraticMap.polar (zornNorm (R := ℝ)) X Y)⁻¹ • Y, ?_⟩
  rw [QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hY]

/-- A unit polar partner constructs a projection onto the actual null kernel. -/
theorem null_kernel_projection (X Y : CanonicalZorn)
    (hX : zornNormFun X = 0)
    (hXY : QuadraticMap.polar (zornNorm (R := ℝ)) X Y = 1) :
    LinearMap.IsProj (LinearMap.ker (leftRegularRepresentation X))
      (leftRegularRepresentation (zornConj X) * leftRegularRepresentation Y) := by
  have hzero :
      leftRegularRepresentation X * leftRegularRepresentation (zornConj X) = 0 := by
    rw [leftRegular_mul_conj, hX, zero_smul]
  have hresolution :
      leftRegularRepresentation (zornConj X) * leftRegularRepresentation Y +
        leftRegularRepresentation (zornConj Y) * leftRegularRepresentation X = 1 := by
    rw [conj_mul_leftRegular_polarized, hXY, one_smul]
  constructor
  · intro v
    change leftRegularRepresentation X
      (leftRegularRepresentation (zornConj X) (leftRegularRepresentation Y v)) = 0
    simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
      congrArg (fun T : Module.End ℝ CanonicalZorn => T (leftRegularRepresentation Y v)) hzero
  · intro v hv
    have h := congrArg (fun T : Module.End ℝ CanonicalZorn => T v) hresolution
    change leftRegularRepresentation (zornConj X) (leftRegularRepresentation Y v) +
      leftRegularRepresentation (zornConj Y) (leftRegularRepresentation X v) = v at h
    rw [show leftRegularRepresentation X v = 0 from hv, map_zero, add_zero] at h
    exact h

/-- The full null kernel is the conjugate regular image, without a trace restriction. -/
theorem range_conj_eq_ker (X : CanonicalZorn) (hX0 : X ≠ 0)
    (hX : zornNormFun X = 0) :
    LinearMap.range (leftRegularRepresentation (zornConj X)) =
      LinearMap.ker (leftRegularRepresentation X) := by
  obtain ⟨Y, hXY⟩ := exists_polar_eq_one X hX0
  have hp := null_kernel_projection X Y hX hXY
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    change (leftRegularRepresentation X * leftRegularRepresentation (zornConj X)) w = 0
    rw [leftRegular_mul_conj, hX, zero_smul]
    rfl
  · intro v hv
    exact ⟨leftRegularRepresentation Y v, hp.map_id v hv⟩

/-- The kernel of left multiplication by a nonzero null split octonion has dimension four. -/
theorem finrank_ker_eq_four (X : CanonicalZorn) (hX0 : X ≠ 0)
    (hX : zornNormFun X = 0) :
    Module.finrank ℝ (LinearMap.ker (leftRegularRepresentation X)) = 4 := by
  let : FiniteDimensional ℝ CanonicalZorn :=
    FiniteDimensional.of_finrank_eq_succ canonicalZorn_finrank
  obtain ⟨Y, hXY⟩ := exists_polar_eq_one X hX0
  have ht := (null_kernel_projection X Y hX hXY).trace
  rw [trace_conj_mul_leftRegular, hXY, mul_one] at ht
  exact_mod_cast ht.symm

/-- The conjugate regular image has the same four-dimensional incidence carrier. -/
theorem finrank_range_conj_eq_four (X : CanonicalZorn) (hX0 : X ≠ 0)
    (hX : zornNormFun X = 0) :
    Module.finrank ℝ (LinearMap.range (leftRegularRepresentation (zornConj X))) = 4 := by
  rw [range_conj_eq_ker X hX0 hX, finrank_ker_eq_four X hX0 hX]

/-- The original regular operator also has rank four on every nonzero null element. -/
theorem finrank_range_eq_four (X : CanonicalZorn) (hX0 : X ≠ 0)
    (hX : zornNormFun X = 0) :
    Module.finrank ℝ (LinearMap.range (leftRegularRepresentation X)) = 4 := by
  let : FiniteDimensional ℝ CanonicalZorn :=
    FiniteDimensional.of_finrank_eq_succ canonicalZorn_finrank
  have hrank := LinearMap.finrank_range_add_finrank_ker (leftRegularRepresentation X)
  rw [finrank_ker_eq_four X hX0 hX, canonicalZorn_finrank] at hrank
  omega

end InfoGeometry.Lie.CanonicalZornNullIncidence
