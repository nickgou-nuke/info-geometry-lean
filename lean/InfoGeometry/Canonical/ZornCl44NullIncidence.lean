/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornCl44TrialityOrthogonal
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Null-vector kernels on the full real Zorn carrier

For every nonzero Zorn vector of zero norm, the kernel of left
multiplication is a four-dimensional maximal totally isotropic subspace.
There is no imaginary-vector restriction.  Polarized Clifford contraction
identifies the kernel with the range of conjugate left multiplication;
adjointness then identifies that kernel with its own orthogonal complement.

Conjugation transports right kernels to left kernels, giving the same
dimension and isotropy for right multiplication.  The doubled Dirac gamma
kernel has dimension eight, rather than four.

These results construct the kernel incidence assignment.  They do not
assert a projective or Grassmannian bijection, an outer triality action,
or an identification with a chosen spacetime/cotangent manifold.
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornCl44NullIncidence

open ZornMatrix ZornClifford ZornCl44Triality

local instance : FiniteDimensional ℝ (ZornMatrix ℝ) :=
  (ZornMatrix.coordLinearEquiv (R := ℝ)).symm.finiteDimensional

private theorem zorn_finrank_eq_eight : Module.finrank ℝ (ZornMatrix ℝ) = 8 := by
  calc
    Module.finrank ℝ (ZornMatrix ℝ) = Module.finrank ℝ (ZornMatrix.Coord ℝ) :=
      (ZornMatrix.coordLinearEquiv (R := ℝ)).finrank_eq
    _ = 8 := by
      norm_num [ZornMatrix.Coord, Module.finrank_prod, Module.finrank_pi]

/-- Each canonical coordinate is detected by its opposite null basis coordinate. -/
theorem zornBilin_separatingLeft : zornBilin.SeparatingLeft := by
  intro z hz
  apply ZornMatrix.ext
  · change z.a = 0
    have h := hz (zornMinus (R := ℝ))
    norm_num [zornBilin_apply, zornMinus, dot] at h ⊢
    linarith
  · change z.b = 0
    have h := hz (zornPlus (R := ℝ))
    norm_num [zornBilin_apply, zornPlus, dot] at h ⊢
    linarith
  · funext i
    change z.x i = 0
    have h := hz (chiralLowerBasis (R := ℝ) i)
    fin_cases i <;>
      norm_num [zornBilin_apply, chiralLowerBasis, dot,
        Matrix.vecHead, Matrix.vecTail] at h ⊢ <;> linarith
  · funext i
    change z.y i = 0
    have h := hz (chiralUpperBasis (R := ℝ) i)
    fin_cases i <;>
      norm_num [zornBilin_apply, chiralUpperBasis, dot,
        Matrix.vecHead, Matrix.vecTail] at h ⊢ <;> linarith

/-- Nondegeneracy of the native split bilinear form in both arguments. -/
theorem zornBilin_nondegenerate : zornBilin.Nondegenerate := by
  refine ⟨zornBilin_separatingLeft, ?_⟩
  intro z hz
  apply zornBilin_separatingLeft z
  intro w
  rw [zornBilin_symm]
  exact hz w

/-- A nonzero vector has a partner normalized to unit full polarization. -/
theorem exists_polar_partner (z : ZornMatrix ℝ) (hz : z ≠ 0) :
    ∃ w : ZornMatrix ℝ, 2 * zornBilin z w = 1 := by
  classical
  have hnot : ¬ ∀ w : ZornMatrix ℝ, zornBilin z w = 0 :=
    fun h => hz (zornBilin_separatingLeft z h)
  obtain ⟨w, hw⟩ := not_forall.mp hnot
  have hc : (2 : ℝ) * zornBilin z w ≠ 0 :=
    mul_ne_zero (by norm_num) hw
  refine ⟨((2 * zornBilin z w)⁻¹) • w, ?_⟩
  calc
    2 * zornBilin z (((2 * zornBilin z w)⁻¹) • w) =
        (2 * zornBilin z w)⁻¹ * (2 * zornBilin z w) := by
      rw [map_smul, smul_eq_mul]
      ring
    _ = 1 := inv_mul_cancel₀ hc

/-- The second diagonal block of the polarized Clifford square law. -/
theorem left_conjugate_polarized (z w x : ZornMatrix ℝ) :
    leftMulLinear (zornConj z) (leftMulLinear w x) +
        leftMulLinear (zornConj w) (leftMulLinear z x) =
      (2 * zornBilin z w) • x := by
  have h := congrArg
    (fun F : Module.End ℝ (DiracSpinor16 (R := ℝ)) => (F (0, x)).2)
    (diracGamma_anticommutator z w)
  change zornConj z * (w * x) + zornConj w * (z * x) =
    (2 * zornBilin z w) • x at h
  exact h

/-- Null conjugate left multiplications form an exact two-periodic pair. -/
theorem ker_left_eq_range_conjugate (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    LinearMap.ker (leftMulLinear z) =
      LinearMap.range (leftMulLinear (zornConj z)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := exists_polar_partner z hz
    refine ⟨leftMulLinear w x, ?_⟩
    have h := left_conjugate_polarized z w x
    rw [LinearMap.mem_ker.mp hx, map_zero, add_zero, hw, one_smul] at h
    exact h
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    have h : leftMulLinear z (leftMulLinear (zornConj z) y) = zornNorm z • y := by
      simpa only [leftMulLinear_apply, zornNorm_apply] using mul_zornConj_mul z y
    rw [hn, zero_smul] at h
    exact h

/-- Adjointness identifies the orthogonal complement of the conjugate range. -/
theorem range_left_conjugate_orthogonal (z : ZornMatrix ℝ) :
    zornBilin.orthogonal (LinearMap.range (leftMulLinear (zornConj z))) =
      LinearMap.ker (leftMulLinear z) := by
  ext y
  constructor
  · intro hy
    apply LinearMap.mem_ker.mpr
    apply zornBilin_nondegenerate.2 (leftMulLinear z y)
    intro x
    have hzero := hy (leftMulLinear (zornConj z) x) ⟨x, rfl⟩
    have hadj := leftMulLinear_isAdjointPair (zornConj z) x y
    simp only [zornConj_involutive] at hadj
    exact hadj.symm.trans hzero
  · intro hy
    rintro v ⟨x, rfl⟩
    have hadj := leftMulLinear_isAdjointPair (zornConj z) x y
    simp only [zornConj_involutive] at hadj
    rw [LinearMap.mem_ker.mp hy, map_zero] at hadj
    exact hadj

/-- The null multiplication kernel equals its own orthogonal complement. -/
theorem ker_left_self_orthogonal (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    zornBilin.orthogonal (LinearMap.ker (leftMulLinear z)) =
      LinearMap.ker (leftMulLinear z) := by
  calc
    zornBilin.orthogonal (LinearMap.ker (leftMulLinear z)) =
        zornBilin.orthogonal (LinearMap.range (leftMulLinear (zornConj z))) :=
      congrArg zornBilin.orthogonal (ker_left_eq_range_conjugate z hz hn)
    _ = LinearMap.ker (leftMulLinear z) := range_left_conjugate_orthogonal z

/-- Every nonzero null vector on the full eight-dimensional carrier has a
four-dimensional left multiplication kernel. -/
theorem finrank_ker_left_of_nonzero_null (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    Module.finrank ℝ (LinearMap.ker (leftMulLinear z)) = 4 := by
  have hdim := LinearMap.BilinForm.finrank_orthogonal zornBilin_nondegenerate
    (LinearMap.ker (leftMulLinear z))
  rw [ker_left_self_orthogonal z hz hn, zorn_finrank_eq_eight] at hdim
  omega

theorem finrank_range_left_of_nonzero_null (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    Module.finrank ℝ (LinearMap.range (leftMulLinear z)) = 4 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (leftMulLinear z)
  rw [finrank_ker_left_of_nonzero_null z hz hn, zorn_finrank_eq_eight] at hdim
  omega

theorem ker_left_isotropic (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0)
    {x y : ZornMatrix ℝ} (hx : x ∈ LinearMap.ker (leftMulLinear z))
    (hy : y ∈ LinearMap.ker (leftMulLinear z)) :
    zornBilin x y = 0 := by
  have hy' : y ∈ zornBilin.orthogonal (LinearMap.ker (leftMulLinear z)) := by
    rw [ker_left_self_orthogonal z hz hn]
    exact hy
  exact hy' x hx

theorem norm_eq_zero_of_mem_ker_left (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0)
    {x : ZornMatrix ℝ} (hx : x ∈ LinearMap.ker (leftMulLinear z)) :
    zornNorm x = 0 := by
  rw [← zornBilin_self]
  exact ker_left_isotropic z hz hn hx hx

/-- No strictly larger subspace containing the kernel can remain totally isotropic. -/
theorem ker_left_maximal_isotropic (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) (W : Submodule ℝ (ZornMatrix ℝ))
    (hcontain : LinearMap.ker (leftMulLinear z) ≤ W)
    (hW : ∀ x ∈ W, ∀ y ∈ W, zornBilin x y = 0) :
    W = LinearMap.ker (leftMulLinear z) := by
  apply le_antisymm ?_ hcontain
  intro x hx
  rw [← ker_left_self_orthogonal z hz hn]
  intro y hy
  exact hW y (hcontain hy) x hx

@[simp] theorem zornConj_zero : zornConj (0 : ZornMatrix ℝ) = 0 :=
  (conjugationLinear (R := ℝ)).map_zero

/-- Conjugation is the existing canonical anti-automorphism. -/
theorem zornConj_mul (x y : ZornMatrix ℝ) :
    zornConj (x * y) = zornConj y * zornConj x :=
  ZornMatrix.conjugate_mul x y

@[simp] theorem zornNorm_conjugate (z : ZornMatrix ℝ) :
    zornNorm (zornConj z) = zornNorm z := by
  simp [zornNorm_apply, zornNormFun, zornConj, dot]; ring

@[simp] theorem zornBilin_conjugate (x y : ZornMatrix ℝ) :
    zornBilin (zornConj x) (zornConj y) = zornBilin x y := by
  simp [zornBilin_apply, zornConj, dot]; ring

theorem zornConj_ne_zero (z : ZornMatrix ℝ) (hz : z ≠ 0) : zornConj z ≠ 0 := by
  intro h
  apply hz
  have hc := congrArg zornConj h
  simpa only [zornConj_involutive, zornConj_zero] using hc

/-- Conjugation identifies a right kernel with the corresponding conjugate left kernel. -/
def rightKernelEquivLeftConjugate (z : ZornMatrix ℝ) :
    LinearMap.ker (rightMulLinear z) ≃ₗ[ℝ]
      LinearMap.ker (leftMulLinear (zornConj z)) where
  toFun x := ⟨zornConj x, by
    change zornConj z * zornConj x.1 = 0
    rw [← zornConj_mul]
    change zornConj (rightMulLinear z x.1) = 0
    rw [LinearMap.mem_ker.mp x.2, zornConj_zero]⟩
  invFun y := ⟨zornConj y, by
    change zornConj y.1 * z = 0
    calc
      zornConj y.1 * z = zornConj (zornConj z * y.1) := by
        rw [zornConj_mul, zornConj_involutive]
      _ = 0 := by
        change zornConj (leftMulLinear (zornConj z) y.1) = 0
        rw [LinearMap.mem_ker.mp y.2, zornConj_zero]⟩
  left_inv x := by
    apply Subtype.ext
    exact zornConj_involutive x.1
  right_inv y := by
    apply Subtype.ext
    exact zornConj_involutive y.1
  map_add' x y := by
    apply Subtype.ext
    exact zornConj_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact zornConj_smul r x.1

theorem finrank_ker_right_of_nonzero_null (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    Module.finrank ℝ (LinearMap.ker (rightMulLinear z)) = 4 := by
  calc
    Module.finrank ℝ (LinearMap.ker (rightMulLinear z)) =
        Module.finrank ℝ (LinearMap.ker (leftMulLinear (zornConj z))) :=
      (rightKernelEquivLeftConjugate z).finrank_eq
    _ = 4 := finrank_ker_left_of_nonzero_null (zornConj z)
      (zornConj_ne_zero z hz) (by simpa only [zornNorm_conjugate] using hn)

theorem finrank_range_right_of_nonzero_null (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    Module.finrank ℝ (LinearMap.range (rightMulLinear z)) = 4 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (rightMulLinear z)
  rw [finrank_ker_right_of_nonzero_null z hz hn, zorn_finrank_eq_eight] at hdim
  omega

theorem ker_right_isotropic (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0)
    {x y : ZornMatrix ℝ} (hx : x ∈ LinearMap.ker (rightMulLinear z))
    (hy : y ∈ LinearMap.ker (rightMulLinear z)) :
    zornBilin x y = 0 := by
  have hx' := (rightKernelEquivLeftConjugate z ⟨x, hx⟩).2
  have hy' := (rightKernelEquivLeftConjugate z ⟨y, hy⟩).2
  have h := ker_left_isotropic (zornConj z) (zornConj_ne_zero z hz)
    (by simpa only [zornNorm_conjugate] using hn) hx' hy'
  change zornBilin (zornConj x) (zornConj y) = 0 at h
  simpa only [zornBilin_conjugate] using h

theorem norm_eq_zero_of_mem_ker_right (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0)
    {x : ZornMatrix ℝ} (hx : x ∈ LinearMap.ker (rightMulLinear z)) :
    zornNorm x = 0 := by
  rw [← zornBilin_self]
  exact ker_right_isotropic z hz hn hx hx

/-- The full doubled gamma operator is an exact square-zero endomorphism
at every nonzero null vector. -/
theorem ker_diracGamma_eq_range (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    LinearMap.ker (diracGamma z) = LinearMap.range (diracGamma z) := by
  ext s
  constructor
  · intro hs
    obtain ⟨w, hw⟩ := exists_polar_partner z hz
    refine ⟨diracGamma w s, ?_⟩
    have h := congrArg
      (fun F : Module.End ℝ (DiracSpinor16 (R := ℝ)) => F s)
      (diracGamma_anticommutator z w)
    simp only [LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.mul_apply, Module.End.one_apply] at h
    rw [LinearMap.mem_ker.mp hs, map_zero, add_zero, hw, one_smul] at h
    exact h
  · rintro ⟨s, rfl⟩
    apply LinearMap.mem_ker.mpr
    have h := diracGamma_sq_apply z s
    rw [hn, zero_smul] at h
    exact h

/-- The full Dirac kernel is eight-dimensional; the chiral multiplication
kernels above are each four-dimensional. -/
theorem finrank_ker_diracGamma_of_nonzero_null (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    Module.finrank ℝ (LinearMap.ker (diracGamma z)) = 8 := by
  have hdim := LinearMap.finrank_range_add_finrank_ker (diracGamma z)
  rw [← ker_diracGamma_eq_range z hz hn] at hdim
  have hspin : Module.finrank ℝ (DiracSpinor16 (R := ℝ)) = 16 := by
    change Module.finrank ℝ (ZornMatrix ℝ × ZornMatrix ℝ) = 16
    norm_num [Module.finrank_prod, zorn_finrank_eq_eight]
  rw [hspin] at hdim
  omega

theorem finrank_range_diracGamma_of_nonzero_null (z : ZornMatrix ℝ)
    (hz : z ≠ 0) (hn : zornNorm z = 0) :
    Module.finrank ℝ (LinearMap.range (diracGamma z)) = 8 := by
  rw [← ker_diracGamma_eq_range z hz hn]
  exact finrank_ker_diracGamma_of_nonzero_null z hz hn

end InfoGeometry.Canonical.ZornCl44NullIncidence
