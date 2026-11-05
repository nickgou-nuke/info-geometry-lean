/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.SquareZeroPairDeformation
import InfoGeometry.HodgeCohomology.KreinHodgeDirac

/-!
# Bilinear adjunction at a square-zero exceptional deformation

The carrier is the native noncommutative algebra `Module.End ℝ E`. The
pairing is an arbitrary real bilinear form, so the results apply to the form
of a real Krein space without requiring positivity or a finite dimension.
Adjunction uses Mathlib's `LinearMap.IsAdjointPair`, rather than a new
operator or metric structure. No definiteness of a spectral sector is claimed.
-/

namespace InfoGeometry.Krein.ExceptionalPointBilinear

open InfoGeometry.Algebra.SquareZeroPairDeformation
open InfoGeometry.GrandUnification.ArchetypeDictionary

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (B : LinearMap.BilinForm ℝ E)

/-- The image of a self-adjoint square-zero map is totally isotropic. -/
theorem square_zero_range_pairing (N : Module.End ℝ E)
    (hN : LinearMap.IsAdjointPair B B N N) (hNN : N * N = 0) (x y : E) :
    B (N x) (N y) = 0 := by
  rw [hN]
  have hz : N (N y) = 0 := LinearMap.congr_fun hNN y
  rw [hz, map_zero]

/-- A real Jordan-chain eigenvector is null; no global square-zero assumption
on the shifted operator is needed. -/
theorem jordan_chain_isotropic (T : Module.End ℝ E)
    (hT : LinearMap.IsAdjointPair B B T T) (r : ℝ) (x y : E)
    (hchain : (T - r • (1 : Module.End ℝ E)) y = x) (heigen : (T - r • (1 : Module.End ℝ E)) x = 0) :
    B x x = 0 := by
  have hshift : LinearMap.IsAdjointPair B B (T - r • (1 : Module.End ℝ E)) (T - r • (1 : Module.End ℝ E)) :=
    hT.sub ((LinearMap.isAdjointPair_one (B := B)).smul r)
  have hlocal : ((T - r • (1 : Module.End ℝ E)) * (T - r • (1 : Module.End ℝ E))) y = 0 := by
    change (T - r • (1 : Module.End ℝ E)) ((T - r • (1 : Module.End ℝ E)) y) = 0
    rw [hchain, heigen]
  have hiso := InfoGeometry.HodgeCohomology.KreinHodgeDirac.square_zero_implies_isotropic_image
    B (T - r • (1 : Module.End ℝ E)) hshift y hlocal
  simpa only [hchain] using hiso

/-- Reversal of the ordered round trip is forced by adjunction. -/
theorem round_trips_adjoint (u v : Module.End ℝ E)
    (hu : LinearMap.IsAdjointPair B B u u)
    (hv : LinearMap.IsAdjointPair B B v v) :
    LinearMap.IsAdjointPair B B (u * v) (v * u) :=
  hu.mul hv

/-- The first ordered round-trip range is isotropic, even though it becomes
an idempotent range under the additional normalization. -/
theorem round_trip_range_pairing (u v : Module.End ℝ E)
    (hu : LinearMap.IsAdjointPair B B u u) (huu : u * u = 0) (x y : E) :
    B ((u * v) x) ((u * v) y) = 0 :=
  square_zero_range_pairing B u hu huu (v x) (v y)

theorem deformation_adjoint (u v : Module.End ℝ E)
    (hu : LinearMap.IsAdjointPair B B u u)
    (hv : LinearMap.IsAdjointPair B B v v) (δ : ℝ) :
    LinearMap.IsAdjointPair B B (deformation (A := Module.End ℝ E) u v δ) (deformation (A := Module.End ℝ E) u v δ) :=
  hu.add (hv.smul δ)

theorem normalized_adjoint (u v : Module.End ℝ E)
    (hu : LinearMap.IsAdjointPair B B u u)
    (hv : LinearMap.IsAdjointPair B B v v) (t : ℝ) :
    LinearMap.IsAdjointPair B B (normalized (A := Module.End ℝ E) u v t) (normalized (A := Module.End ℝ E) u v t) :=
  (hu.smul t⁻¹).add (hv.smul t)

theorem projectorPlus_adjoint (u v : Module.End ℝ E)
    (hu : LinearMap.IsAdjointPair B B u u)
    (hv : LinearMap.IsAdjointPair B B v v) (t : ℝ) :
    LinearMap.IsAdjointPair B B (projectorPlus (A := Module.End ℝ E) u v t) (projectorPlus (A := Module.End ℝ E) u v t) :=
  ((LinearMap.isAdjointPair_one (B := B)).add
    (normalized_adjoint B u v hu hv t)).smul (⅟(2 : ℝ))

theorem projectorMinus_adjoint (u v : Module.End ℝ E)
    (hu : LinearMap.IsAdjointPair B B u u)
    (hv : LinearMap.IsAdjointPair B B v v) (t : ℝ) :
    LinearMap.IsAdjointPair B B (projectorMinus (A := Module.End ℝ E) u v t) (projectorMinus (A := Module.End ℝ E) u v t) :=
  ((LinearMap.isAdjointPair_one (B := B)).sub
    (normalized_adjoint B u v hu hv t)).smul (⅟(2 : ℝ))

/-- Spectral ranges are orthogonal for the indefinite form; this is not a
claim that either range is definite. -/
theorem spectral_ranges_orthogonal (u v : Module.End ℝ E)
    (hu : u * u = 0) (hv : v * v = 0) (hunit : u * v + v * u = 1)
    (huadj : LinearMap.IsAdjointPair B B u u)
    (hvadj : LinearMap.IsAdjointPair B B v v)
    {t : ℝ} (ht : t ≠ 0) (x y : E) :
    B (projectorPlus (A := Module.End ℝ E) u v t x) (projectorMinus (A := Module.End ℝ E) u v t y) = 0 := by
  rw [projectorPlus_adjoint B u v huadj hvadj t]
  have hz : projectorPlus (A := Module.End ℝ E) u v t (projectorMinus (A := Module.End ℝ E) u v t y) = 0 :=
    LinearMap.congr_fun (projectorPlus_mul_projectorMinus (A := Module.End ℝ E) u v hu hv hunit ht) y
  rw [hz, map_zero]

/-- The spectral constraint retains the sign of the deformation parameter. -/
theorem eigenvalue_square (u v : Module.End ℝ E)
    (hu : u * u = 0) (hv : v * v = 0) (hunit : u * v + v * u = 1)
    (δ r : ℝ) (x : E) (hx : x ≠ 0)
    (heigen : deformation (A := Module.End ℝ E) u v δ x = r • x) : r ^ 2 = δ := by
  have hsq : δ • x = (r ^ 2) • x := by
    calc
      δ • x = (deformation (A := Module.End ℝ E) u v δ * deformation (A := Module.End ℝ E) u v δ) x := by
        rw [deformation_square u v hu hv hunit]
        rfl
      _ = (r ^ 2) • x := by
        change deformation (A := Module.End ℝ E) u v δ (deformation (A := Module.End ℝ E) u v δ x) = _
        rw [heigen, map_smul, heigen, smul_smul, pow_two]
  have hz : (δ - r ^ 2) • x = 0 := by rw [sub_smul, hsq, sub_self]
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hx)).symm

/-- A negative signed parameter permits no real eigenvalue with a nonzero
eigenvector. Complex spectral or dynamical conclusions are separate claims. -/
theorem no_real_eigenvector_of_negative (u v : Module.End ℝ E)
    (hu : u * u = 0) (hv : v * v = 0) (hunit : u * v + v * u = 1)
    {δ : ℝ} (hδ : δ < 0) (r : ℝ) (x : E) (hx : x ≠ 0) :
    deformation (A := Module.End ℝ E) u v δ x ≠ r • x := by
  intro heigen
  have hsq := eigenvalue_square u v hu hv hunit δ r x hx heigen
  exact (not_lt_of_ge (hsq ▸ sq_nonneg r)) hδ

end InfoGeometry.Krein.ExceptionalPointBilinear
