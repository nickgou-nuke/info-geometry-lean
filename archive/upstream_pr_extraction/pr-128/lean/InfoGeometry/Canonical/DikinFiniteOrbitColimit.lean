/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.DikinBlahutOrbits
import InfoGeometry.Canonical.QuantumInformationGeometryColimitDualityCapstone
import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm
import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity
import InfoGeometry.Canonical.SouriauOnsagerBKMStrictPositivity

/-!
# Finite Dikin orbit confinement

This is the finite-stage replacement for an analytic convergence argument.
It records only iterated membership in nested Dikin ellipsoids.  No limit,
continuity, or classical analyticity is used; such finite statements are the
ones that can subsequently be transported through a filtered colimit.
-/

namespace InfoGeometry.Canonical.DikinFiniteOrbitColimit

open InfoGeometry.Quantum.DikinBlahutOrbits
open InfoGeometry.Canonical.QuantumInfoColimit
open SouriauOnsagerBKM

noncomputable section

def orbit (T : ℝ → ℝ) (y : ℝ) : ℕ → ℝ
  | 0 => y
  | n + 1 => T (orbit T y n)

theorem orbit_zero (T : ℝ → ℝ) (y : ℝ) : orbit T y 0 = y := rfl

theorem orbit_succ (T : ℝ → ℝ) (y : ℝ) (n : ℕ) :
    orbit T y (n + 1) = T (orbit T y n) := rfl

/-- Every finite iterate stays in the Dikin ellipsoid with the contracted
radius, provided the map contracts distance to the orbit centre. -/
theorem orbit_mem_dikin_ellipsoid
    (T : ℝ → ℝ) (x y r Kc : ℝ)
    (hx : 0 < x) (hr : 0 ≤ r) (hKc : 0 ≤ Kc)
    (hcontract : ∀ z : ℝ, |T z - x| ≤ Kc * |z - x|)
    (hstart : InDikinEllipsoid x y r) :
    ∀ n : ℕ, InDikinEllipsoid x (orbit T y n) (Kc ^ n * r) := by
  intro n
  induction n with
  | zero =>
      simpa [orbit, pow_zero, one_mul] using hstart
  | succ n ih =>
      rw [orbit_succ]
      rw [dikin_ellipsoid_iff_abs_le x (T (orbit T y n)) (Kc ^ (n + 1) * r)
        hx (by positivity)]
      rw [dikin_ellipsoid_iff_abs_le x (orbit T y n) (Kc ^ n * r) hx
        (by positivity)] at ih
      have hstep := hcontract (orbit T y n)
      have hpow : Kc ^ (n + 1) * r = Kc * (Kc ^ n * r) := by
        rw [pow_succ]
        ring
      rw [hpow]
      exact le_trans hstep (by
        calc
          Kc * |orbit T y n - x| ≤ Kc * (Kc ^ n * r * x) :=
            mul_le_mul_of_nonneg_left ih hKc
          _ = Kc * (Kc ^ n * r) * x := by ring)

/-- A finite Dikin orbit satisfying a subunit radius constraint remains in the
strict positive interior. -/
theorem orbit_strictly_positive
    (T : ℝ → ℝ) (x y r Kc : ℝ)
    (hx : 0 < x) (hr : 0 ≤ r) (hKc : 0 ≤ Kc)
    (hcontract : ∀ z : ℝ, |T z - x| ≤ Kc * |z - x|)
    (hstart : InDikinEllipsoid x y r)
    (n : ℕ) (hradius : Kc ^ n * r < 1) :
    0 < orbit T y n := by
  apply dikin_ellipsoid_strictly_positive x (orbit T y n) (Kc ^ n * r) hx
    (by positivity) hradius
  exact orbit_mem_dikin_ellipsoid T x y r Kc hx hr hKc hcontract hstart n

theorem orbit_strictly_positive_of_subunit_radius
    (T : ℝ → ℝ) (x y r Kc : ℝ)
    (hx : 0 < x) (hr : 0 ≤ r) (hr_lt : r < 1)
    (hKc : 0 ≤ Kc) (hKc_le : Kc ≤ 1)
    (hcontract : ∀ z : ℝ, |T z - x| ≤ Kc * |z - x|)
    (hstart : InDikinEllipsoid x y r) (n : ℕ) :
    0 < orbit T y n := by
  apply orbit_strictly_positive T x y r Kc hx hr hKc hcontract hstart n
  have hpow : ∀ k : ℕ, Kc ^ k * r ≤ r := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hmul : Kc * (Kc ^ k * r) ≤ Kc * r :=
          mul_le_mul_of_nonneg_left ih hKc
        nlinarith
  exact lt_of_le_of_lt (hpow n) hr_lt

/-- The squared Dikin radius is antitone in the finite sample/stage index.
This is the finite constraint law used in place of an analytic limiting claim. -/
theorem dikin_radius_sq_antitone
    (i1 : ℝ) (hi1 : 0 < i1) {N M : ℕ}
    (hNM : N ≤ M) (hN : 0 < N) :
    dikinRadius M i1 ^ 2 ≤ dikinRadius N i1 ^ 2 := by
  rw [dikin_radius_sq_eq_cramer_rao M i1 (by omega) hi1,
    dikin_radius_sq_eq_cramer_rao N i1 hN hi1]
  apply one_div_le_one_div_of_le
  · positivity
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNM) (le_of_lt hi1)

/-- Every finite-stage Dikin radius is nonzero (and hence has positive square)
when the sample index and one-stage information are positive. -/
theorem dikin_radius_sq_pos
    (N : ℕ) (i1 : ℝ) (hN : 0 < N) (hi1 : 0 < i1) :
    0 < dikinRadius N i1 ^ 2 := by
  rw [dikin_radius_sq_eq_cramer_rao N i1 hN hi1]
  exact one_div_pos.mpr (by positivity)

/-- The finite-stage Dikin constraints are contravariantly nested: a later
sample stage has a smaller admissible ellipsoid. -/
theorem dikin_stage_constraint_mono
    (x i1 : ℝ) (hi1 : 0 < i1)
    {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    {y : ℝ}
    (hy : InDikinEllipsoid x y (dikinRadius M i1)) :
    InDikinEllipsoid x y (dikinRadius N i1) := by
  unfold InDikinEllipsoid at hy ⊢
  have hradius : dikinRadius M i1 ^ 2 ≤ dikinRadius N i1 ^ 2 :=
    dikin_radius_sq_antitone i1 hi1 hNM hN
  exact le_trans hy hradius

/-- A point satisfying a finite-stage Dikin constraint with subunit radius is
strictly interior to the positive ray. -/
theorem dikin_stage_constraint_strictly_positive
    (x i1 y : ℝ) (hx : 0 < x)
    (hRadius_nonneg : 0 ≤ dikinRadius N i1)
    (hRadius : dikinRadius N i1 < 1)
    (hy : InDikinEllipsoid x y (dikinRadius N i1)) :
    0 < y := by
  apply dikin_ellipsoid_strictly_positive x y (dikinRadius N i1) hx
    hRadius_nonneg hRadius
  exact hy

/-! ## BKM Dikin constraints on the native self-adjoint carrier -/

abbrev SelfAdjointOperator (n : ℕ) := selfAdjoint (FiniteOperatorAlgebra n)

def bkmDikinQuadratic
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : SelfAdjointOperator n) : ℝ :=
  D.bkmRealBilinForm h A.1 A.1

def InBkmDikinEllipsoid
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : SelfAdjointOperator n) (r : ℝ) : Prop :=
  bkmDikinQuadratic D h A ≤ r ^ 2

def InBkmDikinEllipsoidAt
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (C A : SelfAdjointOperator n) (r : ℝ) : Prop :=
  bkmDikinQuadratic D h (C - A) ≤ r ^ 2

theorem inBkmDikinEllipsoidAt_iff
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (C A : SelfAdjointOperator n) (r : ℝ) :
    InBkmDikinEllipsoidAt D h C A r ↔
      InBkmDikinEllipsoid D h (C - A) r := by
  rfl

theorem inBkmDikinEllipsoidAt_center
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (C : SelfAdjointOperator n) {r : ℝ} :
    InBkmDikinEllipsoidAt D h C C r := by
  unfold InBkmDikinEllipsoidAt bkmDikinQuadratic
  simp
  exact sq_nonneg r

theorem bkmDikinQuadratic_nonneg
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : SelfAdjointOperator n) :
    0 ≤ bkmDikinQuadratic D h A := by
  exact D.kuboMoriPairing_self_re_nonneg A.1 h

theorem bkmDikinQuadratic_pos_of_ne_zero
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : SelfAdjointOperator n) (hA : A ≠ 0) :
    0 < bkmDikinQuadratic D h A := by
  apply D.kuboMoriPairing_self_pos A.1 h
  intro hzero
  apply hA
  apply Subtype.ext
  exact hzero

theorem bkmDikinQuadratic_eq_zero_iff
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : SelfAdjointOperator n) :
    bkmDikinQuadratic D h A = 0 ↔ A = 0 := by
  unfold bkmDikinQuadratic
  constructor
  · intro hA
    apply Subtype.ext
    exact (D.kuboMoriPairing_self_eq_zero_iff A.1 h).mp hA
  · intro hA
    subst hA
    simp

theorem bkmDikinQuadraticAt_eq_zero_iff
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (C A : SelfAdjointOperator n) :
    bkmDikinQuadratic D h (C - A) = 0 ↔ C = A := by
  rw [bkmDikinQuadratic_eq_zero_iff D h]
  exact sub_eq_zero

theorem inBkmDikinEllipsoidAt_radius_zero_iff
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (C A : SelfAdjointOperator n) :
    InBkmDikinEllipsoidAt D h C A 0 ↔ C = A := by
  constructor
  · intro hCA
    have hzero : bkmDikinQuadratic D h (C - A) = 0 := by
      apply le_antisymm
      · simpa [InBkmDikinEllipsoidAt] using hCA
      · exact bkmDikinQuadratic_nonneg D h (C - A)
    exact (bkmDikinQuadraticAt_eq_zero_iff D h C A).mp hzero
  · intro hCA
    rw [hCA]
    exact inBkmDikinEllipsoidAt_center D h A

theorem inBkmDikinEllipsoid_mono_radius
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : SelfAdjointOperator n) {r s : ℝ}
    (hrs : r ^ 2 ≤ s ^ 2)
    (hA : InBkmDikinEllipsoid D h A r) :
    InBkmDikinEllipsoid D h A s := by
  exact le_trans hA hrs

/-- A BKM-isometric linear transition transports Dikin constraints without
changing their radius.  This is the native preservation law required of a
future filtered-stage bonding map. -/
theorem bkmDikinEllipsoid_preimage
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (L : SelfAdjointOperator n →ₗ[ℝ] SelfAdjointOperator n)
    (hL : ∀ A : SelfAdjointOperator n,
      bkmDikinQuadratic D h (L A) = bkmDikinQuadratic D h A)
    (A : SelfAdjointOperator n) (r : ℝ) :
    InBkmDikinEllipsoid D h (L A) r ↔
      InBkmDikinEllipsoid D h A r := by
  simp only [InBkmDikinEllipsoid]
  rw [hL A]

/-- Combining metric preservation with radius enlargement transports a BKM
Dikin constraint along a finite-stage transition. -/
theorem bkmDikinEllipsoid_map_mono_radius
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (L : SelfAdjointOperator n →ₗ[ℝ] SelfAdjointOperator n)
    (hL : ∀ A : SelfAdjointOperator n,
      bkmDikinQuadratic D h (L A) = bkmDikinQuadratic D h A)
    (A : SelfAdjointOperator n) {r s : ℝ}
    (hrs : r ^ 2 ≤ s ^ 2)
    (hA : InBkmDikinEllipsoid D h A r) :
    InBkmDikinEllipsoid D h (L A) s := by
  have hAs : InBkmDikinEllipsoid D h A s :=
    inBkmDikinEllipsoid_mono_radius D h A hrs hA
  exact (bkmDikinEllipsoid_preimage D h L hL A s).mpr hAs

end

end InfoGeometry.Canonical.DikinFiniteOrbitColimit
