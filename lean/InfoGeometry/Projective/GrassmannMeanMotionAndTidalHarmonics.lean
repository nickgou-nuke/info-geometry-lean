/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Projective.GrassmannMechanicsBarycenterAndPotentials
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# Grassmann's *Mechanik* (1877) §§5–6: Mean Motion, Elliptic Kepler Terms, and Tidal Harmonics

This module formalizes Archetypes `GM₅` (`§5`, `pp. 231–236`, `Eqs. (10)–(11)`) and
`GM₆` (`§6`, `pp. 236–240`, `Eqs. (12)–(16)`) from Hermann Grassmann's *Die Mechanik
nach den Principien der Ausdehnungslehre* (*Mathematische Annalen* 12, 1877, pp. 231–240):

1. **`GM₅` (`§5`, Linear Equations & Mean Motion)**:
   - Exponential forcing pencil `dynPencil A B κ = κ² I + κ A + B`, unique non-resonant
     particular solution when `IsUnit (dynPencil A B κ).det`, and homogeneous characteristic
     resonance iff `det (dynPencil A B lam) = 0`.
   - Real harmonic particular solution `u(t) = cos(κt) a + sin(κt) b` (`p. 234`).
   - Exact antiderivatives and uniform oscillatory bounds proving Grassmann's mean-motion
     kinetic-energy minimization theorem: any nonzero free oscillation `(p, q)` at frequency
     `β ≠ κ` strictly increases `∫₀ᵀ T dt` by at least `(1/8) β² (p² + q²) T` for large `T`.
   - Elliptic terms (`ellipticTerm`, `ellipticVel`): periodicity, conjugate semi-diameter
     circle equation, and constant exterior bivector areal velocity `½ [r δr] = (κ/2) [a b]`.
2. **`GM₆` (`§6`, Rotating Earth & Theory of Ebbe und Fluth)**:
   - Noncommutative rotating-frame generator `rotGen eHat n v = n • (eHat ⨯₃ v)`, proof of
     Grassmann's exact `p. 236` warning `rotGen²(v) = -n² (v - (eHat ⬝ᵥ v) eHat)`, and
     rotating Coriolis/centrifugal equations `Eqs. (12)–(13)`.
   - Directional derivative proof of the tidal quadrupole force `(L/ρ³)((3(r⬝x)/ρ²)r - x)`
     (`p. 237`), barycentric vanishing, spherical-cosine `3`-harmonic `{0, γ, 2γ}` identity,
     two-body five-harmonic *Ebbe und Fluth Hauptsatz* (`Eqs. (14)–(15)`), the `24 → 8`
     Laplace vertical-projection surjection (`p. 239`), and sea-surface `Eq. (16)`.
-/

noncomputable section

namespace InfoGeometry.Projective.GrassmannMeanMotionAndTidalHarmonics

open Matrix ExteriorAlgebra Real
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Projective.GrassmannMechanicsBarycenterAndPotentials

section Sec5LinearMeanMotionAndKepler

/-- Characteristic second-order matrix pencil `κ² I + κ A + B` (`§5`, `p. 233`, `Eq. (11)`). -/
def dynPencil {K : Type*} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) (κ : K) : Matrix (Fin n) (Fin n) K :=
  (κ ^ 2) • (1 : Matrix (Fin n) (Fin n) K) + κ • A + B

private lemma hasDerivAt_mul_const_left (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => κ * s) κ t := by
  convert (hasDerivAt_id t).const_mul κ using 1
  · rfl
  · exact (mul_one κ).symm

private lemma hasDerivAt_exp_mul (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (κ * s)) (κ * Real.exp (κ * t)) t := by
  convert (Real.hasDerivAt_exp (κ * t)).comp t (hasDerivAt_mul_const_left κ t) using 1
  · rfl
  · exact mul_comm κ (Real.exp (κ * t))

private lemma hasDerivAt_cos_mul (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos (κ * s)) (-Real.sin (κ * t) * κ) t :=
  (Real.hasDerivAt_cos (κ * t)).comp t (hasDerivAt_mul_const_left κ t)

private lemma hasDerivAt_sin_mul (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (κ * s)) (Real.cos (κ * t) * κ) t :=
  (Real.hasDerivAt_sin (κ * t)).comp t (hasDerivAt_mul_const_left κ t)

private lemma ext3_ι_self (x : Vec3) :
    ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ x = 0 :=
  ExteriorAlgebra.ι_sq_zero (R := ℝ) x

private lemma ext3_ι_anticomm (x y : Vec3) :
    ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ y =
      -(ExteriorAlgebra.ι ℝ y * ExteriorAlgebra.ι ℝ x) := by
  have hsq : ExteriorAlgebra.ι ℝ (x + y) * ExteriorAlgebra.ι ℝ (x + y) = 0 := ext3_ι_self (x + y)
  have h1 : ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ x = 0 := ext3_ι_self x
  have h2 : ExteriorAlgebra.ι ℝ y * ExteriorAlgebra.ι ℝ y = 0 := ext3_ι_self y
  rw [map_add, add_mul, mul_add, mul_add, h1, h2, zero_add, add_zero] at hsq
  exact eq_neg_of_add_eq_zero_left hsq

/-- Derivative helper for `t ↦ exp (κ * t) • y`. -/
theorem hasDerivAt_exp_smul {n : ℕ} (y : Fin n → ℝ) (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (κ * s) • y) ((κ * Real.exp (κ * t)) • y) t := by
  rw [hasDerivAt_pi]
  intro i
  convert (hasDerivAt_exp_mul κ t).mul_const (y i) using 1

/-- Second derivative helper for `t ↦ exp (κ * t) • y`. -/
theorem hasDerivAt_exp_vel_smul {n : ℕ} (y : Fin n → ℝ) (κ t : ℝ) :
    HasDerivAt (fun s : ℝ => (κ * Real.exp (κ * s)) • y)
      ((κ ^ 2 * Real.exp (κ * t)) • y) t := by
  rw [hasDerivAt_pi]
  intro i
  have hexp : HasDerivAt (fun s : ℝ => κ * Real.exp (κ * s)) (κ * (κ * Real.exp (κ * t))) t :=
    (hasDerivAt_exp_mul κ t).const_mul κ
  convert hexp.mul_const (y i) using 1
  dsimp only [Pi.smul_apply]
  rw [smul_eq_mul]
  ring

/-- Exponential particular-mode theorem `Eqs. (10)–(11)` (`§5`, `pp. 232–233`). -/
theorem expMode_solves_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (y g : Fin n → ℝ) (κ : ℝ) :
    let u : ℝ → Fin n → ℝ := fun t => Real.exp (κ * t) • y
    let du : ℝ → Fin n → ℝ := fun t => (κ * Real.exp (κ * t)) • y
    let ddu : ℝ → Fin n → ℝ := fun t => (κ ^ 2 * Real.exp (κ * t)) • y
    (∀ t, HasDerivAt u (du t) t ∧ HasDerivAt du (ddu t) t) ∧
      ((∀ t, ddu t + A *ᵥ du t + B *ᵥ u t = Real.exp (κ * t) • g) ↔
        dynPencil A B κ *ᵥ y = g) := by
  refine ⟨fun t => ⟨hasDerivAt_exp_smul y κ t, hasDerivAt_exp_vel_smul y κ t⟩, ?_⟩
  have hfold : ∀ t : ℝ,
      (κ ^ 2 * Real.exp (κ * t)) • y + A *ᵥ ((κ * Real.exp (κ * t)) • y) +
          B *ᵥ (Real.exp (κ * t) • y) =
        Real.exp (κ * t) • (dynPencil A B κ *ᵥ y) := by
    intro t
    have hdu : (κ * Real.exp (κ * t)) • y = Real.exp (κ * t) • (κ • y) := by
      rw [smul_smul, mul_comm]
    rw [hdu, mulVec_smul, mulVec_smul, mulVec_smul]
    simp only [dynPencil, add_mulVec, smul_mulVec, one_mulVec, smul_add, smul_smul]
    ext i
    simp [mul_comm]
  constructor
  · intro h
    have h0 := h 0
    rw [hfold 0, mul_zero, Real.exp_zero, one_smul] at h0
    simpa [one_smul] using h0
  · intro hy t
    rw [hfold t, hy]

/-- Non-resonant invertibility of `Eq. (11)` when `(dynPencil A B κ).det ≠ 0`. -/
theorem expMode_unique_of_det_ne_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → ℝ) {κ : ℝ} (hdet : (dynPencil A B κ).det ≠ 0) :
    ∃! y : Fin n → ℝ, dynPencil A B κ *ᵥ y = g := by
  have hu : IsUnit (dynPencil A B κ).det := isUnit_iff_ne_zero.mpr hdet
  refine ⟨(dynPencil A B κ)⁻¹ *ᵥ g, ?_, ?_⟩
  · dsimp only; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  · intro y hy
    calc
      y = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ y := (Matrix.one_mulVec y).symm
      _ = ((dynPencil A B κ)⁻¹ * dynPencil A B κ) *ᵥ y := by rw [Matrix.nonsing_inv_mul _ hu]
      _ = (dynPencil A B κ)⁻¹ *ᵥ (dynPencil A B κ *ᵥ y) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = (dynPencil A B κ)⁻¹ *ᵥ g := by rw [hy]

/-- Homogeneous characteristic resonance equation of degree `2n` (`§5`, `p. 233`). -/
theorem homogResonance_iff_det_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (lam : ℝ) :
    (∃ z : Fin n → ℝ, z ≠ 0 ∧ dynPencil A B lam *ᵥ z = 0) ↔
      (dynPencil A B lam).det = 0 :=
  Matrix.exists_mulVec_eq_zero_iff

/-- Grassmann's elliptic term `a cos(κt) + b sin(κt)` (`§5`, `p. 235`). -/
def ellipticTerm {n : ℕ} (a b : Fin n → ℝ) (κ t : ℝ) : Fin n → ℝ :=
  Real.cos (κ * t) • a + Real.sin (κ * t) • b

/-- Velocity `δr = κ(b cos(κt) - a sin(κt))` of an elliptic term (`§5`, `p. 235`). -/
def ellipticVel {n : ℕ} (a b : Fin n → ℝ) (κ t : ℝ) : Fin n → ℝ :=
  κ • (Real.cos (κ * t) • b - Real.sin (κ * t) • a)

/-- Acceleration `δ²r = -κ² r` of an elliptic term (`§5`, `p. 234`). -/
def ellipticAcc {n : ℕ} (a b : Fin n → ℝ) (κ t : ℝ) : Fin n → ℝ :=
  (-κ ^ 2) • ellipticTerm a b κ t

theorem hasDerivAt_ellipticTerm {n : ℕ} (a b : Fin n → ℝ) (κ t : ℝ) :
    HasDerivAt (ellipticTerm a b κ) (ellipticVel a b κ t) t := by
  rw [hasDerivAt_pi]
  intro i
  have hd := ((hasDerivAt_cos_mul κ t).mul_const (a i)).add
    ((hasDerivAt_sin_mul κ t).mul_const (b i))
  convert hd using 1
  · funext s; rfl
  · dsimp only [ellipticVel, Pi.smul_apply, Pi.sub_apply]
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring

theorem hasDerivAt_ellipticVel {n : ℕ} (a b : Fin n → ℝ) (κ t : ℝ) :
    HasDerivAt (ellipticVel a b κ) (ellipticAcc a b κ t) t := by
  rw [hasDerivAt_pi]
  intro i
  have hd := (((hasDerivAt_cos_mul κ t).mul_const (b i)).sub
    ((hasDerivAt_sin_mul κ t).mul_const (a i))).const_mul κ
  convert hd using 1
  · funext s; rfl
  · dsimp only [ellipticAcc, ellipticTerm, Pi.smul_apply, Pi.add_apply]
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring

/-- Real harmonic mean-integral theorem (`§5`, `p. 234`):
an elliptic response solves `u'' + A u' + B u = cos(κt) c + sin(κt) c'`. -/
theorem harmonic_mean_integral_solves {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (a b c c' : Fin n → ℝ) (κ : ℝ)
    (hc : ((-(κ ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) + B) *ᵥ a + κ • (A *ᵥ b)) = c)
    (hc' : (-(κ • (A *ᵥ a)) + (-(κ ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) + B) *ᵥ b) = c')
    (t : ℝ) :
    ellipticAcc a b κ t + A *ᵥ ellipticVel a b κ t + B *ᵥ ellipticTerm a b κ t =
      ellipticTerm c c' κ t := by
  have hAvel : A *ᵥ ellipticVel a b κ t =
      Real.cos (κ * t) • (κ • (A *ᵥ b)) - Real.sin (κ * t) • (κ • (A *ᵥ a)) := by
    rw [ellipticVel, mulVec_smul, sub_eq_add_neg, mulVec_add, mulVec_neg, mulVec_smul, mulVec_smul]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hBterm : B *ᵥ ellipticTerm a b κ t =
      Real.cos (κ * t) • (B *ᵥ a) + Real.sin (κ * t) • (B *ᵥ b) := by
    rw [ellipticTerm, mulVec_add, mulVec_smul, mulVec_smul]
  rw [ellipticAcc, hAvel, hBterm, ← hc, ← hc']
  simp only [ellipticTerm, add_mulVec, smul_mulVec, one_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem ellipticTerm_periodic {n : ℕ} (a b : Fin n → ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℝ) :
    ellipticTerm a b κ (t + 2 * Real.pi / κ) = ellipticTerm a b κ t := by
  have harg : κ * (t + 2 * Real.pi / κ) = κ * t + 2 * Real.pi := by
    field_simp [hκ]
  simp only [ellipticTerm, harg, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem elliptic_conjugate_diameters (κ t : ℝ) :
    Real.cos (κ * t) ^ 2 + Real.sin (κ * t) ^ 2 = 1 := by
  rw [add_comm]
  exact Real.sin_sq_add_cos_sq (κ * t)

/-- Kepler's area law for Grassmann's *elliptische Glieder* (`§5`, `p. 235`):
`½ [r δr] = ½ κ [a b]` constant in time in the exterior algebra. -/
theorem elliptic_areal_velocity (a b : Vec3) (κ t : ℝ) :
    (1 / 2 : ℝ) • (ExteriorAlgebra.ι ℝ (ellipticTerm a b κ t) *
        ExteriorAlgebra.ι ℝ (ellipticVel a b κ t)) =
      (κ / 2) • (ExteriorAlgebra.ι ℝ a * ExteriorAlgebra.ι ℝ b) := by
  simp only [ellipticTerm, ellipticVel]
  rw [map_add, map_smul, map_smul, map_smul, map_sub, map_smul, map_smul]
  rw [mul_smul_comm, add_mul, mul_sub, mul_sub]
  simp only [smul_mul_assoc, mul_smul_comm, ext3_ι_self, smul_zero, sub_zero, zero_sub]
  rw [ext3_ι_anticomm b a, smul_neg, smul_neg, neg_neg, smul_smul, smul_smul, smul_smul, ← add_smul]
  have hcs : Real.cos (κ * t) * Real.cos (κ * t) + Real.sin (κ * t) * Real.sin (κ * t) = 1 := by
    have h1 := Real.sin_sq_add_cos_sq (κ * t)
    linear_combination h1
  rw [hcs, one_smul]
  congr 1
  ring

/-- Scalar integrand `½ κ² (b cos(κt) - a sin(κt))²` for one harmonic component. -/
def diagKineticIntegrand (a b κ t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * κ ^ 2 * (b * Real.cos (κ * t) - a * Real.sin (κ * t)) ^ 2

/-- Exact antiderivative of `diagKineticIntegrand`, vanishing at `T = 0` (`§5`, `p. 234`). -/
def diagKineticAntideriv (a b κ T : ℝ) : ℝ :=
  (1 / 4 : ℝ) * κ ^ 2 * (a ^ 2 + b ^ 2) * T +
    (1 / 8 : ℝ) * κ * (b ^ 2 - a ^ 2) * Real.sin (2 * κ * T) -
    (1 / 4 : ℝ) * κ * a * b * (1 - Real.cos (2 * κ * T))

@[simp]
theorem diagKineticAntideriv_zero (a b κ : ℝ) :
    diagKineticAntideriv a b κ 0 = 0 := by
  unfold diagKineticAntideriv
  rw [mul_zero, mul_zero, Real.sin_zero, Real.cos_zero]
  ring

theorem hasDerivAt_diagKineticAntideriv (a b κ T : ℝ) :
    HasDerivAt (diagKineticAntideriv a b κ) (diagKineticIntegrand a b κ T) T := by
  have h1 : HasDerivAt (fun s => (1 / 4 : ℝ) * κ ^ 2 * (a ^ 2 + b ^ 2) * s)
      ((1 / 4 : ℝ) * κ ^ 2 * (a ^ 2 + b ^ 2)) T := by
    convert (hasDerivAt_id T).const_mul ((1 / 4 : ℝ) * κ ^ 2 * (a ^ 2 + b ^ 2)) using 1
    · funext s; dsimp only [id]
    · ring
  have h2 : HasDerivAt (fun s => (1 / 8 : ℝ) * κ * (b ^ 2 - a ^ 2) * Real.sin (2 * κ * s))
      ((1 / 8 : ℝ) * κ * (b ^ 2 - a ^ 2) * (Real.cos (2 * κ * T) * (2 * κ))) T :=
    (hasDerivAt_sin_mul (2 * κ) T).const_mul ((1 / 8 : ℝ) * κ * (b ^ 2 - a ^ 2))
  have hcos : HasDerivAt (fun s => 1 - Real.cos (2 * κ * s))
      (0 - (-Real.sin (2 * κ * T) * (2 * κ))) T :=
    (hasDerivAt_const T 1).sub (hasDerivAt_cos_mul (2 * κ) T)
  have h3 : HasDerivAt (fun s => (1 / 4 : ℝ) * κ * a * b * (1 - Real.cos (2 * κ * s)))
      ((1 / 4 : ℝ) * κ * a * b * (0 - (-Real.sin (2 * κ * T) * (2 * κ)))) T :=
    hcos.const_mul ((1 / 4 : ℝ) * κ * a * b)
  convert (h1.add h2).sub h3 using 1
  · funext s; rfl
  · have hcos2 : Real.cos (2 * κ * T) = 2 * Real.cos (κ * T) ^ 2 - 1 := by
      rw [mul_assoc 2 κ T, Real.cos_two_mul]
    have hsin2 : Real.sin (2 * κ * T) = 2 * Real.sin (κ * T) * Real.cos (κ * T) := by
      rw [mul_assoc 2 κ T, Real.sin_two_mul]
    have hcos_sq : Real.cos (κ * T) ^ 2 = 1 - Real.sin (κ * T) ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq (κ * T)]
    unfold diagKineticIntegrand
    rw [hcos2, hsin2]
    ring_nf
    rw [hcos_sq]
    ring

theorem diagKineticAntideriv_rem_bound (a b κ T : ℝ) :
    |diagKineticAntideriv a b κ T - (1 / 4 : ℝ) * κ ^ 2 * (a ^ 2 + b ^ 2) * T| ≤
      (1 / 8 : ℝ) * |κ| * |b ^ 2 - a ^ 2| + (1 / 2 : ℝ) * |κ * a * b| := by
  have hsub : diagKineticAntideriv a b κ T - (1 / 4 : ℝ) * κ ^ 2 * (a ^ 2 + b ^ 2) * T =
      (1 / 8 : ℝ) * κ * (b ^ 2 - a ^ 2) * Real.sin (2 * κ * T) -
        (1 / 4 : ℝ) * κ * a * b * (1 - Real.cos (2 * κ * T)) := by
    simp only [diagKineticAntideriv]; ring
  rw [hsub]
  have h1 : |(1 / 8 : ℝ) * κ * (b ^ 2 - a ^ 2) * Real.sin (2 * κ * T)| ≤
      (1 / 8 : ℝ) * |κ| * |b ^ 2 - a ^ 2| := by
    rw [abs_mul, abs_mul, abs_mul]
    calc
      |(1 / 8 : ℝ)| * |κ| * |b ^ 2 - a ^ 2| * |Real.sin (2 * κ * T)|
          ≤ (1 / 8 : ℝ) * |κ| * |b ^ 2 - a ^ 2| * 1 := by
            gcongr
            · norm_num
            · exact Real.abs_sin_le_one _
      _ = (1 / 8 : ℝ) * |κ| * |b ^ 2 - a ^ 2| := mul_one _
  have h2 : |(1 / 4 : ℝ) * κ * a * b * (1 - Real.cos (2 * κ * T))| ≤ (1 / 2 : ℝ) * |κ * a * b| := by
    have hcos_le : |1 - Real.cos (2 * κ * T)| ≤ 2 := by
      calc
        |1 - Real.cos (2 * κ * T)| ≤ |(1 : ℝ)| + |Real.cos (2 * κ * T)| := abs_sub _ _
        _ ≤ 1 + 1 := by gcongr; norm_num; exact Real.abs_cos_le_one _
        _ = 2 := by norm_num
    have hrew : (1 / 4 : ℝ) * κ * a * b * (1 - Real.cos (2 * κ * T)) =
        (1 / 4 : ℝ) * (κ * a * b) * (1 - Real.cos (2 * κ * T)) := by ring
    rw [hrew, abs_mul, abs_mul]
    calc
      |(1 / 4 : ℝ)| * |κ * a * b| * |1 - Real.cos (2 * κ * T)|
          ≤ (1 / 4 : ℝ) * |κ * a * b| * 2 := by
            gcongr; norm_num
      _ = (1 / 2 : ℝ) * |κ * a * b| := by ring
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-- Cross-product integrand between modes `κ` and `β` (`§5`, `pp. 234–235`). -/
def crossKineticIntegrand (a b p q κ β t : ℝ) : ℝ :=
  κ * β * (b * Real.cos (κ * t) - a * Real.sin (κ * t)) *
    (q * Real.cos (β * t) - p * Real.sin (β * t))

/-- Exact trigonometric antiderivative of `crossKineticIntegrand` for `κ ≠ ±β`, vanishing at `0`. -/
def crossKineticAntideriv (a b p q κ β T : ℝ) : ℝ :=
  (κ * β / 2) *
    (((b * q - a * p) / (κ + β)) * Real.sin ((κ + β) * T) +
      ((b * q + a * p) / (κ - β)) * Real.sin ((κ - β) * T) -
      ((b * p + a * q) / (κ + β)) * (1 - Real.cos ((κ + β) * T)) +
      ((b * p - a * q) / (κ - β)) * (1 - Real.cos ((κ - β) * T)))

@[simp]
theorem crossKineticAntideriv_zero (a b p q κ β : ℝ) :
    crossKineticAntideriv a b p q κ β 0 = 0 := by
  unfold crossKineticAntideriv
  rw [mul_zero, mul_zero, Real.sin_zero, Real.cos_zero]
  ring

theorem hasDerivAt_crossKineticAntideriv (a b p q κ β T : ℝ)
    (hsum : κ + β ≠ 0) (hdiff : κ - β ≠ 0) :
    HasDerivAt (crossKineticAntideriv a b p q κ β) (crossKineticIntegrand a b p q κ β T) T := by
  have hs1 : HasDerivAt (fun s => Real.sin ((κ + β) * s))
      (Real.cos ((κ + β) * T) * (κ + β)) T := hasDerivAt_sin_mul (κ + β) T
  have hs2 : HasDerivAt (fun s => Real.sin ((κ - β) * s))
      (Real.cos ((κ - β) * T) * (κ - β)) T := hasDerivAt_sin_mul (κ - β) T
  have hc1 : HasDerivAt (fun s => 1 - Real.cos ((κ + β) * s))
      (Real.sin ((κ + β) * T) * (κ + β)) T := by
    convert (hasDerivAt_const T 1).sub (hasDerivAt_cos_mul (κ + β) T) using 1
    ring
  have hc2 : HasDerivAt (fun s => 1 - Real.cos ((κ - β) * s))
      (Real.sin ((κ - β) * T) * (κ - β)) T := by
    convert (hasDerivAt_const T 1).sub (hasDerivAt_cos_mul (κ - β) T) using 1
    ring
  have hbig :=
    ((((hs1.const_mul ((b * q - a * p) / (κ + β))).add
      (hs2.const_mul ((b * q + a * p) / (κ - β)))).sub
      (hc1.const_mul ((b * p + a * q) / (κ + β)))).add
      (hc2.const_mul ((b * p - a * q) / (κ - β)))).const_mul (κ * β / 2)
  convert hbig using 1
  · funext s; rfl
  · have hcos_sum : Real.cos ((κ + β) * T) =
        Real.cos (κ * T) * Real.cos (β * T) - Real.sin (κ * T) * Real.sin (β * T) := by
      rw [add_mul, Real.cos_add]
    have hcos_diff : Real.cos ((κ - β) * T) =
        Real.cos (κ * T) * Real.cos (β * T) + Real.sin (κ * T) * Real.sin (β * T) := by
      rw [sub_mul, Real.cos_sub]
    have hsin_sum : Real.sin ((κ + β) * T) =
        Real.sin (κ * T) * Real.cos (β * T) + Real.cos (κ * T) * Real.sin (β * T) := by
      rw [add_mul, Real.sin_add]
    have hsin_diff : Real.sin ((κ - β) * T) =
        Real.sin (κ * T) * Real.cos (β * T) - Real.cos (κ * T) * Real.sin (β * T) := by
      rw [sub_mul, Real.sin_sub]
    unfold crossKineticIntegrand
    rw [hcos_sum, hcos_diff, hsin_sum, hsin_diff]
    field_simp [hsum, hdiff]
    ring

theorem crossKineticAntideriv_bound (a b p q κ β T : ℝ) :
    |crossKineticAntideriv a b p q κ β T| ≤
      (|κ * β| / 2) *
        (|(b * q - a * p) / (κ + β)| + |(b * q + a * p) / (κ - β)| +
          2 * |(b * p + a * q) / (κ + β)| + 2 * |(b * p - a * q) / (κ - β)|) := by
  have hsin1 : |((b * q - a * p) / (κ + β)) * Real.sin ((κ + β) * T)| ≤
      |(b * q - a * p) / (κ + β)| := by
    rw [abs_mul]
    calc
      |(b * q - a * p) / (κ + β)| * |Real.sin ((κ + β) * T)|
          ≤ |(b * q - a * p) / (κ + β)| * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = |(b * q - a * p) / (κ + β)| := mul_one _
  have hsin2 : |((b * q + a * p) / (κ - β)) * Real.sin ((κ - β) * T)| ≤
      |(b * q + a * p) / (κ - β)| := by
    rw [abs_mul]
    calc
      |(b * q + a * p) / (κ - β)| * |Real.sin ((κ - β) * T)|
          ≤ |(b * q + a * p) / (κ - β)| * 1 := by gcongr; exact Real.abs_sin_le_one _
      _ = |(b * q + a * p) / (κ - β)| := mul_one _
  have hcos1 : |((b * p + a * q) / (κ + β)) * (1 - Real.cos ((κ + β) * T))| ≤
      2 * |(b * p + a * q) / (κ + β)| := by
    have hc : |1 - Real.cos ((κ + β) * T)| ≤ 2 := by
      calc
        |1 - Real.cos ((κ + β) * T)| ≤ |(1 : ℝ)| + |Real.cos ((κ + β) * T)| := abs_sub _ _
        _ ≤ 1 + 1 := by gcongr; norm_num; exact Real.abs_cos_le_one _
        _ = 2 := by norm_num
    rw [abs_mul]
    calc
      |(b * p + a * q) / (κ + β)| * |1 - Real.cos ((κ + β) * T)|
          ≤ |(b * p + a * q) / (κ + β)| * 2 := by gcongr
      _ = 2 * |(b * p + a * q) / (κ + β)| := mul_comm _ _
  have hcos2 : |((b * p - a * q) / (κ - β)) * (1 - Real.cos ((κ - β) * T))| ≤
      2 * |(b * p - a * q) / (κ - β)| := by
    have hc : |1 - Real.cos ((κ - β) * T)| ≤ 2 := by
      calc
        |1 - Real.cos ((κ - β) * T)| ≤ |(1 : ℝ)| + |Real.cos ((κ - β) * T)| := abs_sub _ _
        _ ≤ 1 + 1 := by gcongr; norm_num; exact Real.abs_cos_le_one _
        _ = 2 := by norm_num
    rw [abs_mul]
    calc
      |(b * p - a * q) / (κ - β)| * |1 - Real.cos ((κ - β) * T)|
          ≤ |(b * p - a * q) / (κ - β)| * 2 := by gcongr
      _ = 2 * |(b * p - a * q) / (κ - β)| := mul_comm _ _
  have htri := abs_add_le
    (((b * q - a * p) / (κ + β)) * Real.sin ((κ + β) * T) +
      ((b * q + a * p) / (κ - β)) * Real.sin ((κ - β) * T) -
      ((b * p + a * q) / (κ + β)) * (1 - Real.cos ((κ + β) * T)))
    (((b * p - a * q) / (κ - β)) * (1 - Real.cos ((κ - β) * T)))
  have htri2 := abs_sub
    (((b * q - a * p) / (κ + β)) * Real.sin ((κ + β) * T) +
      ((b * q + a * p) / (κ - β)) * Real.sin ((κ - β) * T))
    (((b * p + a * q) / (κ + β)) * (1 - Real.cos ((κ + β) * T)))
  have htri3 := abs_add_le
    (((b * q - a * p) / (κ + β)) * Real.sin ((κ + β) * T))
    (((b * q + a * p) / (κ - β)) * Real.sin ((κ - β) * T))
  have hsum_le :
      |((b * q - a * p) / (κ + β)) * Real.sin ((κ + β) * T) +
          ((b * q + a * p) / (κ - β)) * Real.sin ((κ - β) * T) -
          ((b * p + a * q) / (κ + β)) * (1 - Real.cos ((κ + β) * T)) +
          ((b * p - a * q) / (κ - β)) * (1 - Real.cos ((κ - β) * T))| ≤
        |(b * q - a * p) / (κ + β)| + |(b * q + a * p) / (κ - β)| +
          2 * |(b * p + a * q) / (κ + β)| + 2 * |(b * p - a * q) / (κ - β)| := by
    linarith
  rw [crossKineticAntideriv, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact mul_le_mul_of_nonneg_left hsum_le (div_nonneg (abs_nonneg _) (by norm_num))

/-- Total integrated kinetic energy `∫₀ᵀ ½ (v_κ + v_β)² dt` for superposed harmonic modes. -/
def totalKineticAntideriv (a b p q κ β T : ℝ) : ℝ :=
  diagKineticAntideriv a b κ T + diagKineticAntideriv p q β T +
    crossKineticAntideriv a b p q κ β T

/-- Grassmann's Mean-Motion Kinetic-Energy Minimization Theorem (`§5`, `pp. 234–235`):
any nonvanishing free oscillation `(p, q) ≠ (0, 0)` at eigenfrequency `β ≠ κ` strictly increases
the integrated kinetic energy above the mean integral `diagKineticAntideriv` for all large `T`. -/
theorem meanMotion_strictly_minimizes_integrated_kinetic_energy
    (a b p q κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β) (hne : κ ≠ β)
    (hpq : p ≠ 0 ∨ q ≠ 0) :
    (∀ T, HasDerivAt (totalKineticAntideriv a b p q κ β)
      ((1 / 2 : ℝ) * ((κ * (b * Real.cos (κ * T) - a * Real.sin (κ * T)) +
        β * (q * Real.cos (β * T) - p * Real.sin (β * T))) ^ 2)) T) ∧
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (1 / 8 : ℝ) * β ^ 2 * (p ^ 2 + q ^ 2) * T ≤
        totalKineticAntideriv a b p q κ β T - diagKineticAntideriv a b κ T ∧
      0 < totalKineticAntideriv a b p q κ β T - diagKineticAntideriv a b κ T := by
  have hsum : κ + β ≠ 0 := (add_pos hκ hβ).ne'
  have hdiff : κ - β ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · intro T
    have hd := ((hasDerivAt_diagKineticAntideriv a b κ T).add
      (hasDerivAt_diagKineticAntideriv p q β T)).add
      (hasDerivAt_crossKineticAntideriv a b p q κ β T hsum hdiff)
    convert hd using 1
    · funext s; rfl
    · unfold diagKineticIntegrand crossKineticIntegrand
      ring
  · have hpq_pos : 0 < p ^ 2 + q ^ 2 := by
      rcases hpq with hp | hq
      · positivity
      · positivity
    let c₀ : ℝ := (1 / 8 : ℝ) * β ^ 2 * (p ^ 2 + q ^ 2)
    have hc₀ : 0 < c₀ := by
      simp only [c₀]; positivity
    let B₁ := (1 / 8 : ℝ) * |β| * |q ^ 2 - p ^ 2| + (1 / 2 : ℝ) * |β * p * q|
    let B₂ := (|κ * β| / 2) *
      (|(b * q - a * p) / (κ + β)| + |(b * q + a * p) / (κ - β)| +
        2 * |(b * p + a * q) / (κ + β)| + 2 * |(b * p - a * q) / (κ - β)|)
    let T₀ := max 1 ((B₁ + B₂) / c₀)
    have hT₀ : 0 < T₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    refine ⟨T₀, hT₀, fun T hT => ?_⟩
    have hTpos : 0 < T := lt_of_lt_of_le hT₀ hT
    have hD := diagKineticAntideriv_rem_bound p q β T
    have hC := crossKineticAntideriv_bound a b p q κ β T
    have habsD : -B₁ ≤ diagKineticAntideriv p q β T - (1 / 4 : ℝ) * β ^ 2 * (p ^ 2 + q ^ 2) * T :=
      neg_le_of_abs_le hD
    have habsC : -B₂ ≤ crossKineticAntideriv a b p q κ β T :=
      neg_le_of_abs_le hC
    have hsplit : totalKineticAntideriv a b p q κ β T - diagKineticAntideriv a b κ T =
        2 * (c₀ * T) +
          (diagKineticAntideriv p q β T - (1 / 4 : ℝ) * β ^ 2 * (p ^ 2 + q ^ 2) * T) +
          crossKineticAntideriv a b p q κ β T := by
      simp only [totalKineticAntideriv, c₀]; ring
    have hB : B₁ + B₂ ≤ c₀ * T := by
      have hdiv : (B₁ + B₂) / c₀ ≤ T := le_trans (le_max_right _ _) hT
      exact (div_le_iff₀ hc₀).mp hdiv |>.trans_eq (mul_comm _ _)
    have hlow : c₀ * T ≤ totalKineticAntideriv a b p q κ β T - diagKineticAntideriv a b κ T := by
      linarith
    exact ⟨hlow, lt_of_lt_of_le (mul_pos hc₀ hTpos) hlow⟩

end Sec5LinearMeanMotionAndKepler

section Sec6RotatingFrameAndTides

/-- Rotating-frame cross-product generator `v ↦ n • (eHat ⨯₃ v)` (`§6`, `p. 236`). -/
def rotGen (eHat : Vec3) (n : ℝ) (v : Vec3) : Vec3 :=
  n • (eHat ⨯₃ v)

/-- Linear matrix of `rotGen eHat n` on `Vec3`. -/
def rotGenMatrix (eHat : Vec3) (n : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => rotGen eHat n (Pi.single j 1) i

theorem rotGenMatrix_mulVec (eHat : Vec3) (n : ℝ) (v : Vec3) :
    rotGenMatrix eHat n *ᵥ v = rotGen eHat n v := by
  have hv : v = ∑ j : Fin 3, v j • (Pi.single j (1 : ℝ) : Vec3) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  nth_rw 2 [hv]
  simp only [rotGen, map_sum, map_smul, Finset.smul_sum, smul_comm n]
  ext i
  rw [mulVec_eq_sum]
  simp [rotGenMatrix, rotGen, Finset.sum_apply]

theorem rotGenMatrix_noncomm :
    rotGenMatrix ![1, 0, 0] 1 * rotGenMatrix ![0, 1, 0] 1 ≠
      rotGenMatrix ![0, 1, 0] 1 * rotGenMatrix ![1, 0, 0] 1 := by
  intro h
  have h10 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 0) h
  norm_num [Matrix.mul_apply, rotGenMatrix, rotGen, cross_apply, Fin.sum_univ_three] at h10

theorem rotGenMatrix_noncomm_exists :
    ∃ A B : Matrix (Fin 3) (Fin 3) ℝ, A * B ≠ B * A :=
  ⟨rotGenMatrix ![1, 0, 0] 1, rotGenMatrix ![0, 1, 0] 1, rotGenMatrix_noncomm⟩

theorem rotGen_axis_zero (eHat : Vec3) (n : ℝ) :
    rotGen eHat n eHat = 0 := by
  unfold rotGen
  rw [cross_self, smul_zero]

/-- Grassmann's rotating-frame identity (`§6`, `p. 236`):
for a unit axis `eHat`, `α²(v) = -n² (v - (eHat ⬝ᵥ v) eHat)`. -/
theorem rotGen_sq (eHat : Vec3) (he : eHat ⬝ᵥ eHat = 1) (n : ℝ) (v : Vec3) :
    rotGen eHat n (rotGen eHat n v) = -(n ^ 2) • (v - (eHat ⬝ᵥ v) • eHat) := by
  ext i
  have hdot : eHat 0 ^ 2 + eHat 1 ^ 2 + eHat 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using he
  simp only [rotGen, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, cross_apply, dotProduct,
    Fin.sum_univ_three]
  fin_cases i
  · simp; linear_combination -(n ^ 2 * v 0) * hdot
  · simp; linear_combination -(n ^ 2 * v 1) * hdot
  · simp; linear_combination -(n ^ 2 * v 2) * hdot

/-- Grassmann's explicit caution (`§6`, `p. 236`, ll. 808–812):
`α²(v) = -n² v` holds if and only if `v` is perpendicular to the rotation axis `eHat` (for `n ≠ 0`). -/
theorem rotGen_sq_pure_neg_iff (eHat : Vec3) (he : eHat ⬝ᵥ eHat = 1)
    {n : ℝ} (hn : n ≠ 0) (v : Vec3) :
    rotGen eHat n (rotGen eHat n v) = -(n ^ 2) • v ↔ eHat ⬝ᵥ v = 0 := by
  rw [rotGen_sq eHat he n v]
  constructor
  · intro h
    have hn2 : -(n ^ 2) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hn)
    have hsub : v - (eHat ⬝ᵥ v) • eHat = v := by
      have hm := congrArg ((-(n ^ 2))⁻¹ • ·) h
      rw [smul_smul, smul_smul, inv_mul_cancel₀ hn2, one_smul, one_smul] at hm
      exact hm
    have hzero : (eHat ⬝ᵥ v) • eHat = 0 := sub_eq_self.mp hsub
    have he_ne : eHat ≠ 0 := by
      intro hz; simp [hz, dotProduct] at he
    exact (smul_eq_zero.mp hzero).resolve_right he_ne
  · intro h
    rw [h, zero_smul, sub_zero]

/-- Rotating-frame Coriolis + centrifugal split (`§6`, `pp. 236–237`, `Eqs. (12)–(13)`):
separating `(x + u)` gives the equilibrium equation `x α² = q''` and linear perturbation equation. -/
theorem coriolis_centrifugal_split (eHat : Vec3) (he : eHat ⬝ᵥ eHat = 1) (n : ℝ)
    (x u du ddu : Vec3) (q0 q1 : Vec3) (hq0 : rotGen eHat n (rotGen eHat n x) = q0) :
    ddu + (2 : ℝ) • rotGen eHat n du + rotGen eHat n (rotGen eHat n (x + u)) - (q0 + q1) =
      ddu + (2 : ℝ) • rotGen eHat n du - (n ^ 2) • (u - (eHat ⬝ᵥ u) • eHat) - q1 := by
  have hadd : rotGen eHat n (rotGen eHat n (x + u)) =
      rotGen eHat n (rotGen eHat n x) + rotGen eHat n (rotGen eHat n u) := by
    simp [rotGen, map_add]
  rw [hadd, hq0, rotGen_sq eHat he n u, neg_smul]
  abel

/-- First-order gravitational tidal quadrupole force (`§6`, `p. 237`):
`(L / ρ³) ((3 (r ⬝ x) / ρ²) r - x)`. -/
def tidalQuadrupole (L ρ : ℝ) (r x : Vec3) : Vec3 :=
  (L / ρ ^ 3) • ((3 * (r ⬝ᵥ x) / ρ ^ 2) • r - x)

theorem tidalQuadrupole_barycenter_sum_zero {m : ℕ} (L ρ : ℝ) (r : Vec3) (x : Fin m → Vec3)
    (hb : ∑ i : Fin m, x i = 0) :
    ∑ i : Fin m, tidalQuadrupole L ρ r (x i) = 0 := by
  simp only [tidalQuadrupole, ← Finset.smul_sum, Finset.sum_sub_distrib, hb, sub_zero]
  have hdot : ∑ i : Fin m, (3 * (r ⬝ᵥ x i) / ρ ^ 2) • r =
      (∑ i : Fin m, 3 * (r ⬝ᵥ x i) / ρ ^ 2) • r := by
    rw [Finset.sum_smul]
  rw [hdot]
  have hsc : ∑ i : Fin m, 3 * (r ⬝ᵥ x i) / ρ ^ 2 = 0 := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← dotProduct_sum, hb, dotProduct_zero,
      mul_zero, zero_mul]
  rw [hsc, zero_smul, smul_zero]

/-- Exact directional-derivative justification of Grassmann's tidal quadrupole force (`§6`, `p. 237`):
at `s = 0`, `d/ds [ L * ‖r - s x‖⁻³ (r - s x) ] = tidalQuadrupole L ρ r x` when `‖r‖ = ρ > 0`. -/
theorem tidalQuadrupole_hasDerivAt (L ρ : ℝ) (hρ : 0 < ρ) (r x : Vec3) (hr : r ⬝ᵥ r = ρ ^ 2) :
    HasDerivAt (fun s : ℝ =>
        (L * ((r - s • x) ⬝ᵥ (r - s • x)) ^ (-(3 / 2 : ℝ))) • (r - s • x))
      (tidalQuadrupole L ρ r x) 0 := by
  let g : ℝ → ℝ := fun s => (r - s • x) ⬝ᵥ (r - s • x)
  have hg_expr : ∀ s : ℝ, g s = r ⬝ᵥ r - 2 * s * (r ⬝ᵥ x) + s ^ 2 * (x ⬝ᵥ x) := by
    intro s
    simp only [g, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm x r]
    ring
  have hg0 : g 0 = ρ ^ 2 := by simp [hg_expr 0, hr]
  have hgderiv : HasDerivAt g (-2 * (r ⬝ᵥ x)) 0 := by
    have hlin : HasDerivAt (fun s => r ⬝ᵥ r - 2 * s * (r ⬝ᵥ x) + s ^ 2 * (x ⬝ᵥ x))
        (0 - 2 * 1 * (r ⬝ᵥ x) + (2 * 0) * (x ⬝ᵥ x)) 0 := by
      have h1 := (hasDerivAt_const 0 (r ⬝ᵥ r)).sub
        (((hasDerivAt_id 0).const_mul 2).mul_const (r ⬝ᵥ x))
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * (x ⬝ᵥ x)) (2 * 0 * (x ⬝ᵥ x)) 0 := by
        convert (hasDerivAt_pow 2 (0 : ℝ)).mul_const (x ⬝ᵥ x) using 1
        norm_num
      exact h1.add h2
    convert hlin using 1
    · funext s; exact hg_expr s
    · ring
  have hgne : g 0 ≠ 0 := by rw [hg0]; positivity
  have hrpow : HasDerivAt (fun s => (g s) ^ (-(3 / 2 : ℝ)))
      ((-2 * (r ⬝ᵥ x)) * (-(3 / 2 : ℝ)) * (g 0) ^ (-(3 / 2 : ℝ) - 1)) 0 :=
    hgderiv.rpow_const (Or.inl hgne)
  have hrho_pow3 : (ρ ^ 2) ^ (-(3 / 2 : ℝ)) = 1 / ρ ^ 3 := by
    have h2 : (ρ ^ 2) ^ (-(3 / 2 : ℝ)) = ρ ^ ((2 : ℝ) * -(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
      push_cast
      rfl
    rw [h2]
    have hexp : (2 : ℝ) * -(3 / 2 : ℝ) = -3 := by ring
    rw [hexp, Real.rpow_neg hρ.le, one_div]
    norm_cast
  have hrho_pow5 : (ρ ^ 2) ^ (-(3 / 2 : ℝ) - 1) = 1 / ρ ^ 5 := by
    have h2 : (ρ ^ 2) ^ (-(3 / 2 : ℝ) - 1) = ρ ^ ((2 : ℝ) * (-(3 / 2 : ℝ) - 1)) := by
      rw [← Real.rpow_natCast ρ 2, ← Real.rpow_mul hρ.le]
      push_cast
      rfl
    rw [h2]
    have hexp : (2 : ℝ) * (-(3 / 2 : ℝ) - 1) = -5 := by ring
    rw [hexp, Real.rpow_neg hρ.le, one_div]
    norm_cast
  rw [hasDerivAt_pi]
  intro i
  have hvec : HasDerivAt (fun s : ℝ => (r - s • x) i) (-x i) 0 := by
    convert (hasDerivAt_const 0 (r i)).sub ((hasDerivAt_id 0).mul_const (x i)) using 1
    · funext s; simp
    · ring
  have hscalar : HasDerivAt (fun s => L * (g s) ^ (-(3 / 2 : ℝ)))
      (L * ((-2 * (r ⬝ᵥ x)) * (-(3 / 2 : ℝ)) * (g 0) ^ (-(3 / 2 : ℝ) - 1))) 0 :=
    hrpow.const_mul L
  have hprod := hscalar.mul hvec
  convert hprod using 1
  simp only [tidalQuadrupole, hg0, hrho_pow3, hrho_pow5, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    zero_smul, Pi.zero_apply]
  field_simp [hρ.ne']
  ring

/-- Grassmann's single-body `{0, γ, 2γ}` tidal harmonic decomposition (`§6`, `p. 238`):
substituting spherical cosine `cos φ(t) = c₀ + s₀ cos(ω₁ + γt)` and diurnal rotation
`rAxis + cos(γt) rEq - sin(γt) rPerp` yields exactly `p₀ + ellipticTerm a₁ b₁ γ t + ellipticTerm a₂ b₂ (2γ) t`. -/
theorem singleBodyTidal_three_harmonics (c₀ s₀ ω₁ γ : ℝ) (rAxis rEq rPerp : Vec3) :
    let p₀ : Vec3 :=
      c₀ • rAxis + ((1 / 2 : ℝ) * s₀ * Real.cos ω₁) • rEq +
        ((1 / 2 : ℝ) * s₀ * Real.sin ω₁) • rPerp
    let a₁ : Vec3 := c₀ • rEq + (s₀ * Real.cos ω₁) • rAxis
    let b₁ : Vec3 := (-c₀) • rPerp + (-s₀ * Real.sin ω₁) • rAxis
    let a₂ : Vec3 := ((1 / 2 : ℝ) * s₀ * Real.cos ω₁) • rEq -
      ((1 / 2 : ℝ) * s₀ * Real.sin ω₁) • rPerp
    let b₂ : Vec3 := (-(1 / 2 : ℝ) * s₀ * Real.cos ω₁) • rPerp -
      ((1 / 2 : ℝ) * s₀ * Real.sin ω₁) • rEq
    ∀ t : ℝ,
      (c₀ + s₀ * Real.cos (ω₁ + γ * t)) •
          (rAxis + Real.cos (γ * t) • rEq - Real.sin (γ * t) • rPerp) =
        p₀ + ellipticTerm a₁ b₁ γ t + ellipticTerm a₂ b₂ (2 * γ) t := by
  intro p₀ a₁ b₁ a₂ b₂ t
  have hcw : Real.cos (ω₁ + γ * t) =
      Real.cos ω₁ * Real.cos (γ * t) - Real.sin ω₁ * Real.sin (γ * t) := Real.cos_add _ _
  have h2c : Real.cos (2 * γ * t) = 2 * Real.cos (γ * t) ^ 2 - 1 := by
    rw [mul_assoc 2 γ t, Real.cos_two_mul]
  have h2s : Real.sin (2 * γ * t) = 2 * Real.sin (γ * t) * Real.cos (γ * t) := by
    rw [mul_assoc 2 γ t, Real.sin_two_mul]
  have hid := Real.sin_sq_add_cos_sq (γ * t)
  have hcos_sq : Real.cos (γ * t) ^ 2 = 1 - Real.sin (γ * t) ^ 2 := by linarith [hid]
  ext i
  simp only [p₀, a₁, b₁, a₂, b₂, ellipticTerm, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
    smul_eq_mul]
  rw [hcw, h2c, h2s]
  ring_nf
  rw [hcos_sq]
  ring

/-- Grassmann's *Hauptsatz für die Theorie der Ebbe und Fluth* (`§6`, `pp. 238–239`, `Eqs. (14)–(15)`):
superposition of solar (`γ`) and lunar (`γ'`) forcing yields a static mean shift `u₀` plus the
interference of `4` elliptic motions of frequencies `γ, 2γ, γ', 2γ'`. -/
theorem tidal_five_harmonics_hauptsatz (u₀ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : Vec3) (γ γ' t : ℝ) :
    u₀ + ellipticTerm a₁ b₁ γ t + ellipticTerm a₂ b₂ (2 * γ) t +
        ellipticTerm a₃ b₃ γ' t + ellipticTerm a₄ b₄ (2 * γ') t =
      u₀ + (Real.cos (γ * t) • a₁ + Real.sin (γ * t) • b₁) +
        (Real.cos ((2 * γ) * t) • a₂ + Real.sin ((2 * γ) * t) • b₂) +
        (Real.cos (γ' * t) • a₃ + Real.sin (γ' * t) • b₃) +
        (Real.cos ((2 * γ') * t) • a₄ + Real.sin ((2 * γ') * t) • b₄) := by
  unfold ellipticTerm
  rfl

/-- Dimension `24` of the full four-elliptic-term velocity/displacement parameter space
(`§6`, `p. 239`). -/
theorem tidal24ConstSpace_finrank :
    Module.finrank ℝ (Fin 4 → Vec3 × Vec3) = 24 := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Module.finrank_prod, Module.finrank_pi]
  norm_num

/-- Vertical projection of `4` elliptic displacements onto unit vertical axis `ξ` (`§6`, `p. 239`). -/
def laplaceVerticalProj (ξ : Vec3) : (Fin 4 → Vec3 × Vec3) →ₗ[ℝ] (Fin 4 → ℝ × ℝ) where
  toFun C k := (ξ ⬝ᵥ (C k).1, ξ ⬝ᵥ (C k).2)
  map_add' C D := by
    ext k <;> simp [dotProduct_add]
  map_smul' r C := by
    ext k <;> simp [dotProduct_smul, smul_eq_mul]

/-- Laplace reduction from `24` 3D tidal constants to `8` vertical tidal constants
(`§6`, `p. 239`, matching *Méc. Cél. IV, 3*). -/
theorem laplaceHeightSpace_finrank_and_surjective (ξ : Vec3) (hξ : ξ ≠ 0) :
    Function.Surjective (laplaceVerticalProj ξ) ∧
      Module.finrank ℝ (Fin 4 → ℝ × ℝ) = 8 := by
  have hnorm : ξ ⬝ᵥ ξ ≠ 0 := fun h => hξ (dotProduct_self_eq_zero.mp h)
  constructor
  · intro y
    refine ⟨fun k => ((ξ ⬝ᵥ ξ)⁻¹ • ((y k).1 • ξ), (ξ ⬝ᵥ ξ)⁻¹ • ((y k).2 • ξ)), ?_⟩
    ext k
    · change ξ ⬝ᵥ ((ξ ⬝ᵥ ξ)⁻¹ • ((y k).1 • ξ)) = (y k).1
      rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      field_simp [hnorm]
    · change ξ ⬝ᵥ ((ξ ⬝ᵥ ξ)⁻¹ • ((y k).2 • ξ)) = (y k).2
      rw [dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      field_simp [hnorm]
  · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Module.finrank_prod, Module.finrank_self]
    norm_num

/-- Linearized sea-surface elevation `Eq. (16)` (`§6`, `pp. 239–240`):
with `x = r₀ • ξ` (`ξ ⬝ᵥ ξ = 1`), `z = ξ ⬝ᵥ u`, and `y = x + u`, we have `y² - u² = x² + 2 r₀ z`. -/
theorem tidal_sea_surface_eq_sixteen (ξ u : Vec3) (r₀ : ℝ) :
    let x := r₀ • ξ
    let z := ξ ⬝ᵥ u
    let y := x + u
    y ⬝ᵥ y - u ⬝ᵥ u = x ⬝ᵥ x + 2 * r₀ * z := by
  dsimp
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm u ξ]
  ring

end Sec6RotatingFrameAndTides

end InfoGeometry.Projective.GrassmannMeanMotionAndTidalHarmonics
