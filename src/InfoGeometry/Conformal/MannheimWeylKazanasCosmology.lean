/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Meta.ArchetypePipeline
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Archetypes `MA₁` & `MA₂`: Conformal Weyl Scaling, Algebraic 4D Weyl Curvature, and Mannheim–Kazanas Fourth-Order Cosmology

Formalizes the constructive core of the first part of Philip Mannheim's lecture:

1. **Archetype `MA₁` — Weyl Scale–Gauge Unification, $d = 4$ Conformal Weights, & Algebraic Weyl Curvature**:
   - Local scale–gauge multiplier `scaleGaugeMultiplier β α = exp (β + i α)` separating the
     unitary phase (`α`, norm `1`) from the Weyl conformal dilation (`β`, norm `exp β`);
   - Light-cone and angle invariance of `conformalRescale β g = exp (2 * β) • g`;
   - Exact $d = 4$ Weyl invariance of massless Dirac kinetic (`-3/2 - 1 - 3/2 + 4 = 0`), Yukawa
     (`-1 - 3/2 - 3/2 + 4 = 0`), and quartic scalar (`-4 + 4 = 0`) terms vs. scale breaking of
     bare scalar mass, bare fermion mass, and bare cosmological constant;
   - Signature-general $4\mathrm{D}$ algebraic Weyl tensor `weylTensor4` via the Kulkarni–Nomizu
     product `kulkarniNomizu`, proving exact trace-freeness `∑ i, ε i * weylTensor4 ε Riem i j i l = 0`
     whenever `ε i ^ 2 = 1` and `Riem` satisfies pair-exchange symmetry `Riem k l i j = Riem i j k l`;
   - Uniqueness of Mannheim's $R_{\mu\nu} R^{\mu\nu} - \frac{1}{3} R^2$ conformal action ratio on
     linearized pure-conformal modes (`b = -(1 / 3) * a`).

2. **Archetype `MA₂` — Mannheim–Kazanas Fourth-Order Biharmonic Solution & Conformal Cosmology**:
   - Exact derivatives up to 4th order of `mannheimKazanasPotential α β γ κ r = α - 2 β / r + γ r - κ r²`,
     proving `radialBiharmonic = 0` identically for all `r ≠ 0` while `radialLaplacian = 2 γ / r - 6 κ`
     vanishes on `(0, ∞)` iff `γ = 0 ∧ κ = 0`;
   - Exact static spherical `C²` Weyl density `sphericalWeylSq` and fourth-order Bach tensor
     difference `sphericalBachW00 - sphericalBachWrr = (b / 3) * (b4 + (4 / r) * b3)`, plus exact
     vanishing of both `sphericalBachWrr` and `sphericalBachW00` on the Mannheim–Kazanas parameters
     `c₀ = -β (2 - 3 β γ)`, `c₁ = 1 - 3 β γ`, `c₂ = γ`, `c₃ = -κ`;
   - Negative effective cosmological Newton coupling `conformalGeff S₀ < 0`, open-hyperbolic
     deceleration bounds `-1 < q₀ < 0`, and sub-unit refractive index acceleration `c < c / n_ref`.
-/

noncomputable section

namespace InfoGeometry.Conformal.MannheimWeylKazanasCosmology

open Filter _root_.Topology
open Matrix BigOperators
open InfoGeometry.MetaCompiler

/-! ## Non-Commutativity Witness on `M₂(ℝ)` (OpenGauss T16 Guardrail) -/

/-- Explicit $2 \times 2$ real matrix non-commutativity witness. -/
theorem conformal_mat2_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-! ## Archetype `MA₁`: Weyl Scale–Gauge Unification, $d=4$ Conformal Weights & 4D Weyl Curvature -/

section ArchetypeMA1_WeylScaleCurvature

/-- Unified Weyl scale (`β`) and Yang–Mills phase (`α`) complex multiplier `exp (β + i α)`. -/
def scaleGaugeMultiplier (β α : ℝ) : ℂ :=
  Complex.exp ((β : ℂ) + (α : ℂ) * Complex.I)

theorem scaleGaugeMultiplier_add (β₁ α₁ β₂ α₂ : ℝ) :
    scaleGaugeMultiplier (β₁ + β₂) (α₁ + α₂) =
      scaleGaugeMultiplier β₁ α₁ * scaleGaugeMultiplier β₂ α₂ := by
  unfold scaleGaugeMultiplier
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem scaleGaugeMultiplier_zero :
    scaleGaugeMultiplier 0 0 = 1 := by
  unfold scaleGaugeMultiplier
  norm_num

theorem scaleGaugeMultiplier_neg_mul_cancel (β α : ℝ) :
    scaleGaugeMultiplier (-β) (-α) * scaleGaugeMultiplier β α = 1 := by
  rw [← scaleGaugeMultiplier_add, neg_add_cancel, neg_add_cancel, scaleGaugeMultiplier_zero]

/-- Gauging the imaginary part `α` preserves the norm, while gauging the real part `β`
rescales the norm by `Real.exp β`. -/
theorem norm_scaleGaugeMultiplier (β α : ℝ) :
    ‖scaleGaugeMultiplier β α‖ = Real.exp β := by
  unfold scaleGaugeMultiplier
  rw [Complex.norm_exp]
  have hre : ((β : ℂ) + (α : ℂ) * Complex.I).re = β := by simp
  rw [hre]

/-- Local conformal rescaling `g ↦ exp (2 β) • g` of a real bilinear metric form. -/
def conformalRescale {V : Type*} [AddCommGroup V] [Module ℝ V]
    (β : ℝ) (g : LinearMap.BilinForm ℝ V) : LinearMap.BilinForm ℝ V :=
  Real.exp (2 * β) • g

/-- Conformal rescaling preserves the light cone `g(v, v) = 0`. -/
theorem conformalRescale_null_cone_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    (β : ℝ) (g : LinearMap.BilinForm ℝ V) (v : V) :
    conformalRescale β g v v = 0 ↔ g v v = 0 := by
  unfold conformalRescale
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero]
  exact or_iff_right (Real.exp_pos (2 * β)).ne'

/-- Conformal rescaling preserves squared cosines of angles between non-null vectors. -/
theorem conformalRescale_cosAngle_invariant {V : Type*} [AddCommGroup V] [Module ℝ V]
    (β : ℝ) (g : LinearMap.BilinForm ℝ V) (u v : V)
    (hu : g u u ≠ 0) (hv : g v v ≠ 0) :
    (conformalRescale β g u v) ^ 2 / ((conformalRescale β g u u) * (conformalRescale β g v v)) =
      (g u v) ^ 2 / (g u u * g v v) := by
  have he : Real.exp (2 * β) ≠ 0 := (Real.exp_pos (2 * β)).ne'
  simp only [conformalRescale, LinearMap.smul_apply, smul_eq_mul]
  field_simp [he, hu, hv]

/-- 4D volume form scaling factor `det(e) ↦ exp (4 β) det(e)`. -/
def vol4Scale (β : ℝ) : ℝ := Real.exp (4 * β)

/-- Inverse vierbein / covariant spin-connection derivative weight `exp (-β)`. -/
def invTetradScale (β : ℝ) : ℝ := Real.exp (-β)

/-- 4D Dirac spinor conformal weight `-3/2`, i.e., `exp (-3/2 * β)`. -/
def spinorScale (β : ℝ) : ℝ := Real.exp (-(3 / 2 : ℝ) * β)

/-- 4D conformally coupled scalar field weight `-1`, i.e., `exp (-β)`. -/
def confScalarScale (β : ℝ) : ℝ := Real.exp (-β)

/-- Exact $d = 4$ conformal invariance of massless Dirac kinetic, Yukawa, and quartic scalar
couplings, contrasted with explicit scale breaking by bare mass and bare cosmological terms. -/
theorem dirac_yukawa_quartic_conformal_invariant_vs_mass_breaking (β : ℝ) :
    vol4Scale β * spinorScale β * invTetradScale β * spinorScale β = 1 ∧
    vol4Scale β * confScalarScale β * (spinorScale β) ^ 2 = 1 ∧
    vol4Scale β * (confScalarScale β) ^ 4 = 1 ∧
    (vol4Scale β * (confScalarScale β) ^ 2 = 1 ↔ β = 0) ∧
    (vol4Scale β * (spinorScale β) ^ 2 = 1 ↔ β = 0) ∧
    (vol4Scale β = 1 ↔ β = 0) := by
  unfold vol4Scale invTetradScale spinorScale confScalarScale
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    have harg : 4 * β + -(3 / 2 : ℝ) * β + -β + -(3 / 2 : ℝ) * β = 0 := by ring
    rw [harg, Real.exp_zero]
  · rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    have harg : 4 * β + -β + (-(3 / 2 : ℝ) * β + -(3 / 2 : ℝ) * β) = 0 := by ring
    rw [harg, Real.exp_zero]
  · rw [show (Real.exp (-β)) ^ 4 = Real.exp (-β) * Real.exp (-β) * Real.exp (-β) * Real.exp (-β) by ring]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    have harg : 4 * β + (-β + -β + -β + -β) = 0 := by ring
    rw [harg, Real.exp_zero]
  · rw [pow_two, ← Real.exp_add, ← Real.exp_add, Real.exp_eq_one_iff]
    constructor <;> intro h <;> linarith
  · rw [pow_two, ← Real.exp_add, ← Real.exp_add, Real.exp_eq_one_iff]
    constructor <;> intro h <;> linarith
  · rw [Real.exp_eq_one_iff]
    constructor <;> intro h <;> linarith

/-- Kulkarni–Nomizu algebraic curvature product `(A ⊙ B)_{ijkl}` of two matrices. -/
def kulkarniNomizu {n : ℕ} {R : Type*} [CommRing R]
    (A B : Matrix (Fin n) (Fin n) R) (i j k l : Fin n) : R :=
  A i k * B j l - A i l * B j k + B i k * A j l - B i l * A j k

/-- The Kulkarni–Nomizu product of two symmetric matrices satisfies all four algebraic Riemann
symmetries: pair antisymmetry in `(i, j)` and `(k, l)`, pair-exchange symmetry, and the first
Bianchi identity. -/
theorem kulkarniNomizu_curv_symmetries {n : ℕ} {R : Type*} [CommRing R]
    (A B : Matrix (Fin n) (Fin n) R) (hA : Aᵀ = A) (hB : Bᵀ = B) (i j k l : Fin n) :
    kulkarniNomizu A B j i k l = -kulkarniNomizu A B i j k l ∧
    kulkarniNomizu A B i j l k = -kulkarniNomizu A B i j k l ∧
    kulkarniNomizu A B k l i j = kulkarniNomizu A B i j k l ∧
    kulkarniNomizu A B i j k l + kulkarniNomizu A B i k l j + kulkarniNomizu A B i l j k = 0 := by
  have ha (p q : Fin n) : A p q = A q p := by
    rw [← Matrix.transpose_apply A q p, hA]
  have hb (p q : Fin n) : B p q = B q p := by
    rw [← Matrix.transpose_apply B q p, hB]
  unfold kulkarniNomizu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha j k, ha i l, ha j l, ha i k, hb j k, hb i l, hb j l, hb i k]; ring
  · ring
  · rw [ha k i, ha l j, ha l i, ha k j, hb k i, hb l j, hb l i, hb k j]; ring
  · rw [ha j l, ha k j, ha l k, hb j l, hb k j, hb l k]; ring

/-- Diagonal metric matrix `diag(ε₀, ε₁, ε₂, ε₃)` for any 4D signature `ε : Fin 4 → ℝ`. -/
def diagMetric4 (ε : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ε

lemma diagMetric4_transpose (ε : Fin 4 → ℝ) : (diagMetric4 ε)ᵀ = diagMetric4 ε := by
  ext i j
  by_cases h : i = j <;> simp [diagMetric4, h, eq_comm]

/-- Signature-general 4D Ricci tensor `R_{jl} = ∑_i ε_i R_{ijil}`. -/
def ricciContract4 (ε : Fin 4 → ℝ) (Riem : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (j l : Fin 4) : ℝ :=
  ∑ i : Fin 4, ε i * Riem i j i l

/-- Signature-general 4D Ricci scalar `R = ∑_j ε_j R_{jj}`. -/
def ricciScalar4 (ε : Fin 4 → ℝ) (Riem : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ j : Fin 4, ε j * ricciContract4 ε Riem j j

/-- Exact 4D algebraic Weyl tensor:
`C_{ijkl} = R_{ijkl} - (1/2) (g ⊙ Ric)_{ijkl} + (R/12) (g ⊙ g)_{ijkl}`. -/
def weylTensor4 (ε : Fin 4 → ℝ) (Riem : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  Riem i j k l -
    (1 / 2 : ℝ) * kulkarniNomizu (diagMetric4 ε) (Matrix.of (ricciContract4 ε Riem)) i j k l +
    (ricciScalar4 ε Riem / 12) * kulkarniNomizu (diagMetric4 ε) (diagMetric4 ε) i j k l

/-- **Exact 4D Weyl Trace-Freeness Across All Signatures (`ε_i² = 1`)**:
For any 4D signature `ε` with `ε i * ε i = 1` (covering Lorentzian `(-1,1,1,1)`, Euclidean
`(1,1,1,1)`, and Kleinian `(1,1,-1,-1)`) and any algebraic Riemann tensor satisfying
pair-exchange symmetry `Riem k l i j = Riem i j k l`, contracting the first and third slots
gives `∑ i, ε i * weylTensor4 ε Riem i j i l = 0`. -/
theorem weylTensor4_trace_zero
    (ε : Fin 4 → ℝ) (hε : ∀ i : Fin 4, ε i * ε i = 1)
    (Riem : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h_pair : ∀ i j k l, Riem k l i j = Riem i j k l)
    (j l : Fin 4) :
    ∑ i : Fin 4, ε i * weylTensor4 ε Riem i j i l = 0 := by
  have hRic_sym : ∀ a b : Fin 4, ricciContract4 ε Riem a b = ricciContract4 ε Riem b a := by
    intro a b
    unfold ricciContract4
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [h_pair i a i b]
  have h_diag_sum : ∀ i : Fin 4, ∑ k : Fin 4, ε k * diagMetric4 ε k i = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp [diagMetric4, hε i]
    · intro k _ hk
      simp [diagMetric4, Matrix.diagonal_apply_ne _ hk]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have h_trace_g : ∑ i : Fin 4, ε i * diagMetric4 ε i i = 4 := by
    calc
      ∑ i : Fin 4, ε i * diagMetric4 ε i i = ∑ _i : Fin 4, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [diagMetric4, hε i]
      _ = 4 := by norm_num
  have h_sum_kn_g_R :
      ∑ i : Fin 4, ε i * kulkarniNomizu (diagMetric4 ε) (Matrix.of (ricciContract4 ε Riem)) i j i l =
        2 * ricciContract4 ε Riem j l + diagMetric4 ε j l * ricciScalar4 ε Riem := by
    unfold kulkarniNomizu
    have hsplit :
        ∀ i : Fin 4,
          ε i * (diagMetric4 ε i i * ricciContract4 ε Riem j l -
            diagMetric4 ε i l * ricciContract4 ε Riem j i +
            ricciContract4 ε Riem i i * diagMetric4 ε j l -
            ricciContract4 ε Riem i l * diagMetric4 ε j i) =
          (ε i * diagMetric4 ε i i) * ricciContract4 ε Riem j l -
          (ε i * diagMetric4 ε i l) * ricciContract4 ε Riem j i +
          (ε i * ricciContract4 ε Riem i i) * diagMetric4 ε j l -
          (ε i * diagMetric4 ε j i) * ricciContract4 ε Riem i l := by
      intro i; ring
    simp only [Matrix.of_apply, hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : ∑ i : Fin 4, (ε i * diagMetric4 ε i i) * ricciContract4 ε Riem j l =
        4 * ricciContract4 ε Riem j l := by
      rw [← Finset.sum_mul, h_trace_g]
    have h2 : ∑ i : Fin 4, (ε i * diagMetric4 ε i l) * ricciContract4 ε Riem j i =
        ricciContract4 ε Riem j l := by
      rw [Finset.sum_eq_single l]
      · simp [diagMetric4, hε l]
      · intro i _ hi
        simp [diagMetric4, Matrix.diagonal_apply_ne _ hi]
      · intro hl
        exact (hl (Finset.mem_univ l)).elim
    have h3 : ∑ i : Fin 4, (ε i * ricciContract4 ε Riem i i) * diagMetric4 ε j l =
        ricciScalar4 ε Riem * diagMetric4 ε j l := by
      rw [← Finset.sum_mul]
      rfl
    have h4 : ∑ i : Fin 4, (ε i * diagMetric4 ε j i) * ricciContract4 ε Riem i l =
        ricciContract4 ε Riem j l := by
      rw [Finset.sum_eq_single j]
      · simp [diagMetric4, hε j]
      · intro i _ hi
        simp [diagMetric4, Matrix.diagonal_apply_ne _ hi.symm]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    rw [h1, h2, h3, h4, hRic_sym]
    ring
  have h_sum_kn_g_g :
      ∑ i : Fin 4, ε i * kulkarniNomizu (diagMetric4 ε) (diagMetric4 ε) i j i l =
        6 * diagMetric4 ε j l := by
    unfold kulkarniNomizu
    have hsplit :
        ∀ i : Fin 4,
          ε i * (diagMetric4 ε i i * diagMetric4 ε j l -
            diagMetric4 ε i l * diagMetric4 ε j i +
            diagMetric4 ε i i * diagMetric4 ε j l -
            diagMetric4 ε i l * diagMetric4 ε j i) =
          2 * (ε i * diagMetric4 ε i i) * diagMetric4 ε j l -
          2 * (ε i * diagMetric4 ε i l) * diagMetric4 ε j i := by
      intro i; ring
    simp only [hsplit, Finset.sum_sub_distrib]
    have h1 : ∑ i : Fin 4, 2 * (ε i * diagMetric4 ε i i) * diagMetric4 ε j l =
        8 * diagMetric4 ε j l := by
      have : ∑ i : Fin 4, 2 * (ε i * diagMetric4 ε i i) * diagMetric4 ε j l =
          (2 * ∑ i : Fin 4, ε i * diagMetric4 ε i i) * diagMetric4 ε j l := by
        calc
          ∑ i : Fin 4, 2 * (ε i * diagMetric4 ε i i) * diagMetric4 ε j l
              = (∑ i : Fin 4, 2 * (ε i * diagMetric4 ε i i)) * diagMetric4 ε j l := by
                rw [← Finset.sum_mul]
          _ = (2 * ∑ i : Fin 4, ε i * diagMetric4 ε i i) * diagMetric4 ε j l := by
                rw [← Finset.mul_sum]
      rw [this, h_trace_g]
      ring
    have h2 : ∑ i : Fin 4, 2 * (ε i * diagMetric4 ε i l) * diagMetric4 ε j i =
        2 * diagMetric4 ε j l := by
      rw [Finset.sum_eq_single l]
      · simp [diagMetric4, hε l]
      · intro i _ hi
        simp [diagMetric4, Matrix.diagonal_apply_ne _ hi]
      · intro hl
        exact (hl (Finset.mem_univ l)).elim
    rw [h1, h2]
    ring
  have h_weyl_expand :
      ∑ i : Fin 4, ε i * weylTensor4 ε Riem i j i l =
        (∑ i : Fin 4, ε i * Riem i j i l) -
        (1 / 2 : ℝ) * (∑ i : Fin 4, ε i * kulkarniNomizu (diagMetric4 ε) (Matrix.of (ricciContract4 ε Riem)) i j i l) +
        (ricciScalar4 ε Riem / 12) * (∑ i : Fin 4, ε i * kulkarniNomizu (diagMetric4 ε) (diagMetric4 ε) i j i l) := by
    unfold weylTensor4
    have hterm :
        ∀ i : Fin 4,
          ε i * (Riem i j i l -
            (1 / 2 : ℝ) * kulkarniNomizu (diagMetric4 ε) (Matrix.of (ricciContract4 ε Riem)) i j i l +
            (ricciScalar4 ε Riem / 12) * kulkarniNomizu (diagMetric4 ε) (diagMetric4 ε) i j i l) =
          ε i * Riem i j i l -
            (1 / 2 : ℝ) * (ε i * kulkarniNomizu (diagMetric4 ε) (Matrix.of (ricciContract4 ε Riem)) i j i l) +
            (ricciScalar4 ε Riem / 12) * (ε i * kulkarniNomizu (diagMetric4 ε) (diagMetric4 ε) i j i l) := by
      intro i; ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h_riem_eq : ∑ i : Fin 4, ε i * Riem i j i l = ricciContract4 ε Riem j l := rfl
  rw [h_weyl_expand, h_riem_eq, h_sum_kn_g_R, h_sum_kn_g_g]
  ring

/-- Scalar diagonal 4D metric entry `g_{μν} = ε_μ δ_{μν}` (component form). -/
def diagEntry4 (ε : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  if μ = ν then ε μ else 0

/-- Signature-general 4D squared norm `∑ μ, ε μ * (k μ)²`. -/
def lorentzNormSq4 (ε k : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, ε μ * (k μ) ^ 2

/-- Linearized pure-conformal 4D Ricci tensor `2 k_μ k_ν + g_{μν} k²`. -/
def pureConformalRicci4 (ε k : Fin 4 → ℝ) (μ ν : Fin 4) : ℝ :=
  2 * k μ * k ν + diagEntry4 ε μ ν * lorentzNormSq4 ε k

/-- Linearized pure-conformal 4D Ricci scalar `6 k²`. -/
def pureConformalScalar4 (ε k : Fin 4 → ℝ) : ℝ :=
  6 * lorentzNormSq4 ε k

/-- **Mannheim's Unique `-1/3` Action Ratio Theorem (`MA₁`)**:
On linearized pure-conformal fluctuations `R_{μν} = 2 k_μ k_ν + g_{μν} k²`,
`R_{μν} R^{μν} = 12 (k²)²` and `R² = 36 (k²)²`. Thus a quadratic curvature combination
`a R_{μν} R^{μν} + b R²` vanishes on all pure-conformal modes **if and only if** `b = -(1 / 3) * a`
(separating local conformal invariance `a = 1, b = -1/3` from generic quadratic gravity). -/
theorem mannheim_conformal_ricci_sq_minus_third_scalar_sq_iff
    (ε : Fin 4 → ℝ) (hε : ∀ i : Fin 4, ε i * ε i = 1) (a b : ℝ) :
    (∀ k : Fin 4 → ℝ,
      ∑ μ : Fin 4, ε μ * pureConformalRicci4 ε k μ μ = pureConformalScalar4 ε k) ∧
    (∀ k : Fin 4 → ℝ,
      ∑ μ : Fin 4, ∑ ν : Fin 4, ε μ * ε ν * (pureConformalRicci4 ε k μ ν) ^ 2 =
        12 * (lorentzNormSq4 ε k) ^ 2) ∧
    ((∀ k : Fin 4 → ℝ,
      a * (∑ μ : Fin 4, ∑ ν : Fin 4, ε μ * ε ν * (pureConformalRicci4 ε k μ ν) ^ 2) +
      b * (pureConformalScalar4 ε k) ^ 2 = 0) ↔ b = -(1 / 3 : ℝ) * a) := by
  have h_tr_g : ∑ μ : Fin 4, ε μ * diagEntry4 ε μ μ = 4 := by
    calc
      ∑ μ : Fin 4, ε μ * diagEntry4 ε μ μ = ∑ _μ : Fin 4, (1 : ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro μ _; simp [diagEntry4, hε μ]
      _ = 4 := by norm_num
  have h1 : ∀ k : Fin 4 → ℝ,
      ∑ μ : Fin 4, ε μ * pureConformalRicci4 ε k μ μ = pureConformalScalar4 ε k := by
    intro k
    unfold pureConformalRicci4 pureConformalScalar4
    have hsplit : ∀ μ : Fin 4,
        ε μ * (2 * k μ * k μ + diagEntry4 ε μ μ * lorentzNormSq4 ε k) =
        2 * (ε μ * (k μ) ^ 2) + (ε μ * diagEntry4 ε μ μ) * lorentzNormSq4 ε k := by
      intro μ; ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [h_tr_g]
    change 2 * lorentzNormSq4 ε k + 4 * lorentzNormSq4 ε k = 6 * lorentzNormSq4 ε k
    ring
  have h2 : ∀ k : Fin 4 → ℝ,
      ∑ μ : Fin 4, ∑ ν : Fin 4, ε μ * ε ν * (pureConformalRicci4 ε k μ ν) ^ 2 =
        12 * (lorentzNormSq4 ε k) ^ 2 := by
    intro k
    have hsq_exp : ∀ μ ν : Fin 4,
        ε μ * ε ν * (pureConformalRicci4 ε k μ ν) ^ 2 =
          4 * (ε μ * (k μ) ^ 2) * (ε ν * (k ν) ^ 2) +
          4 * lorentzNormSq4 ε k * (ε μ * k μ * k ν * (ε ν * diagEntry4 ε μ ν)) +
          (lorentzNormSq4 ε k) ^ 2 * (ε μ * diagEntry4 ε μ ν) * (ε ν * diagEntry4 ε μ ν) := by
      intro μ ν
      unfold pureConformalRicci4
      ring
    simp only [hsq_exp, Finset.sum_add_distrib]
    have sA :
        ∑ μ : Fin 4, ∑ ν : Fin 4, 4 * (ε μ * (k μ) ^ 2) * (ε ν * (k ν) ^ 2) =
          4 * (lorentzNormSq4 ε k) ^ 2 := by
      calc
        ∑ μ : Fin 4, ∑ ν : Fin 4, 4 * (ε μ * (k μ) ^ 2) * (ε ν * (k ν) ^ 2)
            = ∑ μ : Fin 4, 4 * (ε μ * (k μ) ^ 2) * (∑ ν : Fin 4, ε ν * (k ν) ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro μ _
              rw [Finset.mul_sum]
        _ = 4 * (∑ μ : Fin 4, (ε μ * (k μ) ^ 2) * (∑ ν : Fin 4, ε ν * (k ν) ^ 2)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro μ _; ring
        _ = 4 * (lorentzNormSq4 ε k) ^ 2 := by
              rw [← Finset.sum_mul]
              change 4 * (lorentzNormSq4 ε k * lorentzNormSq4 ε k) = _
              ring
    have sB :
        ∑ μ : Fin 4, ∑ ν : Fin 4,
            4 * lorentzNormSq4 ε k * (ε μ * k μ * k ν * (ε ν * diagEntry4 ε μ ν)) =
          4 * (lorentzNormSq4 ε k) ^ 2 := by
      have h_in : ∀ μ : Fin 4,
          ∑ ν : Fin 4,
            4 * lorentzNormSq4 ε k * (ε μ * k μ * k ν * (ε ν * diagEntry4 ε μ ν)) =
            4 * lorentzNormSq4 ε k * (ε μ * (k μ) ^ 2) := by
        intro μ
        rw [Finset.sum_eq_single μ]
        · have h1 : diagEntry4 ε μ μ = ε μ := by simp [diagEntry4]
          rw [h1]
          calc
            4 * lorentzNormSq4 ε k * (ε μ * k μ * k μ * (ε μ * ε μ))
                = 4 * lorentzNormSq4 ε k * (ε μ * k μ ^ 2 * (ε μ * ε μ)) := by ring
            _ = 4 * lorentzNormSq4 ε k * (ε μ * (k μ) ^ 2) := by rw [hε μ, mul_one]
        · intro ν _ hν
          simp [diagEntry4, hν.symm]
        · intro hμ
          exact (hμ (Finset.mem_univ μ)).elim
      simp only [h_in, ← Finset.mul_sum]
      change 4 * lorentzNormSq4 ε k * lorentzNormSq4 ε k = 4 * (lorentzNormSq4 ε k) ^ 2
      ring
    have sC :
        ∑ μ : Fin 4, ∑ ν : Fin 4,
            (lorentzNormSq4 ε k) ^ 2 * (ε μ * diagEntry4 ε μ ν) * (ε ν * diagEntry4 ε μ ν) =
          4 * (lorentzNormSq4 ε k) ^ 2 := by
      have h_in : ∀ μ : Fin 4,
          ∑ ν : Fin 4,
            (lorentzNormSq4 ε k) ^ 2 * (ε μ * diagEntry4 ε μ ν) * (ε ν * diagEntry4 ε μ ν) =
            (lorentzNormSq4 ε k) ^ 2 := by
        intro μ
        rw [Finset.sum_eq_single μ]
        · simp only [diagEntry4, ↓reduceIte]
          calc
            (lorentzNormSq4 ε k) ^ 2 * (ε μ * ε μ) * (ε μ * ε μ)
                = (lorentzNormSq4 ε k) ^ 2 * 1 * 1 := by rw [hε μ]
            _ = (lorentzNormSq4 ε k) ^ 2 := by ring
        · intro ν _ hν
          simp [diagEntry4, hν.symm]
        · intro hμ
          exact (hμ (Finset.mem_univ μ)).elim
      simp only [h_in, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [sA, sB, sC]
    ring
  refine ⟨h1, h2, ?_⟩
  constructor
  · intro h_all
    let k₀ : Fin 4 → ℝ := ![1, 0, 0, 0]
    have hk₀_sq : lorentzNormSq4 ε k₀ = ε 0 := by
      simp [lorentzNormSq4, Fin.sum_univ_four, k₀]
    have hk₀_fourth : (lorentzNormSq4 ε k₀) ^ 2 = 1 := by
      rw [hk₀_sq, pow_two, hε 0]
    have heval := h_all k₀
    rw [h2 k₀] at heval
    unfold pureConformalScalar4 at heval
    rw [show (6 * lorentzNormSq4 ε k₀) ^ 2 = 36 * (lorentzNormSq4 ε k₀) ^ 2 by ring] at heval
    rw [hk₀_fourth] at heval
    linarith
  · intro hb k
    rw [hb, h2 k]
    unfold pureConformalScalar4
    ring

end ArchetypeMA1_WeylScaleCurvature

/-! ## Archetype `MA₂`: Mannheim–Kazanas Fourth-Order Solution, Static Spherical Bach Tensor & Conformal Cosmology -/

section ArchetypeMA2_MannheimKazanasCosmology

/-- Radial Laplacian `(d²/dr² + 2/r d/dr) B(r)` for static spherically symmetric potentials. -/
def radialLaplacian (B : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv B) r + (2 / r) * deriv B r

/-- Radial biharmonic `(d⁴/dr⁴ + 4/r d³/dr³) B(r)` (= `(1/r) d⁴/dr⁴(r B(r))`). -/
def radialBiharmonic (B : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv (deriv (deriv B))) r + (4 / r) * deriv (deriv (deriv B)) r

/-- Exact Mannheim–Kazanas metric potential `B(r) = α - 2 β / r + γ r - κ r²`. -/
def mannheimKazanasPotential (α β γ κ r : ℝ) : ℝ :=
  α - 2 * β / r + γ * r - κ * r ^ 2

def mannheimKazanasDeriv1 (β γ κ r : ℝ) : ℝ :=
  2 * β / r ^ 2 + γ - 2 * κ * r

def mannheimKazanasDeriv2 (β κ r : ℝ) : ℝ :=
  -(4 * β) / r ^ 3 - 2 * κ

def mannheimKazanasDeriv3 (β r : ℝ) : ℝ :=
  12 * β / r ^ 4

def mannheimKazanasDeriv4 (β r : ℝ) : ℝ :=
  -(48 * β) / r ^ 5

lemma hasDerivAt_inv_pow (k : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => 1 / x ^ k) (-(k : ℝ) / r ^ (k + 1)) r := by
  have hrk : r ^ k ≠ 0 := pow_ne_zero k hr
  have hpow : HasDerivAt (fun x : ℝ => x ^ k) ((k : ℝ) * r ^ (k - 1)) r := hasDerivAt_pow k r
  have hinv := (hasDerivAt_inv hrk).comp r hpow
  have heq_fun : (fun x : ℝ => 1 / x ^ k) = (fun x : ℝ => (x ^ k)⁻¹) := by
    ext x; simp [one_div]
  rw [heq_fun]
  refine hinv.congr_deriv ?_
  cases k with
  | zero => simp
  | succ m =>
    have hpow_ne : r ^ (m + 1) ≠ 0 := pow_ne_zero (m + 1) hr
    have h2 : r ^ (2 * (m + 1)) = r ^ (m + 2) * r ^ m := by
      rw [← pow_add]; ring_nf
    simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
    field_simp [hr, hpow_ne]
    ring

lemma mannheimKazanas_deriv1_eq (α β γ κ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (mannheimKazanasPotential α β γ κ) r = mannheimKazanasDeriv1 β γ κ r := by
  have h1 := (hasDerivAt_const r α).sub ((hasDerivAt_inv_pow 1 hr).const_mul (2 * β))
  have h2 : HasDerivAt (fun x : ℝ => γ * x) γ r := by
    simpa using (hasDerivAt_id r).const_mul γ
  have h3 := (hasDerivAt_pow 2 r).const_mul κ
  have htot : HasDerivAt (mannheimKazanasPotential α β γ κ) _ r :=
    ((h1.add h2).sub h3).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
      simp only [mannheimKazanasPotential, Pi.sub_apply, Pi.add_apply, pow_one,
        div_eq_mul_inv, one_mul])
  rw [htot.deriv, mannheimKazanasDeriv1]
  simp only [Nat.cast_one, Nat.cast_ofNat]
  ring

lemma mannheimKazanas_deriv2_eq (α β γ κ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv (mannheimKazanasPotential α β γ κ)) r = mannheimKazanasDeriv2 β κ r := by
  have hev : deriv (mannheimKazanasPotential α β γ κ) =ᶠ[𝓝 r] mannheimKazanasDeriv1 β γ κ := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx
    exact mannheimKazanas_deriv1_eq α β γ κ hx
  rw [hev.deriv_eq]
  have h1 := ((hasDerivAt_inv_pow 2 hr).const_mul (2 * β)).add (hasDerivAt_const r γ)
  have h2 : HasDerivAt (fun x : ℝ => 2 * κ * x) (2 * κ) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * κ)
  have htot : HasDerivAt (mannheimKazanasDeriv1 β γ κ) _ r :=
    (h1.sub h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
      simp only [mannheimKazanasDeriv1, Pi.sub_apply, Pi.add_apply, div_eq_mul_inv, one_mul])
  rw [htot.deriv, mannheimKazanasDeriv2]
  norm_num
  ring

lemma mannheimKazanas_deriv3_eq (α β γ κ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv (deriv (mannheimKazanasPotential α β γ κ))) r = mannheimKazanasDeriv3 β r := by
  have hev : deriv (deriv (mannheimKazanasPotential α β γ κ)) =ᶠ[𝓝 r] mannheimKazanasDeriv2 β κ := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx
    exact mannheimKazanas_deriv2_eq α β γ κ hx
  rw [hev.deriv_eq]
  have h1 := ((hasDerivAt_inv_pow 3 hr).const_mul (-(4 * β))).sub (hasDerivAt_const r (2 * κ))
  have htot : HasDerivAt (mannheimKazanasDeriv2 β κ) _ r :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
      simp only [mannheimKazanasDeriv2, Pi.sub_apply, div_eq_mul_inv, one_mul])
  rw [htot.deriv, mannheimKazanasDeriv3]
  norm_num
  ring

lemma mannheimKazanas_deriv4_eq (α β γ κ : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv (deriv (deriv (mannheimKazanasPotential α β γ κ)))) r =
      mannheimKazanasDeriv4 β r := by
  have hev : deriv (deriv (deriv (mannheimKazanasPotential α β γ κ))) =ᶠ[𝓝 r]
      mannheimKazanasDeriv3 β := by
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx
    exact mannheimKazanas_deriv3_eq α β γ κ hx
  rw [hev.deriv_eq]
  have h1 := (hasDerivAt_inv_pow 4 hr).const_mul (12 * β)
  have htot : HasDerivAt (mannheimKazanasDeriv3 β) _ r :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
      simp only [mannheimKazanasDeriv3, div_eq_mul_inv, one_mul])
  rw [htot.deriv, mannheimKazanasDeriv4]
  norm_num
  ring

/-- **Biharmonic vs. Harmonic Characterization of the Mannheim–Kazanas Metric Potential**:
For every `(α, β, γ, κ)` and every `r ≠ 0`:
1. `mannheimKazanasPotential α β γ κ` solves the exact 4th-order biharmonic equation
   `radialBiharmonic B r = 0`;
2. Its 2nd-order radial Laplacian equals `2 γ / r - 6 κ`, which vanishes on `(0, ∞)` **iff** both
   the linear dark-matter term `γ` and quadratic de Sitter term `κ` vanish (recovering Schwarzschild). -/
theorem mannheimKazanas_biharmonic_and_schwarzschild_reduction (α β γ κ : ℝ) :
    (∀ r : ℝ, r ≠ 0 → radialBiharmonic (mannheimKazanasPotential α β γ κ) r = 0) ∧
    (∀ r : ℝ, r ≠ 0 → radialLaplacian (mannheimKazanasPotential α β γ κ) r = 2 * γ / r - 6 * κ) ∧
    ((∀ r : ℝ, 0 < r → radialLaplacian (mannheimKazanasPotential α β γ κ) r = 0) ↔
      γ = 0 ∧ κ = 0) := by
  have hbih : ∀ r : ℝ, r ≠ 0 → radialBiharmonic (mannheimKazanasPotential α β γ κ) r = 0 := by
    intro r hr
    unfold radialBiharmonic
    rw [mannheimKazanas_deriv4_eq α β γ κ hr, mannheimKazanas_deriv3_eq α β γ κ hr]
    unfold mannheimKazanasDeriv4 mannheimKazanasDeriv3
    field_simp [hr]
    ring
  have hlap : ∀ r : ℝ, r ≠ 0 →
      radialLaplacian (mannheimKazanasPotential α β γ κ) r = 2 * γ / r - 6 * κ := by
    intro r hr
    unfold radialLaplacian
    rw [mannheimKazanas_deriv2_eq α β γ κ hr, mannheimKazanas_deriv1_eq α β γ κ hr]
    unfold mannheimKazanasDeriv2 mannheimKazanasDeriv1
    field_simp [hr]
    ring
  refine ⟨hbih, hlap, ?_⟩
  constructor
  · intro hzero
    have h1 := hzero 1 zero_lt_one
    have h2 := hzero 2 (by norm_num)
    rw [hlap 1 one_ne_zero] at h1
    rw [hlap 2 (by norm_num)] at h2
    have hγ : γ = 0 := by linarith
    have hκ : κ = 0 := by linarith
    exact ⟨hγ, hκ⟩
  · rintro ⟨rfl, rfl⟩ r hr
    rw [hlap r hr.ne']
    ring

/-- Static spherically symmetric 4D Weyl-squared scalar `C_{μνρσ} C^{μνρσ}` in jet coordinates
`(r, B, B', B'')` for `ds² = -B(r) dt² + dr² / B(r) + r² dΩ²`. -/
def sphericalWeylSq (r b b1 b2 : ℝ) : ℝ :=
  (r ^ 2 * b2 - 2 * r * b1 + 2 * b - 2) ^ 2 / (3 * r ^ 4)

/-- Static spherically symmetric radial Bach tensor component `W^r_r` in jet coordinates. -/
def sphericalBachWrr (r b b1 b2 b3 : ℝ) : ℝ :=
  b1 * b3 / 6 - b2 ^ 2 / 12 - b * b3 / (3 * r) + b1 * b2 / (3 * r) -
    b * b2 / (3 * r ^ 2) - b1 ^ 2 / (3 * r ^ 2) + 2 * b * b1 / (3 * r ^ 3) -
    b ^ 2 / (3 * r ^ 4) + 1 / (3 * r ^ 4)

/-- Static spherically symmetric temporal Bach tensor component `W^0_0` in jet coordinates. -/
def sphericalBachW00 (r b b1 b2 b3 b4 : ℝ) : ℝ :=
  b * b4 / 3 + b1 * b3 / 6 - b2 ^ 2 / 12 + b * b3 / r + b1 * b2 / (3 * r) -
    b * b2 / (3 * r ^ 2) - b1 ^ 2 / (3 * r ^ 2) + 2 * b * b1 / (3 * r ^ 3) -
    b ^ 2 / (3 * r ^ 4) + 1 / (3 * r ^ 4)

/-- **Exact Nonlinear Mannheim–Kazanas Bach Reduction & Vacuum Constraint**:
1. The nonlinear difference `W^0_0 - W^r_r` eliminates every quadratic and lower-order term,
   leaving exactly `(B / 3) * (B'''' + (4 / r) B''')`;
2. On the general Laurent ansatz `B(r) = c₀ / r + c₁ + c₂ r + c₃ r²`, both `W^r_r` and `W^0_0`
   reduce to `(3 c₀ c₂ - c₁² + 1) / (3 r⁴)` (independent of `c₃ = -κ`);
3. With Mannheim–Kazanas parameters `c₀ = -β (2 - 3 β γ)`, `c₁ = 1 - 3 β γ`, `c₂ = γ`,
   `3 c₀ c₂ - c₁² + 1 = 0`, so the full fourth-order vacuum Bach tensor vanishes identically. -/
theorem mannheim_kazanas_bach_difference_and_vacuum_constraint
    (r b b1 b2 b3 b4 c₀ c₁ c₂ c₃ β γ : ℝ) (hr : r ≠ 0) :
    (sphericalBachW00 r b b1 b2 b3 b4 - sphericalBachWrr r b b1 b2 b3 =
      (b / 3) * (b4 + (4 / r) * b3)) ∧
    (let Bval := c₀ / r + c₁ + c₂ * r + c₃ * r ^ 2
     let B1 := -c₀ / r ^ 2 + c₂ + 2 * c₃ * r
     let B2 := 2 * c₀ / r ^ 3 + 2 * c₃
     let B3 := -6 * c₀ / r ^ 4
     let B4 := 24 * c₀ / r ^ 5
     sphericalBachWrr r Bval B1 B2 B3 = (3 * c₀ * c₂ - c₁ ^ 2 + 1) / (3 * r ^ 4) ∧
     sphericalBachW00 r Bval B1 B2 B3 B4 = (3 * c₀ * c₂ - c₁ ^ 2 + 1) / (3 * r ^ 4)) ∧
    (let mc₀ := -β * (2 - 3 * β * γ)
     let mc₁ := 1 - 3 * β * γ
     let mc₂ := γ
     let Bval := mc₀ / r + mc₁ + mc₂ * r + c₃ * r ^ 2
     let B1 := -mc₀ / r ^ 2 + mc₂ + 2 * c₃ * r
     let B2 := 2 * mc₀ / r ^ 3 + 2 * c₃
     let B3 := -6 * mc₀ / r ^ 4
     let B4 := 24 * mc₀ / r ^ 5
     3 * mc₀ * mc₂ - mc₁ ^ 2 + 1 = 0 ∧
     sphericalBachWrr r Bval B1 B2 B3 = 0 ∧
     sphericalBachW00 r Bval B1 B2 B3 B4 = 0) := by
  have hdiff : sphericalBachW00 r b b1 b2 b3 b4 - sphericalBachWrr r b b1 b2 b3 =
      (b / 3) * (b4 + (4 / r) * b3) := by
    unfold sphericalBachW00 sphericalBachWrr
    field_simp [hr]
    ring
  have hpoly : ∀ p₀ p₁ p₂ p₃ : ℝ,
      let Bval := p₀ / r + p₁ + p₂ * r + p₃ * r ^ 2
      let B1 := -p₀ / r ^ 2 + p₂ + 2 * p₃ * r
      let B2 := 2 * p₀ / r ^ 3 + 2 * p₃
      let B3 := -6 * p₀ / r ^ 4
      let B4 := 24 * p₀ / r ^ 5
      sphericalBachWrr r Bval B1 B2 B3 = (3 * p₀ * p₂ - p₁ ^ 2 + 1) / (3 * r ^ 4) ∧
      sphericalBachW00 r Bval B1 B2 B3 B4 = (3 * p₀ * p₂ - p₁ ^ 2 + 1) / (3 * r ^ 4) := by
    intro p₀ p₁ p₂ p₃
    unfold sphericalBachWrr sphericalBachW00
    constructor <;> · field_simp [hr]; ring
  refine ⟨hdiff, hpoly c₀ c₁ c₂ c₃, ?_⟩
  have hmk_id : 3 * (-β * (2 - 3 * β * γ)) * γ - (1 - 3 * β * γ) ^ 2 + 1 = 0 := by ring
  obtain ⟨hwrr, hw00⟩ := hpoly (-β * (2 - 3 * β * γ)) (1 - 3 * β * γ) γ c₃
  rw [hmk_id, zero_div] at hwrr hw00
  exact ⟨hmk_id, hwrr, hw00⟩

/-- Conformal cosmological effective gravitational coupling `G_eff(S₀) = -3 / (4 π S₀²)`. -/
def conformalGeff (S₀ : ℝ) : ℝ :=
  -(3 : ℝ) / (4 * Real.pi * S₀ ^ 2)

/-- **Mannheim Conformal Cosmology & Negative-Curvature Acceleration Theorem**:
1. The conformally induced cosmological Newton constant `conformalGeff S₀` is strictly negative
   for `S₀ ≠ 0` (repulsive cosmological gravity decoupling `G_N` from `Λ`);
2. Whenever `0 < omegaLambdaBar` and `omegaLambdaBar + omegaKBar = 1` with negative-curvature
   contribution `0 < omegaKBar := -k / (a² H²)`, one automatically obtains `0 < omegaLambdaBar < 1`
   and cosmic deceleration parameter `q₀ = -omegaLambdaBar ∈ (-1, 0)`;
3. Any refractive medium with index `0 < n_ref < 1` gives superluminal phase velocity `c < c / n_ref`. -/
theorem mannheim_conformal_cosmology_deceleration_bounds
    (S₀ k a H omegaLambdaBar c n_ref : ℝ)
    (hS : S₀ ≠ 0) (hk : k < 0) (ha : 0 < a) (hH : H ≠ 0)
    (h_lam_pos : 0 < omegaLambdaBar)
    (h_friedmann : omegaLambdaBar + (-k / (a ^ 2 * H ^ 2)) = 1)
    (hc : 0 < c) (hn0 : 0 < n_ref) (hn1 : n_ref < 1) :
    conformalGeff S₀ < 0 ∧
    0 < (-k / (a ^ 2 * H ^ 2)) ∧
    omegaLambdaBar < 1 ∧
    (-1 < -omegaLambdaBar ∧ -omegaLambdaBar < 0) ∧
    c < c / n_ref := by
  have hGeff : conformalGeff S₀ < 0 := by
    unfold conformalGeff
    have hden : 0 < 4 * Real.pi * S₀ ^ 2 :=
      mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_ne_zero hS)
    exact div_neg_of_neg_of_pos (by norm_num) hden
  have hK : 0 < -k / (a ^ 2 * H ^ 2) := by
    have hnum : 0 < -k := neg_pos.mpr hk
    have hden : 0 < a ^ 2 * H ^ 2 := mul_pos (sq_pos_of_ne_zero ha.ne') (sq_pos_of_ne_zero hH)
    exact div_pos hnum hden
  have hlam_lt : omegaLambdaBar < 1 := by linarith [h_friedmann, hK]
  have hq : -1 < -omegaLambdaBar ∧ -omegaLambdaBar < 0 :=
    ⟨by linarith [hlam_lt], by linarith [h_lam_pos]⟩
  have hvel : c < c / n_ref := by
    rw [lt_div_iff₀ hn0]
    nlinarith [hc, hn1]
  exact ⟨hGeff, hK, hlam_lt, hq, hvel⟩

/-- Exact parameterized Mannheim–Kazanas metric function `B(r) = -β(2-3βγ)/r + (1-3βγ) + γ r - κ r²`
solving the fourth-order vacuum Bach equations via iterated `deriv`. -/
def mkExactMetricPotential (β γ κ r : ℝ) : ℝ :=
  mannheimKazanasPotential (1 - 3 * β * γ) (β * (1 - 3 * β * γ / 2)) γ κ r

/-- **True Iterated-`deriv` Vacuum Bach Theorem (`MA₂` Jet-Premise Closure)**:
Evaluating `sphericalBachWrr` and `sphericalBachW00` on `B := mkExactMetricPotential β γ κ` together with
its actual first four iterated `deriv` functions `deriv B`, `deriv (deriv B)`, `deriv (deriv (deriv B))`,
and `deriv (deriv (deriv (deriv B)))` vanishes identically for every `r ≠ 0` (discharging algebraic
jet-coordinate assumptions). -/
theorem mannheimKazanas_true_deriv_bach_vacuum (β γ κ r : ℝ) (hr : r ≠ 0) :
    let B := mkExactMetricPotential β γ κ
    sphericalBachWrr r (B r) (deriv B r) (deriv (deriv B) r) (deriv (deriv (deriv B)) r) = 0 ∧
    sphericalBachW00 r (B r) (deriv B r) (deriv (deriv B) r) (deriv (deriv (deriv B)) r)
      (deriv (deriv (deriv (deriv B))) r) = 0 := by
  intro B
  have hmk_fun : B = mannheimKazanasPotential (1 - 3 * β * γ) (β * (1 - 3 * β * γ / 2)) γ κ := rfl
  have hB : B r = -β * (2 - 3 * β * γ) / r + (1 - 3 * β * γ) + γ * r + (-κ) * r ^ 2 := by
    simp only [hmk_fun, mannheimKazanasPotential]
    ring
  have hd1 : deriv B r = -(-β * (2 - 3 * β * γ)) / r ^ 2 + γ + 2 * (-κ) * r := by
    rw [hmk_fun, mannheimKazanas_deriv1_eq (1 - 3 * β * γ) (β * (1 - 3 * β * γ / 2)) γ κ hr,
      mannheimKazanasDeriv1]
    ring
  have hd2 : deriv (deriv B) r = 2 * (-β * (2 - 3 * β * γ)) / r ^ 3 + 2 * (-κ) := by
    rw [hmk_fun, mannheimKazanas_deriv2_eq (1 - 3 * β * γ) (β * (1 - 3 * β * γ / 2)) γ κ hr,
      mannheimKazanasDeriv2]
    ring
  have hd3 : deriv (deriv (deriv B)) r = -6 * (-β * (2 - 3 * β * γ)) / r ^ 4 := by
    rw [hmk_fun, mannheimKazanas_deriv3_eq (1 - 3 * β * γ) (β * (1 - 3 * β * γ / 2)) γ κ hr,
      mannheimKazanasDeriv3]
    ring
  have hd4 : deriv (deriv (deriv (deriv B))) r = 24 * (-β * (2 - 3 * β * γ)) / r ^ 5 := by
    rw [hmk_fun, mannheimKazanas_deriv4_eq (1 - 3 * β * γ) (β * (1 - 3 * β * γ / 2)) γ κ hr,
      mannheimKazanasDeriv4]
    ring
  have hvac := (mannheim_kazanas_bach_difference_and_vacuum_constraint
    r 0 0 0 0 0 0 0 0 (-κ) β γ hr).2.2
  rw [hB, hd1, hd2, hd3, hd4]
  exact ⟨hvac.2.1, hvac.2.2⟩

/-- Characteristic de Sitter Hubble expansion rate `μ = √(2 λ S₀²)` of the conformal vacuum. -/
def mannheimCosmoRate (S₀ lam : ℝ) : ℝ :=
  Real.sqrt (2 * lam * S₀ ^ 2)

/-- Open (`k < 0`) conformal Robertson–Walker scale factor
`a(t) = (√(-k) / μ) * sinh (μ t)`. -/
def mannheimScaleFactor (S₀ lam k t : ℝ) : ℝ :=
  (Real.sqrt (-k) / mannheimCosmoRate S₀ lam) * Real.sinh (mannheimCosmoRate S₀ lam * t)

/-- Constructive Hubble parameter `H(t) = deriv a(t) / a(t)`. -/
def mannheimHubble (S₀ lam k t : ℝ) : ℝ :=
  deriv (mannheimScaleFactor S₀ lam k) t / mannheimScaleFactor S₀ lam k t

/-- Constructive cosmic deceleration parameter `q(t) = -(a(t) a''(t)) / (a'(t))²`. -/
def mannheimDeceleration (S₀ lam k t : ℝ) : ℝ :=
  -(mannheimScaleFactor S₀ lam k t * deriv (deriv (mannheimScaleFactor S₀ lam k)) t) /
    (deriv (mannheimScaleFactor S₀ lam k) t) ^ 2

/-- Constructive conformal vacuum density fraction `Ω_Λ(t) = 2 λ S₀² / H(t)²`. -/
def mannheimOmegaLambdaBar (S₀ lam k t : ℝ) : ℝ :=
  (2 * lam * S₀ ^ 2) / (mannheimHubble S₀ lam k t) ^ 2

/-- Constructive negative-curvature density fraction `Ω_k(t) = -k / (a(t)² H(t)²)`. -/
def mannheimOmegaKBar (S₀ lam k t : ℝ) : ℝ :=
  -k / ((mannheimScaleFactor S₀ lam k t) ^ 2 * (mannheimHubble S₀ lam k t) ^ 2)

/-- **Constructive Conformal Robertson–Walker ODE & Friedmann Closure (`C-COND` #1 Discharge)**:
For any constant conformal scalar VEV `S₀ ≠ 0`, quartic coupling `0 < lam`, open spatial curvature
`k < 0`, and cosmological time `0 < t`, `a := mannheimScaleFactor S₀ lam k` is proved via `HasDerivAt`
(with **zero** assumed Friedmann closure or `omegaLambdaBar < 1` hypothesis) to satisfy:
1. Exact first and second derivatives `deriv a t = √(-k) cosh(μ t)` and `deriv (deriv a) t = μ √(-k) sinh(μ t)`
   where `μ = √(2 lam S₀²)`, with `0 < a t`, `0 < deriv a t`, `0 < deriv (deriv a) t`, and `0 < H t`;
2. Both the `(0, 0)` and `(i, i)` conformal Einstein–scalar equations `-(1/6) S₀² G_{μν} - g_{μν} lam S₀⁴ = 0`
   hold identically (`-(1/6) S₀² (3 ((a')² + k)/a²) + lam S₀⁴ = 0` and
   `-(1/6) S₀² (-(2 a a'' + (a')² + k)/a²) - lam S₀⁴ = 0`);
3. Constructive Friedmann closure `Ω_Λ(t) + Ω_k(t) = 1` with `0 < Ω_Λ(t)` and `0 < Ω_k(t)`;
4. Deceleration bounds `q(t) = -Ω_Λ(t)`, `-1 < q(t)`, and `q(t) < 0` (eternal cosmic acceleration). -/
theorem mannheim_conformal_friedmann_ode_and_acceleration_constructive
    (S₀ lam k t : ℝ) (hS : S₀ ≠ 0) (hlam : 0 < lam) (hk : k < 0) (ht : 0 < t) :
    let μ := mannheimCosmoRate S₀ lam
    let a := mannheimScaleFactor S₀ lam k
    let H := mannheimHubble S₀ lam k t
    let q := mannheimDeceleration S₀ lam k t
    let oL := mannheimOmegaLambdaBar S₀ lam k t
    let oK := mannheimOmegaKBar S₀ lam k t
    deriv a t = Real.sqrt (-k) * Real.cosh (μ * t) ∧
    deriv (deriv a) t = μ * Real.sqrt (-k) * Real.sinh (μ * t) ∧
    0 < a t ∧ 0 < deriv a t ∧ 0 < deriv (deriv a) t ∧ 0 < H ∧
    -(1 / 6 : ℝ) * S₀ ^ 2 * (3 * ((deriv a t) ^ 2 + k) / (a t) ^ 2) + lam * S₀ ^ 4 = 0 ∧
    -(1 / 6 : ℝ) * S₀ ^ 2 * (-(2 * a t * deriv (deriv a) t + (deriv a t) ^ 2 + k) / (a t) ^ 2) -
      lam * S₀ ^ 4 = 0 ∧
    0 < oL ∧ 0 < oK ∧ oL + oK = 1 ∧
    q = -oL ∧ -1 < q ∧ q < 0 := by
  intro μ a H q oL oK
  have hμ2_pos : 0 < 2 * lam * S₀ ^ 2 :=
    mul_pos (mul_pos zero_lt_two hlam) (sq_pos_of_ne_zero hS)
  have hμ_pos : 0 < μ := Real.sqrt_pos.mpr hμ2_pos
  have hμ_sq : μ ^ 2 = 2 * lam * S₀ ^ 2 := Real.sq_sqrt hμ2_pos.le
  have hk_pos : 0 < -k := neg_pos.mpr hk
  have hrk_pos : 0 < Real.sqrt (-k) := Real.sqrt_pos.mpr hk_pos
  have hrk_sq : (Real.sqrt (-k)) ^ 2 = -k := Real.sq_sqrt hk_pos.le
  have hderiv1_all : ∀ s : ℝ, deriv a s = Real.sqrt (-k) * Real.cosh (μ * s) := by
    intro s
    have hlin : HasDerivAt (fun x : ℝ => μ * x) μ s := by
      simpa using (hasDerivAt_id s).const_mul μ
    have hsinh : HasDerivAt (fun x : ℝ => Real.sinh (μ * x)) (Real.cosh (μ * s) * μ) s :=
      (Real.hasDerivAt_sinh (μ * s)).comp s hlin
    have ha : HasDerivAt a ((Real.sqrt (-k) / μ) * (Real.cosh (μ * s) * μ)) s :=
      (hsinh.const_mul (Real.sqrt (-k) / μ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
    rw [ha.deriv]
    field_simp [hμ_pos.ne']
  have hd1 : deriv a t = Real.sqrt (-k) * Real.cosh (μ * t) := hderiv1_all t
  have hd2 : deriv (deriv a) t = μ * Real.sqrt (-k) * Real.sinh (μ * t) := by
    have hfun : deriv a = fun s : ℝ => Real.sqrt (-k) * Real.cosh (μ * s) := funext hderiv1_all
    have hlin : HasDerivAt (fun x : ℝ => μ * x) μ t := by
      simpa using (hasDerivAt_id t).const_mul μ
    have hcosh : HasDerivAt (fun x : ℝ => Real.cosh (μ * x)) (Real.sinh (μ * t) * μ) t :=
      (Real.hasDerivAt_cosh (μ * t)).comp t hlin
    have hder := hcosh.const_mul (Real.sqrt (-k))
    rw [hfun, hder.deriv]
    ring
  have hsinh_pos : 0 < Real.sinh (μ * t) := Real.sinh_pos_iff.mpr (mul_pos hμ_pos ht)
  have hcosh_pos : 0 < Real.cosh (μ * t) := Real.cosh_pos (μ * t)
  have ha_pos : 0 < a t := by
    dsimp only [a, mannheimScaleFactor]
    exact mul_pos (div_pos hrk_pos hμ_pos) hsinh_pos
  have hd1_pos : 0 < deriv a t := by
    rw [hd1]
    exact mul_pos hrk_pos hcosh_pos
  have hd2_pos : 0 < deriv (deriv a) t := by
    rw [hd2]
    exact mul_pos (mul_pos hμ_pos hrk_pos) hsinh_pos
  have hH_pos : 0 < H := div_pos hd1_pos ha_pos
  have hcosh_sinh : Real.cosh (μ * t) ^ 2 - 1 = Real.sinh (μ * t) ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq (μ * t)]
  have hcomb : ((deriv a t) ^ 2 + k) / (a t) ^ 2 = 2 * lam * S₀ ^ 2 := by
    have ha_sq : (a t) ^ 2 = ((-k) / μ ^ 2) * Real.sinh (μ * t) ^ 2 := by
      dsimp only [a, mannheimScaleFactor]
      rw [mul_pow, div_pow, hrk_sq]
    have hd1_sq : (deriv a t) ^ 2 + k = (-k) * Real.sinh (μ * t) ^ 2 := by
      rw [hd1, mul_pow, hrk_sq]
      calc
        (-k) * Real.cosh (μ * t) ^ 2 + k = (-k) * (Real.cosh (μ * t) ^ 2 - 1) := by ring
        _ = (-k) * Real.sinh (μ * t) ^ 2 := by rw [hcosh_sinh]
    rw [hd1_sq, ha_sq]
    have hs_ne : Real.sinh (μ * t) ^ 2 ≠ 0 := pow_ne_zero 2 hsinh_pos.ne'
    have hden_ne : (-k) / μ ^ 2 * Real.sinh (μ * t) ^ 2 ≠ 0 :=
      mul_ne_zero (div_ne_zero hk_pos.ne' (pow_ne_zero 2 hμ_pos.ne')) hs_ne
    calc
      (-k) * Real.sinh (μ * t) ^ 2 / ((-k) / μ ^ 2 * Real.sinh (μ * t) ^ 2) = μ ^ 2 := by
        rw [div_eq_iff hden_ne]
        field_simp [hμ_pos.ne']
      _ = 2 * lam * S₀ ^ 2 := hμ_sq
  have hdd_ratio : deriv (deriv a) t / a t = 2 * lam * S₀ ^ 2 := by
    rw [hd2]
    have ha_expr : a t = (Real.sqrt (-k) / μ) * Real.sinh (μ * t) := rfl
    rw [ha_expr]
    field_simp [hμ_pos.ne', hrk_pos.ne', hsinh_pos.ne']
    exact hμ_sq
  have h00 : -(1 / 6 : ℝ) * S₀ ^ 2 * (3 * ((deriv a t) ^ 2 + k) / (a t) ^ 2) + lam * S₀ ^ 4 = 0 := by
    rw [show 3 * ((deriv a t) ^ 2 + k) / (a t) ^ 2 = 3 * (((deriv a t) ^ 2 + k) / (a t) ^ 2) by ring,
      hcomb]
    ring
  have hii : -(1 / 6 : ℝ) * S₀ ^ 2 *
      (-(2 * a t * deriv (deriv a) t + (deriv a t) ^ 2 + k) / (a t) ^ 2) - lam * S₀ ^ 4 = 0 := by
    have hsplit : (2 * a t * deriv (deriv a) t + (deriv a t) ^ 2 + k) / (a t) ^ 2 =
        2 * (deriv (deriv a) t / a t) + ((deriv a t) ^ 2 + k) / (a t) ^ 2 := by
      field_simp [ha_pos.ne']
      ring
    rw [neg_div, hsplit, hdd_ratio, hcomb]
    ring
  have hoL_pos : 0 < oL := div_pos hμ2_pos (sq_pos_of_pos hH_pos)
  have hoK_pos : 0 < oK := div_pos hk_pos (mul_pos (sq_pos_of_pos ha_pos) (sq_pos_of_pos hH_pos))
  have hclosure : oL + oK = 1 := by
    dsimp only [oL, oK, mannheimOmegaLambdaBar, mannheimOmegaKBar, mannheimHubble]
    change (2 * lam * S₀ ^ 2) / (deriv a t / a t) ^ 2 +
        (-k) / ((a t) ^ 2 * (deriv a t / a t) ^ 2) = 1
    rw [← hcomb]
    field_simp [ha_pos.ne', hd1_pos.ne']
    ring
  have hq_eq : q = -oL := by
    dsimp only [q, oL, mannheimDeceleration, mannheimOmegaLambdaBar, mannheimHubble]
    change -(a t * deriv (deriv a) t) / (deriv a t) ^ 2 =
        -((2 * lam * S₀ ^ 2) / (deriv a t / a t) ^ 2)
    have h1 : deriv (deriv a) t = (2 * lam * S₀ ^ 2) * a t := by
      rw [← hdd_ratio]
      field_simp [ha_pos.ne']
    rw [h1]
    field_simp [ha_pos.ne', hd1_pos.ne']
  have hq_gt : -1 < q := by linarith [hq_eq, hclosure, hoK_pos]
  have hq_lt : q < 0 := by linarith [hq_eq, hoL_pos]
  exact ⟨hd1, hd2, ha_pos, hd1_pos, hd2_pos, hH_pos, h00, hii, hoL_pos, hoK_pos, hclosure,
    hq_eq, hq_gt, hq_lt⟩

end ArchetypeMA2_MannheimKazanasCosmology

/-! ## Certified `TypedArchetype` Registrations for `MA₁` & `MA₂` -/

section ArchetypeRegistrations

/-- Proved `TypedArchetype` for `MA₁`: Weyl scale–gauge multiplier, $d=4$ conformal invariance,
4D signature-general Weyl trace-freeness, and uniqueness of `R_{μν} R^{μν} - 1/3 R²`. -/
def archMA1WeylScaleCurvature : TypedArchetype Unit .proved where
  name := `archMA1WeylScaleCurvature
  phase := 1
  claim := fun _ =>
    (∀ (β α : ℝ), ‖scaleGaugeMultiplier β α‖ = Real.exp β) ∧
    (∀ (β : ℝ),
      vol4Scale β * spinorScale β * invTetradScale β * spinorScale β = 1 ∧
      vol4Scale β * confScalarScale β * (spinorScale β) ^ 2 = 1 ∧
      vol4Scale β * (confScalarScale β) ^ 4 = 1) ∧
    (∀ (ε : Fin 4 → ℝ), (∀ i, ε i * ε i = 1) →
      ∀ (Riem : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ),
        (∀ i j k l, Riem k l i j = Riem i j k l) →
        ∀ j l, ∑ i : Fin 4, ε i * weylTensor4 ε Riem i j i l = 0) ∧
    (∀ (ε : Fin 4 → ℝ), (∀ i, ε i * ε i = 1) → ∀ a b : ℝ,
      ((∀ k : Fin 4 → ℝ,
        a * (∑ μ : Fin 4, ∑ ν : Fin 4, ε μ * ε ν * (pureConformalRicci4 ε k μ ν) ^ 2) +
        b * (pureConformalScalar4 ε k) ^ 2 = 0) ↔ b = -(1 / 3 : ℝ) * a))
  evidence := fun _ =>
    ⟨norm_scaleGaugeMultiplier,
     fun β => let h := dirac_yukawa_quartic_conformal_invariant_vs_mass_breaking β
              ⟨h.1, h.2.1, h.2.2.1⟩,
     fun ε hε Riem hp j l => weylTensor4_trace_zero ε hε Riem hp j l,
     fun ε hε a b => (mannheim_conformal_ricci_sq_minus_third_scalar_sq_iff ε hε a b).2.2⟩

/-- Proved `TypedArchetype` for `MA₂`: Mannheim–Kazanas biharmonic potential, true-derivative
vacuum Bach vanishing (`mkExactMetricPotential`), and constructive Robertson–Walker Friedmann
closure (`mannheimScaleFactor`) with `q(t) ∈ (-1, 0)` (no assumed Friedmann hypothesis). -/
def archMA2MannheimKazanasCosmology : TypedArchetype Unit .proved where
  name := `archMA2MannheimKazanasCosmology
  phase := 2
  claim := fun _ =>
    (∀ (α β γ κ r : ℝ), r ≠ 0 →
      radialBiharmonic (mannheimKazanasPotential α β γ κ) r = 0 ∧
      radialLaplacian (mannheimKazanasPotential α β γ κ) r = 2 * γ / r - 6 * κ) ∧
    (∀ (β γ κ r : ℝ), r ≠ 0 →
      let B := mkExactMetricPotential β γ κ
      sphericalBachWrr r (B r) (deriv B r) (deriv (deriv B) r) (deriv (deriv (deriv B)) r) = 0 ∧
      sphericalBachW00 r (B r) (deriv B r) (deriv (deriv B) r) (deriv (deriv (deriv B)) r)
        (deriv (deriv (deriv (deriv B))) r) = 0) ∧
    (∀ (S₀ lam k t : ℝ), S₀ ≠ 0 → 0 < lam → k < 0 → 0 < t →
      0 < mannheimScaleFactor S₀ lam k t ∧
      0 < deriv (mannheimScaleFactor S₀ lam k) t ∧
      0 < deriv (deriv (mannheimScaleFactor S₀ lam k)) t ∧
      mannheimOmegaLambdaBar S₀ lam k t + mannheimOmegaKBar S₀ lam k t = 1 ∧
      -1 < mannheimDeceleration S₀ lam k t ∧ mannheimDeceleration S₀ lam k t < 0) ∧
    (∀ (S₀ : ℝ), S₀ ≠ 0 → conformalGeff S₀ < 0)
  evidence := fun _ =>
    ⟨fun α β γ κ r hr =>
      ⟨(mannheimKazanas_biharmonic_and_schwarzschild_reduction α β γ κ).1 r hr,
       (mannheimKazanas_biharmonic_and_schwarzschild_reduction α β γ κ).2.1 r hr⟩,
     mannheimKazanas_true_deriv_bach_vacuum,
     fun S₀ lam k t hS hlam hk ht =>
       let h := mannheim_conformal_friedmann_ode_and_acceleration_constructive S₀ lam k t hS hlam hk ht
       ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
     fun S₀ hS => (mannheim_conformal_cosmology_deceleration_bounds S₀ (-(1/2)) 1 1 (1/2) 1 (1/2)
       hS (by norm_num) one_pos one_ne_zero (by norm_num) (by norm_num) one_pos (by norm_num) (by norm_num)).1⟩

#register_archetype archMA1WeylScaleCurvature
#audit_archetype archMA1WeylScaleCurvature
#register_archetype archMA2MannheimKazanasCosmology
#audit_archetype archMA2MannheimKazanasCosmology

end ArchetypeRegistrations

end InfoGeometry.Conformal.MannheimWeylKazanasCosmology
