import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

/-!
# Finite Gibbs Thermodynamics

Finite-state thermodynamic layer parameterized by an energy function `E` and
divergence scale `ε`.
-/

namespace InfoGeometry.Thermo

section Finite

variable {Ω : Type _} [Fintype Ω] [Nonempty Ω]

/-- Gibbs weight `exp(-E/ε)`. -/
noncomputable def weight (E : Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(E ω) / ε)

/-- Partition function `Z(ε)`. -/
noncomputable def Z (E : Ω → ℝ) (ε : ℝ) : ℝ :=
  ∑ ω, weight E ε ω

/-- Log-partition function `log Z(ε)`. -/
noncomputable def logZ (E : Ω → ℝ) (ε : ℝ) : ℝ :=
  Real.log (Z E ε)

/-- Free energy `F(ε) = -ε log Z(ε)`. -/
noncomputable def freeEnergy (E : Ω → ℝ) (ε : ℝ) : ℝ :=
  -ε * logZ E ε

omit [Nonempty Ω] in
@[simp] lemma freeEnergy_def' (E : Ω → ℝ) (ε : ℝ) :
    freeEnergy E ε = -ε * Real.log (Z E ε) := rfl

/-- Soft-min functional induced by `E` at scale `ε`. -/
noncomputable def softMin (E : Ω → ℝ) (ε : ℝ) : ℝ :=
  freeEnergy E ε

/-- Gibbs probability mass `P_ε(ω) = w_ε(ω) / Z_ε`. -/
noncomputable def gibbsProb (E : Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ :=
  weight E ε ω / Z E ε

/-- Expectation under a finite weight/probability function. -/
noncomputable def expectation (P : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω, P ω * f ω

lemma expectation_add (P f g : Ω → ℝ) :
    expectation P (fun ω => f ω + g ω) =
      expectation P f + expectation P g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_smul (P f : Ω → ℝ) (c : ℝ) :
    expectation P (fun ω => c * f ω) = c * expectation P f := by
  unfold expectation
  calc
    ∑ ω, P ω * (c * f ω) =
        ∑ ω, c * (P ω * f ω) := by
          apply Finset.sum_congr rfl
          intro ω hω
          ring
    _ = c * ∑ ω, P ω * f ω := by
          rw [Finset.mul_sum]

noncomputable def expectationLinear (P : Ω → ℝ) :
    (Ω → ℝ) →ₗ[ℝ] ℝ where
  toFun := expectation P
  map_add' f g := by
    simpa [Pi.add_apply] using expectation_add P f g
  map_smul' c f := by
    simpa [Pi.smul_apply] using expectation_smul P f c

@[simp] lemma expectationLinear_apply (P f : Ω → ℝ) :
    expectationLinear P f = expectation P f :=
  rfl

lemma expectationLinear_const_of_sum_one (P : Ω → ℝ) (c : ℝ)
    (hP : ∑ ω, P ω = 1) :
    expectationLinear P (fun _ => c) = c := by
  unfold expectationLinear expectation
  calc
    ∑ ω, P ω * c = c * ∑ ω, P ω := by
      calc
        ∑ ω, P ω * c = ∑ ω, c * P ω := by
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        _ = c * ∑ ω, P ω := by
          rw [Finset.mul_sum]
    _ = c := by rw [hP]; ring

lemma expectation_add_constant (P f : Ω → ℝ) (c : ℝ) :
    expectation P (fun ω => f ω + c) =
      expectation P f + c * (∑ ω, P ω) := by
  unfold expectation
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    (∑ ω, P ω * c) = ∑ ω, c * P ω := by
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    _ = c * ∑ ω, P ω := by
      rw [Finset.mul_sum]

lemma expectation_const_of_sum_one (P : Ω → ℝ) (c : ℝ)
    (hP : ∑ ω, P ω = 1) :
    expectation P (fun _ => c) = c := by
  unfold expectation
  calc
    ∑ ω, P ω * c = c * ∑ ω, P ω := by
      calc
        ∑ ω, P ω * c = ∑ ω, c * P ω := by
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        _ = c * ∑ ω, P ω := by
          rw [Finset.mul_sum]
    _ = c := by rw [hP]; ring

/-- Internal energy `U_ε = E_{P_ε}[E]`. -/
noncomputable def internalEnergy (E : Ω → ℝ) (ε : ℝ) : ℝ :=
  expectation (gibbsProb E ε) E

/-- Shannon entropy `S_ε = -E_{P_ε}[\log P_ε]`. -/
noncomputable def shannonEntropy (E : Ω → ℝ) (ε : ℝ) : ℝ :=
  -expectation (gibbsProb E ε) (fun ω => Real.log (gibbsProb E ε ω))

lemma Z_pos (E : Ω → ℝ) (ε : ℝ) : 0 < Z E ε := by
  classical
  unfold Z
  simpa using
    (Finset.sum_pos
      (s := (Finset.univ : Finset Ω))
      (f := fun ω => weight E ε ω)
      (by
        intro ω hω
        unfold weight
        exact Real.exp_pos _)
      Finset.univ_nonempty)

lemma Z_ne_zero (E : Ω → ℝ) (ε : ℝ) : Z E ε ≠ 0 :=
  (Z_pos E ε).ne'

omit [Fintype Ω] [Nonempty Ω] in
lemma weight_pos (E : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    0 < weight E ε ω := by
  unfold weight
  exact Real.exp_pos _

/-- A constant energy shift contributes one common multiplicative weight factor. -/
lemma weight_add_constant
    (E : Ω → ℝ) (c ε : ℝ) (hε : ε ≠ 0) (ω : Ω) :
    weight (fun ω => E ω + c) ε ω =
      Real.exp (-c / ε) * weight E ε ω := by
  unfold weight
  change Real.exp (-(E ω + c) / ε) =
    Real.exp (-c / ε) * Real.exp (-(E ω) / ε)
  rw [show -(E ω + c) / ε = (-c / ε) + (-(E ω) / ε) by
        field_simp [hε] <;> ring,
    Real.exp_add]

/-- The partition function transforms covariantly under a constant energy shift. -/
lemma Z_add_constant
    (E : Ω → ℝ) (c ε : ℝ) (hε : ε ≠ 0) :
    Z (fun ω => E ω + c) ε =
      Real.exp (-c / ε) * Z E ε := by
  unfold Z
  calc
    ∑ ω, weight (fun ω => E ω + c) ε ω =
        ∑ ω, Real.exp (-c / ε) * weight E ε ω := by
          apply Finset.sum_congr rfl
          intro ω hω
          exact weight_add_constant E c ε hε ω
    _ = Real.exp (-c / ε) * ∑ ω, weight E ε ω := by
          rw [Finset.mul_sum]

/-- The log-partition function transforms by the additive gauge term. -/
lemma logZ_add_constant
    (E : Ω → ℝ) (c ε : ℝ) (hε : ε ≠ 0) :
    logZ (fun ω => E ω + c) ε = logZ E ε - c / ε := by
  unfold logZ
  rw [Z_add_constant E c ε hε]
  rw [Real.log_mul (Real.exp_ne_zero _) (Z_ne_zero E ε), Real.log_exp]
  ring

/-- Free energy is affine-covariant under a common energy gauge shift. -/
lemma freeEnergy_add_constant
    (E : Ω → ℝ) (c ε : ℝ) (hε : ε ≠ 0) :
    freeEnergy (fun ω => E ω + c) ε = freeEnergy E ε + c := by
  unfold freeEnergy logZ
  rw [Z_add_constant E c ε hε]
  rw [Real.log_mul (Real.exp_ne_zero _) (Z_ne_zero E ε), Real.log_exp]
  field_simp [hε]
  ring

/-- The soft-minimum inherits the same energy gauge covariance. -/
lemma softMin_add_constant
    (E : Ω → ℝ) (c ε : ℝ) (hε : ε ≠ 0) :
    softMin (fun ω => E ω + c) ε = softMin E ε + c := by
  exact freeEnergy_add_constant E c ε hε

/-- Gibbs probabilities are invariant under a common energy gauge shift. -/
lemma gibbsProb_add_constant_invariant
    (E : Ω → ℝ) (c ε : ℝ) (hε : ε ≠ 0) (ω : Ω) :
    gibbsProb (fun ω => E ω + c) ε ω = gibbsProb E ε ω := by
  unfold gibbsProb
  rw [weight_add_constant E c ε hε ω, Z_add_constant E c ε hε]
  field_simp [Real.exp_ne_zero, Z_ne_zero E ε]

omit [Nonempty Ω] in
lemma softMin_def (E : Ω → ℝ) (ε : ℝ) :
    softMin E ε = -ε * Real.log (∑ ω, Real.exp (-(E ω) / ε)) := by
  simp [softMin, freeEnergy, logZ, Z, weight]

lemma gibbsProb_nonneg (E : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    0 ≤ gibbsProb E ε ω := by
  unfold gibbsProb weight
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Z_pos E ε))

lemma gibbsProb_pos (E : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    0 < gibbsProb E ε ω := by
  unfold gibbsProb
  exact div_pos (weight_pos E ε ω) (Z_pos E ε)

lemma gibbsProb_sum_one (E : Ω → ℝ) (ε : ℝ) :
    ∑ ω, gibbsProb E ε ω = 1 := by
  unfold gibbsProb
  have hZne : Z E ε ≠ 0 := Z_ne_zero E ε
  calc
    ∑ ω, weight E ε ω / Z E ε
        = (∑ ω, weight E ε ω) / Z E ε := by
            symm
            simpa using
              (Finset.sum_div
                (s := (Finset.univ : Finset Ω))
                (f := fun ω => weight E ε ω)
                (a := Z E ε))
    _ = Z E ε / Z E ε := by simp [Z]
    _ = 1 := by exact div_self hZne

/-- Internal energy is affine-covariant under a common energy gauge shift. -/
lemma internalEnergy_add_constant
    (E : Ω → ℝ) (c ε : ℝ) (hε : ε ≠ 0) :
    internalEnergy (fun ω => E ω + c) ε = internalEnergy E ε + c := by
  unfold internalEnergy expectation
  simp_rw [gibbsProb_add_constant_invariant E c ε hε]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hconstant :
      (∑ ω, gibbsProb E ε ω * c) = c := by
    calc
      (∑ ω, gibbsProb E ε ω * c) =
          c * ∑ ω, gibbsProb E ε ω := by
            calc
              (∑ ω, gibbsProb E ε ω * c) =
                  ∑ ω, c * gibbsProb E ε ω := by
                    apply Finset.sum_congr rfl
                    intro ω hω
                    ring
              _ = c * ∑ ω, gibbsProb E ε ω := by
                    rw [Finset.mul_sum]
      _ = c := by rw [gibbsProb_sum_one]; ring
  rw [hconstant]

/-- Shannon entropy is invariant under a common energy gauge shift. -/
lemma shannonEntropy_add_constant
    (E : Ω → ℝ) (c ε : ℝ) (hε : ε ≠ 0) :
    shannonEntropy (fun ω => E ω + c) ε = shannonEntropy E ε := by
  unfold shannonEntropy expectation
  simp_rw [gibbsProb_add_constant_invariant E c ε hε]

lemma log_gibbsProb (E : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    Real.log (gibbsProb E ε ω) = -(E ω) / ε - logZ E ε := by
  unfold gibbsProb weight logZ
  rw [Real.log_div (by positivity) (Z_ne_zero E ε)]
  simp

/-- The normalized Gibbs weight is the exponential of the log-partition readout. -/
lemma gibbsProb_eq_exp_sub_logZ (E : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    gibbsProb E ε ω =
      Real.exp (-(E ω) / ε - logZ E ε) := by
  unfold gibbsProb weight logZ
  rw [Real.exp_sub, Real.exp_log (Z_pos E ε)]

/-- The exponential-family form is normalized by the log-partition function. -/
lemma exp_sub_logZ_sum_one (E : Ω → ℝ) (ε : ℝ) :
    ∑ ω, Real.exp (-(E ω) / ε - logZ E ε) = 1 := by
  calc
    ∑ ω, Real.exp (-(E ω) / ε - logZ E ε) =
        ∑ ω, gibbsProb E ε ω := by
          apply Finset.sum_congr rfl
          intro ω hω
          exact (gibbsProb_eq_exp_sub_logZ E ε ω).symm
    _ = 1 := gibbsProb_sum_one E ε

lemma neg_log_gibbsProb_eq_energy_div_add_logZ
    (E : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    -Real.log (gibbsProb E ε ω) = E ω / ε + logZ E ε := by
  rw [log_gibbsProb]
  ring

lemma shannonEntropy_eq_internal_div_add_logZ
    (E : Ω → ℝ) (ε : ℝ) :
    shannonEntropy E ε = internalEnergy E ε / ε + logZ E ε := by
  unfold shannonEntropy internalEnergy expectation
  calc
    -∑ ω, gibbsProb E ε ω * Real.log (gibbsProb E ε ω)
        = -∑ ω, gibbsProb E ε ω * (-(E ω) / ε - logZ E ε) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro ω hω
            rw [log_gibbsProb]
    _ = -∑ ω, (gibbsProb E ε ω * (-(E ω) / ε) + gibbsProb E ε ω * (-logZ E ε)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro ω hω
          ring
    _ = -((∑ ω, gibbsProb E ε ω * (-(E ω) / ε))
            + (∑ ω, gibbsProb E ε ω * (-logZ E ε))) := by
          rw [Finset.sum_add_distrib]
    _ = -(((-1 / ε) * (∑ ω, gibbsProb E ε ω * E ω))
            + ((-logZ E ε) * (∑ ω, gibbsProb E ε ω))) := by
          congr
          · calc
              ∑ ω, gibbsProb E ε ω * (-(E ω) / ε)
                  = ∑ ω, (-1 / ε) * (gibbsProb E ε ω * E ω) := by
                      refine Finset.sum_congr rfl ?_
                      intro ω hω
                      ring
              _ = (-1 / ε) * (∑ ω, gibbsProb E ε ω * E ω) := by
                    simpa using
                      (Finset.mul_sum (s := Finset.univ) (a := -1 / ε)
                        (f := fun ω => gibbsProb E ε ω * E ω)).symm
          · calc
              ∑ ω, gibbsProb E ε ω * (-logZ E ε)
                  = ∑ ω, (-logZ E ε) * gibbsProb E ε ω := by
                      refine Finset.sum_congr rfl ?_
                      intro ω hω
                      ring
              _ = (-logZ E ε) * (∑ ω, gibbsProb E ε ω) := by
                    simpa using
                      (Finset.mul_sum (s := Finset.univ) (a := -logZ E ε)
                        (f := fun ω => gibbsProb E ε ω)).symm
    _ = internalEnergy E ε / ε + logZ E ε := by
          rw [gibbsProb_sum_one]
          simp [internalEnergy, expectation]
          ring

lemma freeEnergy_eq_internal_sub_scale_entropy
    (E : Ω → ℝ) (ε : ℝ)
    (hε : ε ≠ 0) :
    freeEnergy E ε = internalEnergy E ε - ε * shannonEntropy E ε := by
  rw [shannonEntropy_eq_internal_div_add_logZ]
  unfold freeEnergy
  field_simp [hε]
  ring

lemma internalEnergy_sub_freeEnergy
    (E : Ω → ℝ) (ε : ℝ) (hε : ε ≠ 0) :
    internalEnergy E ε - freeEnergy E ε = ε * shannonEntropy E ε := by
  rw [freeEnergy_eq_internal_sub_scale_entropy (E := E) (ε := ε) hε]
  ring

lemma epsilon_mul_shannonEntropy
    (E : Ω → ℝ) (ε : ℝ) (hε : ε ≠ 0) :
    ε * shannonEntropy E ε = internalEnergy E ε - freeEnergy E ε :=
  (internalEnergy_sub_freeEnergy (E := E) (ε := ε) hε).symm

end Finite

end InfoGeometry.Thermo
namespace InfoGeometry.Thermo

variable {Ω : Type*}

/-!
The finite prior/degeneracy correction is already contained in the Gibbs
weight: shifting the energy by `- ε log h - μ` factors the weight into the
chemical, prior, and Boltzmann contributions.  This is the native finite
identity used by the projective Gibbs construction.
-/
theorem gibbs_weight_prior_factorization
    (E h : Ω → ℝ) (ε μ : ℝ) (ω : Ω)
    (hε : ε ≠ 0) (hh : 0 < h ω) :
    weight (fun x => E x - ε * Real.log (h x) - μ) ε ω =
      Real.exp (μ / ε) * h ω * weight E ε ω := by
  unfold weight
  have harg :
      -(E ω - ε * Real.log (h ω) - μ) / ε =
        μ / ε + Real.log (h ω) + (-E ω / ε) := by
    field_simp [hε]
    ring
  rw [harg, Real.exp_add, Real.exp_add, Real.exp_log hh]

theorem gibbs_partition_prior_factorization
    [Fintype Ω] (E h : Ω → ℝ) (ε μ : ℝ) (hε : ε ≠ 0)
    (hh : ∀ ω, 0 < h ω) :
    Z (fun x => E x - ε * Real.log (h x) - μ) ε =
      Real.exp (μ / ε) * ∑ ω, h ω * weight E ε ω := by
  unfold Z
  simp_rw [gibbs_weight_prior_factorization E h ε μ _ hε (hh _)]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

end InfoGeometry.Thermo
