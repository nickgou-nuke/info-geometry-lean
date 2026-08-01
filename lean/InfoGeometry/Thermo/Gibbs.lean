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

lemma log_gibbsProb (E : Ω → ℝ) (ε : ℝ) (ω : Ω) :
    Real.log (gibbsProb E ε ω) = -(E ω) / ε - logZ E ε := by
  unfold gibbsProb weight logZ
  rw [Real.log_div (by positivity) (Z_ne_zero E ε)]
  simp

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
