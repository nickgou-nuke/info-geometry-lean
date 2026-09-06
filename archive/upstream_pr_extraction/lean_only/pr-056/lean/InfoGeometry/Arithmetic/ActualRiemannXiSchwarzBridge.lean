import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import InfoGeometry.Arithmetic.RiemannZetaEquivalences

/-!
# Actual completed-zeta Schwarz bridge

This owner proves the analytic realization edge between the Mellin definition
used by Mathlib's completed zeta and complex conjugation.  It does not assert
the Riemann hypothesis or a Hardy-Z factorization.
-/

noncomputable section

open Set Filter MeasureTheory Complex HurwitzZeta
open InfoGeometry.Arithmetic.RiemannZetaEquivalences
open scoped Topology ComplexConjugate

namespace InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge

def CompletedRiemannZetaSchwarzHypothesis : Prop :=
  ∀ s : ℂ, completedRiemannZeta (star s) =
    star (completedRiemannZeta s)

def RiemannXiSchwarzHypothesis : Prop :=
  ∀ s : ℂ, riemannXi (star s) = star (riemannXi s)

/-! ### Concrete Mellin conjugation -/

private theorem mellin_star_conj_of_star_real
    (f : ℝ → ℂ) (hf : ∀ t, star (f t) = f t) (s : ℂ) :
    star (mellin f s) = mellin f (star s) := by
  unfold mellin
  change conj (∫ t : ℝ, (t : ℂ) ^ (s - 1) • f t ∂volume.restrict (Ioi 0)) = _
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg (le_of_lt ht)]
    exact (ne_of_gt Real.pi_pos).symm
  change star ((t : ℂ) ^ (s - 1) * f t) =
    (t : ℂ) ^ (star s - 1) * f t
  rw [star_mul]
  have hpow : star ((t : ℂ) ^ (s - 1)) = (t : ℂ) ^ (star s - 1) := by
    have h := (cpow_conj (t : ℂ) (s - 1) harg).symm
    simpa [sub_eq_add_neg] using h
  rw [hpow, hf]
  exact mul_comm _ _

private theorem hurwitzEvenFEPair_zero_fmodif_star (t : ℝ) :
    star ((hurwitzEvenFEPair 0).f_modif t) =
      (hurwitzEvenFEPair 0).f_modif t := by
  simp only [WeakFEPair.f_modif, hurwitzEvenFEPair, Function.comp_def]
  by_cases h1 : t ∈ Ioi 1 <;> by_cases h2 : t ∈ Ioo 0 1 <;>
    simp [h1, h2]

private theorem completedRiemannZeta_star_concrete (s : ℂ) :
    star (completedRiemannZeta s) =
      completedRiemannZeta (star s) := by
  unfold completedRiemannZeta completedHurwitzZetaEven
  have hΛ (x : ℂ) :
      star ((hurwitzEvenFEPair 0).Λ x) =
        (hurwitzEvenFEPair 0).Λ (star x) := by
    unfold WeakFEPair.Λ WeakFEPair.Λ₀
    rw [star_sub, star_sub]
    rw [mellin_star_conj_of_star_real _
      hurwitzEvenFEPair_zero_fmodif_star x]
    simp [hurwitzEvenFEPair]
  change star ((hurwitzEvenFEPair 0).Λ (s / 2) * (2 : ℂ)⁻¹) =
    (hurwitzEvenFEPair 0).Λ (star s / 2) * (2 : ℂ)⁻¹
  rw [star_mul]
  have htwo : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  have harg : star (s / 2) = star s / 2 := by
    change star (s * (2 : ℂ)⁻¹) = star s * (2 : ℂ)⁻¹
    rw [star_mul, htwo]
    exact mul_comm _ _
  rw [htwo, hΛ (s / 2), harg]
  change (2 : ℂ)⁻¹ * ((hurwitzEvenFEPair 0).Λ (star s / 2)) =
    ((hurwitzEvenFEPair 0).Λ (star s / 2)) * (2 : ℂ)⁻¹
  exact mul_comm _ _

theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (star s) = star (completedRiemannZeta s) := by
  exact (completedRiemannZeta_star_concrete s).symm

theorem actualCompletedRiemannZetaSchwarz :
    CompletedRiemannZetaSchwarzHypothesis := by
  intro s
  exact completedRiemannZeta_conj s

/-- Conditional readback of Xi Schwarz symmetry from a completed-zeta datum. -/
theorem riemannXi_conj_of_completed
    (h : CompletedRiemannZetaSchwarzHypothesis) (s : ℂ) :
    riemannXi (star s) = star (riemannXi s) := by
  unfold riemannXi
  rw [h]
  simp

/-- The completed-zeta datum is realized above from the concrete Mellin
construction, so the Xi Schwarz law has an unconditional owner-level
corollary. -/
theorem actualRiemannXi_conj (s : ℂ) :
    riemannXi (star s) = star (riemannXi s) := by
  exact riemannXi_conj_of_completed actualCompletedRiemannZetaSchwarz s

/-- 🏆 THEOREM 2: Riemann Xi Schwarz Reflection Symmetry:
    $$\xi(\bar{s}) = \overline{\xi(s)}$$ -/
theorem riemannXi_conj_of_datum
    (h : RiemannXiSchwarzHypothesis) (s : ℂ) :
    riemannXi (star s) = star (riemannXi s) := h s

/-- 🏆 THEOREM 3: Alias for Xi Schwarz symmetry -/
theorem riemannXi_star_of_datum
    (h : RiemannXiSchwarzHypothesis) (s : ℂ) :
    riemannXi (star s) = star (riemannXi s) := h s

end InfoGeometry.Arithmetic.ActualRiemannXiSchwarzBridge
