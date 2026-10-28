/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.BdGChiralBlockMatrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Faithful block action and a quantitative chiral spectral gap

The existing BdG matrix entries act as genuine bounded operators on two
copies of the Hilbert space. The product carries its native maximum norm;
no inner product on that product is used. Lower bounds on both sector maps
give a norm lower bound. In finite dimension this excludes a disc from the
native complex spectrum. No scalar or commuting operator restriction occurs.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.ChiralBlockSpectralGap

open InfoGeometry.Physics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The full operator-valued two-by-two block acts on the two sector spaces. -/
def blockAction (M : BdGBlock (E →L[ℂ] E)) : E × E →L[ℂ] E × E :=
  ((M 0 0).comp (ContinuousLinearMap.fst ℂ E E) +
      (M 0 1).comp (ContinuousLinearMap.snd ℂ E E)).prod
    ((M 1 0).comp (ContinuousLinearMap.fst ℂ E E) +
      (M 1 1).comp (ContinuousLinearMap.snd ℂ E E))

@[simp] theorem blockAction_apply (M : BdGBlock (E →L[ℂ] E)) (z : E × E) :
    blockAction M z = (M 0 0 z.1 + M 0 1 z.2, M 1 0 z.1 + M 1 1 z.2) := rfl

/-- Multiplication of the original block matrices is composition of their actions. -/
theorem blockAction_mul (M N : BdGBlock (E →L[ℂ] E)) :
    blockAction (M * N) = blockAction M * blockAction N := by
  ext z <;>
    simp [blockAction_apply, Matrix.mul_apply, Fin.sum_univ_two,
      add_comm]

/-- The action loses none of the four arbitrary operator blocks. -/
theorem blockAction_injective : Function.Injective (blockAction (E := E)) := by
  intro M N h
  ext i j x
  have hleft := congrArg (fun f : E × E →L[ℂ] E × E => f (x, 0)) h
  have hright := congrArg (fun f : E × E →L[ℂ] E × E => f (0, x)) h
  fin_cases i <;> fin_cases j
  · simpa using congrArg Prod.fst hleft
  · simpa using congrArg Prod.fst hright
  · simpa using congrArg Prod.snd hleft
  · simpa using congrArg Prod.snd hright

variable [CompleteSpace E]

@[simp] theorem blockAction_dirac_apply (Δ : E →L[ℂ] E) (z : E × E) :
    blockAction (diracOperator Δ) z = (Δ z.2, (star Δ) z.1) := by
  simp [diracOperator]

/-- Both directions of the intersector map are needed for a uniform bound. -/
theorem diracAction_lowerBound (Δ : E →L[ℂ] E) {m : ℝ} (hm : 0 ≤ m)
    (hΔ : ∀ x : E, m * ‖x‖ ≤ ‖Δ x‖)
    (hΔs : ∀ x : E, m * ‖x‖ ≤ ‖(star Δ) x‖) (z : E × E) :
    m * ‖z‖ ≤ ‖blockAction (diracOperator Δ) z‖ := by
  rw [blockAction_dirac_apply, Prod.norm_def, Prod.norm_def,
    mul_max_of_nonneg _ _ hm]
  exact max_le ((hΔs z.1).trans (le_max_right _ _))
    ((hΔ z.2).trans (le_max_left _ _))

omit [CompleteSpace E] in
/-- A unit supplies its lower bound through the norm of its actual inverse. -/
theorem norm_le_inverse_norm_mul (u : (E →L[ℂ] E)ˣ) (x : E) :
    ‖x‖ ≤ ‖(↑(u⁻¹) : E →L[ℂ] E)‖ * ‖(↑u : E →L[ℂ] E) x‖ := by
  have h := (↑(u⁻¹) : E →L[ℂ] E).le_opNorm ((↑u : E →L[ℂ] E) x)
  simpa only [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self] using h

/-- Invertible coupling gives positive bounds on both sector maps; no
normality or commutation of the coupling with its adjoint is assumed. -/
theorem exists_positive_sector_bound_of_isUnit (Δ : E →L[ℂ] E)
    (hΔ : IsUnit Δ) :
    ∃ m : ℝ, 0 < m ∧ (∀ x : E, m * ‖x‖ ≤ ‖Δ x‖) ∧
      (∀ x : E, m * ‖x‖ ≤ ‖(star Δ) x‖) := by
  have hΔstar : IsUnit (star Δ) := hΔ.star
  obtain ⟨u, hu⟩ := hΔ
  obtain ⟨v, hv⟩ := hΔstar
  let c : ℝ := 1 + ‖(↑(u⁻¹) : E →L[ℂ] E)‖ + ‖(↑(v⁻¹) : E →L[ℂ] E)‖
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound (w : (E →L[ℂ] E)ˣ)
      (hw : ‖(↑(w⁻¹) : E →L[ℂ] E)‖ ≤ c) (x : E) :
      (1 / c) * ‖x‖ ≤ ‖(↑w : E →L[ℂ] E) x‖ := by
    have h := (norm_le_inverse_norm_mul w x).trans
      (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
    calc
      (1 / c) * ‖x‖ = ‖x‖ / c := by ring
      _ ≤ ‖(↑w : E →L[ℂ] E) x‖ :=
        (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using h)
  refine ⟨1 / c, one_div_pos.mpr hc, ?_, ?_⟩
  · rw [← hu]
    exact hbound u (by dsimp [c]; linarith [norm_nonneg (↑(v⁻¹) : E →L[ℂ] E)])
  · rw [← hv]
    exact hbound v (by dsimp [c]; linarith [norm_nonneg (↑(u⁻¹) : E →L[ℂ] E)])

/-- An eigenvalue of the actual chiral action obeys the same lower bound. -/
theorem norm_eigenvalue_ge (Δ : E →L[ℂ] E) {m : ℝ} (hm : 0 ≤ m)
    (hΔ : ∀ x : E, m * ‖x‖ ≤ ‖Δ x‖)
    (hΔs : ∀ x : E, m * ‖x‖ ≤ ‖(star Δ) x‖)
    {μ : ℂ} {z : E × E} (hz : z ≠ 0)
    (heig : blockAction (diracOperator Δ) z = μ • z) :
    m ≤ ‖μ‖ := by
  have hbound := diracAction_lowerBound Δ hm hΔ hΔs z
  rw [heig, norm_smul] at hbound
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)).mp hbound

/-- In finite dimension the lower bound excludes the whole open spectral disc. -/
theorem norm_spectrum_ge [FiniteDimensional ℂ E]
    (Δ : E →L[ℂ] E) {m : ℝ} (hm : 0 ≤ m)
    (hΔ : ∀ x : E, m * ‖x‖ ≤ ‖Δ x‖)
    (hΔs : ∀ x : E, m * ‖x‖ ≤ ‖(star Δ) x‖)
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (blockAction (diracOperator Δ))) :
    m ≤ ‖μ‖ := by
  rw [ContinuousLinearMap.spectrum_eq] at hμ
  obtain ⟨z, hz⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hμ).exists_hasEigenvector
  exact norm_eigenvalue_ge Δ hm hΔ hΔs hz.2 hz.apply_eq_smul

/-- A positive sector bound gives actual invertibility of the chiral action. -/
theorem diracAction_isUnit [FiniteDimensional ℂ E]
    (Δ : E →L[ℂ] E) {m : ℝ} (hm : 0 < m)
    (hΔ : ∀ x : E, m * ‖x‖ ≤ ‖Δ x‖)
    (hΔs : ∀ x : E, m * ‖x‖ ≤ ‖(star Δ) x‖) :
    IsUnit (blockAction (diracOperator Δ)) := by
  apply (spectrum.zero_notMem_iff ℂ).mp
  intro hzero
  have h := norm_spectrum_ge Δ hm.le hΔ hΔs hzero
  have hnonpos : m ≤ 0 := by simpa using h
  exact hm.not_ge hnonpos

/-- Every invertible finite-dimensional coupling yields a genuine positive
gap in the spectrum of its chiral block action. -/
theorem exists_positive_spectral_gap_of_isUnit [FiniteDimensional ℂ E]
    (Δ : E →L[ℂ] E) (hΔ : IsUnit Δ) :
    ∃ m : ℝ, 0 < m ∧
      ∀ μ ∈ spectrum ℂ (blockAction (diracOperator Δ)), m ≤ ‖μ‖ := by
  obtain ⟨m, hm, hleft, hright⟩ := exists_positive_sector_bound_of_isUnit Δ hΔ
  exact ⟨m, hm, fun _ hμ => norm_spectrum_ge Δ hm.le hleft hright hμ⟩

end InfoGeometry.OperatorAlgebra.ChiralBlockSpectralGap
