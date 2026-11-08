/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
import InfoGeometry.Analysis.OperatorDirichletSpectralGap
import InfoGeometry.GrandUnification.CanonicalSpectralGap
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

@[simp] theorem blockAction_zero :
    blockAction (0 : BdGBlock (E →L[ℂ] E)) = 0 := by
  ext z <;> simp [blockAction_apply]

@[simp] theorem blockAction_one :
    blockAction (1 : BdGBlock (E →L[ℂ] E)) = 1 := by
  ext z <;> simp [blockAction_apply]

@[simp] theorem blockAction_add (M N : BdGBlock (E →L[ℂ] E)) :
    blockAction (M + N) = blockAction M + blockAction N := by
  ext z <;> simp [blockAction_apply]

/-- `blockAction` bundled as a ring homomorphism `BdGBlock (E →L[ℂ] E) →+* (E × E →L[ℂ] E × E)`. -/
def blockActionRingHom : BdGBlock (E →L[ℂ] E) →+* (E × E →L[ℂ] E × E) where
  toFun := blockAction
  map_one' := blockAction_one
  map_mul' := blockAction_mul
  map_zero' := blockAction_zero
  map_add' := blockAction_add

@[simp] theorem blockActionRingHom_apply (M : BdGBlock (E →L[ℂ] E)) :
    blockActionRingHom M = blockAction M := rfl

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

/-- An invertible bounded operator on a finite-dimensional Hilbert space has a
positive lower bound on the norm of every point in its native complex spectrum.
The constant is obtained from the norm of the actual inverse, with no normality
or diagonalization assumption. -/
theorem exists_positive_spectral_gap_of_isUnit_operator
    [FiniteDimensional ℂ E] (T : E →L[ℂ] E) (hT : IsUnit T) :
    ∃ m : ℝ, 0 < m ∧ ∀ μ ∈ spectrum ℂ T, m ≤ ‖μ‖ := by
  obtain ⟨u, hu⟩ := hT
  let k : ℝ := ‖(↑(u⁻¹) : E →L[ℂ] E)‖
  let m : ℝ := 1 / (k + 1)
  have hk : 0 ≤ k := norm_nonneg _
  have hm : 0 < m := by
    dsimp [m]
    positivity
  refine ⟨m, hm, fun μ hμ => ?_⟩
  rw [ContinuousLinearMap.spectrum_eq] at hμ
  obtain ⟨x, hx⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hμ).exists_hasEigenvector
  have hinv := norm_le_inverse_norm_mul u x
  rw [hu] at hinv
  have hEig : T x = μ • x := hx.apply_eq_smul
  rw [hEig, norm_smul] at hinv
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx.2
  have hone : 1 ≤ k * ‖μ‖ := by
    apply (mul_le_mul_iff_right₀ hxpos).mp
    simpa [k, mul_assoc, mul_left_comm, mul_comm] using hinv
  have hden : 0 < k + 1 := by linarith
  apply (div_le_iff₀ hden).2
  have hnorm : 0 ≤ ‖μ‖ := norm_nonneg _
  have hprod : 1 ≤ (k + 1) * ‖μ‖ :=
    hone.trans (mul_le_mul_of_nonneg_right (by linarith : k ≤ k + 1) hnorm)
  simpa [mul_comm] using hprod

/-! ## 2. Interconnected Zorn–Peirce–BdG–Dirichlet Spectral Gap Synthesis

Connecting `OperatorZornPeirceTetraktysBridge`, `ChiralBlockSpectralGap`,
`OperatorDirichletSpectralGap`, and `CanonicalSpectralGap` on a complex Hilbert space `E`. -/

section ZornPeirceDirichletGapBridge

open InfoGeometry.Physics.NCG
open InfoGeometry.Canonical
open InfoGeometry.Canonical.OperatorZornFourPotentialGauge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
open InfoGeometry.Analysis.OperatorDirichletLaplacian
open InfoGeometry.GrandUnification.CanonicalSpectralGap

/-- On each spatial chiral plane `i : Fin 3` of an `OperatorZornMatrix (E →L[ℂ] E)` element `X`
satisfying `X.sigma_minus i = star (X.sigma_plus i)`, the `blockAction` of `genPhi` is
`blockAction (diracOperator (X.sigma_plus i))` and its square is the `blockAction` of `genV`
(`= blockAction (diracSquare (X.sigma_plus i))`). -/
theorem zornChiralPlane_blockAction_genPhi_and_genV
    (i : Fin 3) (X : OperatorZornMatrix (E →L[ℂ] E))
    (hAdj : X.sigma_minus i = star (X.sigma_plus i)) :
    blockAction
        (genPhi (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) =
      blockAction (diracOperator (X.sigma_plus i)) ∧
    blockAction
        (genPhi (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) *
      blockAction
        (genPhi (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) =
      blockAction
        (genV (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) ∧
    blockAction
        (genV (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) =
      blockAction (diracSquare (X.sigma_plus i)) := by
  rcases zornChiralPlane_genPhi_and_genV_eq_dirac i X hAdj with ⟨hPhi, hV⟩
  have hP := peirceSheetProj_idem (A := E →L[ℂ] E)
  have hPhiSq :
      genPhi (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X) *
        genPhi (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X) =
      genV (peirceSheetProj (A := E →L[ℂ] E))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X) :=
    (archetype_A3_nilpotent_cones_and_tetraktys_table hP
      (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)).2.2.1
  refine ⟨congrArg blockAction hPhi, ?_, congrArg blockAction hV⟩
  rw [← blockAction_mul, hPhiSq]

/-- **Theorem (`zornChiralPlane_genPhi_spectral_gap_and_trivial_kernel`)**:
For any `X : OperatorZornMatrix (E →L[ℂ] E)` in finite dimension `[FiniteDimensional ℂ E]`
with `X.sigma_minus i = star (X.sigma_plus i)` and `IsUnit (X.sigma_plus i)`:
1. The Peirce–Zorn chiral operator `blockAction (genPhi peirceSheetProj (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X))`
   has a strictly positive spectral gap `∃ m > 0, ∀ μ ∈ spectrum ℂ (...), m ≤ ‖μ‖`;
2. It is a unit in `(E × E →L[ℂ] E × E)`, is injective (`Function.Injective`), and satisfies
   `CanonicalSpectralGap.TrivialKernelProp` (`kernelDimension = 0`). -/
theorem zornChiralPlane_genPhi_spectral_gap_and_trivial_kernel [FiniteDimensional ℂ E]
    (i : Fin 3) (X : OperatorZornMatrix (E →L[ℂ] E))
    (hAdj : X.sigma_minus i = star (X.sigma_plus i))
    (hUnit : IsUnit (X.sigma_plus i)) :
    let D_phi := blockAction
      (genPhi (peirceSheetProj (A := E →L[ℂ] E))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X))
    (∃ m : ℝ, 0 < m ∧ ∀ μ ∈ spectrum ℂ D_phi, m ≤ ‖μ‖) ∧
    IsUnit D_phi ∧
    Function.Injective D_phi ∧
    TrivialKernelProp D_phi.toLinearMap := by
  dsimp only
  have hEq :
      blockAction
        (genPhi (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) =
      blockAction (diracOperator (X.sigma_plus i)) :=
    (zornChiralPlane_blockAction_genPhi_and_genV i X hAdj).1
  rw [hEq]
  obtain ⟨m, hm, hleft, hright⟩ := exists_positive_sector_bound_of_isUnit (X.sigma_plus i) hUnit
  have hGap : ∃ m : ℝ, 0 < m ∧
      ∀ μ ∈ spectrum ℂ (blockAction (diracOperator (X.sigma_plus i))), m ≤ ‖μ‖ :=
    ⟨m, hm, fun _ hμ => norm_spectrum_ge (X.sigma_plus i) hm.le hleft hright hμ⟩
  have hIsUnit : IsUnit (blockAction (diracOperator (X.sigma_plus i))) :=
    diracAction_isUnit (X.sigma_plus i) hm hleft hright
  have hInj : Function.Injective (blockAction (diracOperator (X.sigma_plus i))) := by
    intro z₁ z₂ hz
    have hDiff : blockAction (diracOperator (X.sigma_plus i)) (z₁ - z₂) = 0 := by
      rw [map_sub, hz, sub_self]
    have hBound := diracAction_lowerBound (X.sigma_plus i) hm.le hleft hright (z₁ - z₂)
    rw [hDiff, norm_zero] at hBound
    have hNormZero : ‖z₁ - z₂‖ = 0 :=
      le_antisymm ( nonpos_of_mul_nonpos_right hBound hm ) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)
  have hTrivKer : TrivialKernelProp (blockAction (diracOperator (X.sigma_plus i))).toLinearMap := by
    dsimp [TrivialKernelProp, kernelDimension]
    rw [Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]
    exact hInj
  exact ⟨hGap, hIsUnit, hInj, hTrivKer⟩

/-- **Theorem (`sum_zornChiralPlane_genV_eq_operatorDirichletLaplacian_and_spectral_gap`)**:
For any `X : OperatorZornMatrix (E →L[ℂ] E)` satisfying the Hermitian pairing relation
`∀ i : Fin 3, X.sigma_minus i = star (X.sigma_plus i)`:
1. The upper-sheet `(0, 0)` entry of the 3-axis Peirce–Zorn horizon sum
   `∑ i : Fin 3, genV peirceSheetProj (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)`
   equals the Operator Dirichlet Laplacian `laplacian X.sigma_minus`;
2. The lower-sheet `(1, 1)` entry equals the Operator Dirichlet Laplacian `laplacian X.sigma_plus`;
3. When `[FiniteDimensional ℂ E]`, both sheet entries of the 3-axis Peirce–Zorn horizon sum admit
   strictly positive coercive bounds on their kernel orthogonal complements and strictly positive
   spectral gaps away from zero in the native Mathlib `spectrum ℂ`. -/
theorem sum_zornChiralPlane_genV_eq_operatorDirichletLaplacian_and_spectral_gap
    [FiniteDimensional ℂ E]
    (X : OperatorZornMatrix (E →L[ℂ] E))
    (hAdj : ∀ i : Fin 3, X.sigma_minus i = star (X.sigma_plus i)) :
    let V_sum := ∑ i : Fin 3,
      genV (peirceSheetProj (A := E →L[ℂ] E))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)
    V_sum 0 0 = laplacian X.sigma_minus ∧
    V_sum 1 1 = laplacian X.sigma_plus ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧
      (∀ x ∈ kernelOrthogonal X.sigma_minus, c₀ * ‖x‖ ^ 2 ≤ energy X.sigma_minus x) ∧
      (∀ μ ∈ spectrum ℂ (V_sum 0 0), μ = 0 ∨ c₀ ≤ μ.re)) ∧
    (∃ c₁ : ℝ, 0 < c₁ ∧
      (∀ x ∈ kernelOrthogonal X.sigma_plus, c₁ * ‖x‖ ^ 2 ≤ energy X.sigma_plus x) ∧
      (∀ μ ∈ spectrum ℂ (V_sum 1 1), μ = 0 ∨ c₁ ≤ μ.re)) := by
  dsimp only
  have hSum := sum_zornChiralPlane_genV X X
  have h00 :
      (∑ i : Fin 3,
        genV (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) 0 0 =
      laplacian X.sigma_minus := by
    have hEntry := congrArg (fun M : Matrix (Fin 2) (Fin 2) (E →L[ℂ] E) => M 0 0) hSum
    dsimp at hEntry
    rw [hEntry]
    unfold NCZornElement.zornDot laplacian
    rw [Fin.sum_univ_three]
    have h0 : (ContinuousLinearMap.adjoint (X.sigma_minus 0)).comp (X.sigma_minus 0) =
        X.sigma_plus 0 * X.sigma_minus 0 := by
      change star (X.sigma_minus 0) * X.sigma_minus 0 = _
      rw [hAdj 0, star_star]
    have h1 : (ContinuousLinearMap.adjoint (X.sigma_minus 1)).comp (X.sigma_minus 1) =
        X.sigma_plus 1 * X.sigma_minus 1 := by
      change star (X.sigma_minus 1) * X.sigma_minus 1 = _
      rw [hAdj 1, star_star]
    have h2 : (ContinuousLinearMap.adjoint (X.sigma_minus 2)).comp (X.sigma_minus 2) =
        X.sigma_plus 2 * X.sigma_minus 2 := by
      change star (X.sigma_minus 2) * X.sigma_minus 2 = _
      rw [hAdj 2, star_star]
    rw [h0, h1, h2]
  have h11 :
      (∑ i : Fin 3,
        genV (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) 1 1 =
      laplacian X.sigma_plus := by
    have hEntry := congrArg (fun M : Matrix (Fin 2) (Fin 2) (E →L[ℂ] E) => M 1 1) hSum
    dsimp at hEntry
    rw [hEntry]
    unfold NCZornElement.zornDot laplacian
    rw [Fin.sum_univ_three]
    have h0 : (ContinuousLinearMap.adjoint (X.sigma_plus 0)).comp (X.sigma_plus 0) =
        X.sigma_minus 0 * X.sigma_plus 0 := by
      change star (X.sigma_plus 0) * X.sigma_plus 0 = _
      rw [hAdj 0]
    have h1 : (ContinuousLinearMap.adjoint (X.sigma_plus 1)).comp (X.sigma_plus 1) =
        X.sigma_minus 1 * X.sigma_plus 1 := by
      change star (X.sigma_plus 1) * X.sigma_plus 1 = _
      rw [hAdj 1]
    have h2 : (ContinuousLinearMap.adjoint (X.sigma_plus 2)).comp (X.sigma_plus 2) =
        X.sigma_minus 2 * X.sigma_plus 2 := by
      change star (X.sigma_plus 2) * X.sigma_plus 2 = _
      rw [hAdj 2]
    rw [h0, h1, h2]
  obtain ⟨c₀, hc₀, hBound₀⟩ := exists_positive_coercive_bound X.sigma_minus
  obtain ⟨c₁, hc₁, hBound₁⟩ := exists_positive_coercive_bound X.sigma_plus
  refine ⟨h00, h11, ⟨c₀, hc₀, hBound₀, ?_⟩, ⟨c₁, hc₁, hBound₁, ?_⟩⟩
  · rw [h00]
    intro μ hμ
    by_cases hz : μ = 0
    · exact Or.inl hz
    · right
      rw [ContinuousLinearMap.spectrum_eq] at hμ
      obtain ⟨x, hx⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hμ).exists_hasEigenvector
      exact re_eigenvalue_ge_of_coercive_bound X.sigma_minus hBound₀ hz hx.2 hx.apply_eq_smul
  · rw [h11]
    intro μ hμ
    by_cases hz : μ = 0
    · exact Or.inl hz
    · right
      rw [ContinuousLinearMap.spectrum_eq] at hμ
      obtain ⟨x, hx⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hμ).exists_hasEigenvector
      exact re_eigenvalue_ge_of_coercive_bound X.sigma_plus hBound₁ hz hx.2 hx.apply_eq_smul

omit [CompleteSpace E] in
/-- **Theorem (`blockAction_intertwines_peirce_tetraktys_and_bdg`)**:
The faithful operator-block ring homomorphism `blockActionRingHom` intertwines the sheet idempotent
`peirceSheetProj`, the chiral grading `chiralGrading = invS peirceSheetProj`, the Peirce Tetraktys
generators `genPhi`, `genJ`, `genV`, and the massive Peirce–BdG operator `peirceBdGHamiltonian`
with their native Peirce Spine counterparts on the product operator ring `E × E →L[ℂ] E × E`. -/
theorem blockAction_intertwines_peirce_tetraktys_and_bdg
    (D M N : BdGBlock (E →L[ℂ] E)) :
    let P_E := blockAction (peirceSheetProj (A := E →L[ℂ] E))
    P_E * P_E = P_E ∧
    blockAction (chiralGrading (A := E →L[ℂ] E)) = invS P_E ∧
    blockAction (genPhi (peirceSheetProj (A := E →L[ℂ] E)) M N) =
      genPhi P_E (blockAction M) (blockAction N) ∧
    blockAction (genJ (peirceSheetProj (A := E →L[ℂ] E)) M N) =
      genJ P_E (blockAction M) (blockAction N) ∧
    blockAction (genV (peirceSheetProj (A := E →L[ℂ] E)) M N) =
      genV P_E (blockAction M) (blockAction N) ∧
    blockAction (peirceBdGHamiltonian (peirceSheetProj (A := E →L[ℂ] E)) D M N) =
      peirceBdGHamiltonian P_E (blockAction D) (blockAction M) (blockAction N) := by
  dsimp only
  let f := blockActionRingHom (E := E)
  have hP : f (peirceSheetProj (A := E →L[ℂ] E)) * f (peirceSheetProj (A := E →L[ℂ] E)) =
      f (peirceSheetProj (A := E →L[ℂ] E)) :=
    map_idempotent f peirceSheetProj_idem
  have hGrad : f (chiralGrading (A := E →L[ℂ] E)) = invS (f (peirceSheetProj (A := E →L[ℂ] E))) := by
    rw [← invS_peirceSheetProj_eq_chiralGrading]
    exact map_invS f _
  exact ⟨hP, hGrad,
    map_genPhi f _ M N,
    map_genJ f _ M N,
    map_genV f _ M N,
    (map_peirceBdGHamiltonian f _ D M N).2.2⟩

/-- **Theorem (`zornChiralPlane_genV_unitary_gauge_transport`)**:
When two `OperatorZornMatrix (E →L[ℂ] E)` packets `X, Y` satisfy the Hermitian pairing relation
`σ₋ = star σ₊` and are related on the chiral off-diagonal sectors by a unitary operator
`u : unitary (E →L[ℂ] E)` via `Y.sigma_plus i = u * X.sigma_plus i * star u`, both diagonal
sheet entries of the 3-axis Peirce–Zorn horizon sum `∑ i : Fin 3, genV peirceSheetProj ...`
transform by exact unitary conjugation `u * (·) * star u`. -/
theorem zornChiralPlane_genV_unitary_gauge_transport
    (u : unitary (E →L[ℂ] E))
    (X Y : OperatorZornMatrix (E →L[ℂ] E))
    (hAdjX : ∀ i : Fin 3, X.sigma_minus i = star (X.sigma_plus i))
    (hAdjY : ∀ i : Fin 3, Y.sigma_minus i = star (Y.sigma_plus i))
    (hGauge : ∀ i : Fin 3,
      Y.sigma_plus i = (u : E →L[ℂ] E) * X.sigma_plus i * (star u : E →L[ℂ] E)) :
    let V_X := ∑ i : Fin 3,
      genV (peirceSheetProj (A := E →L[ℂ] E))
        (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)
    let V_Y := ∑ i : Fin 3,
      genV (peirceSheetProj (A := E →L[ℂ] E))
        (zornChiralPlaneMatrix i Y) (zornChiralPlaneMatrix i Y)
    V_Y 0 0 = (u : E →L[ℂ] E) * V_X 0 0 * (star u : E →L[ℂ] E) ∧
    V_Y 1 1 = (u : E →L[ℂ] E) * V_X 1 1 * (star u : E →L[ℂ] E) := by
  dsimp only
  have hSumX := sum_zornChiralPlane_genV X X
  have hSumY := sum_zornChiralPlane_genV Y Y
  have hX00 :
      (∑ i : Fin 3,
        genV (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) 0 0 =
      laplacian X.sigma_minus := by
    have hEntry := congrArg (fun M : Matrix (Fin 2) (Fin 2) (E →L[ℂ] E) => M 0 0) hSumX
    dsimp at hEntry
    rw [hEntry]
    unfold NCZornElement.zornDot laplacian
    rw [Fin.sum_univ_three]
    have h (i : Fin 3) :
        (ContinuousLinearMap.adjoint (X.sigma_minus i)).comp (X.sigma_minus i) =
          X.sigma_plus i * X.sigma_minus i := by
      change star (X.sigma_minus i) * X.sigma_minus i = _
      rw [hAdjX i, star_star]
    rw [h 0, h 1, h 2]
  have hY00 :
      (∑ i : Fin 3,
        genV (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i Y) (zornChiralPlaneMatrix i Y)) 0 0 =
      laplacian Y.sigma_minus := by
    have hEntry := congrArg (fun M : Matrix (Fin 2) (Fin 2) (E →L[ℂ] E) => M 0 0) hSumY
    dsimp at hEntry
    rw [hEntry]
    unfold NCZornElement.zornDot laplacian
    rw [Fin.sum_univ_three]
    have h (i : Fin 3) :
        (ContinuousLinearMap.adjoint (Y.sigma_minus i)).comp (Y.sigma_minus i) =
          Y.sigma_plus i * Y.sigma_minus i := by
      change star (Y.sigma_minus i) * Y.sigma_minus i = _
      rw [hAdjY i, star_star]
    rw [h 0, h 1, h 2]
  have hX11 :
      (∑ i : Fin 3,
        genV (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i X) (zornChiralPlaneMatrix i X)) 1 1 =
      laplacian X.sigma_plus := by
    have hEntry := congrArg (fun M : Matrix (Fin 2) (Fin 2) (E →L[ℂ] E) => M 1 1) hSumX
    dsimp at hEntry
    rw [hEntry]
    unfold NCZornElement.zornDot laplacian
    rw [Fin.sum_univ_three]
    have h (i : Fin 3) :
        (ContinuousLinearMap.adjoint (X.sigma_plus i)).comp (X.sigma_plus i) =
          X.sigma_minus i * X.sigma_plus i := by
      change star (X.sigma_plus i) * X.sigma_plus i = _
      rw [hAdjX i]
    rw [h 0, h 1, h 2]
  have hY11 :
      (∑ i : Fin 3,
        genV (peirceSheetProj (A := E →L[ℂ] E))
          (zornChiralPlaneMatrix i Y) (zornChiralPlaneMatrix i Y)) 1 1 =
      laplacian Y.sigma_plus := by
    have hEntry := congrArg (fun M : Matrix (Fin 2) (Fin 2) (E →L[ℂ] E) => M 1 1) hSumY
    dsimp at hEntry
    rw [hEntry]
    unfold NCZornElement.zornDot laplacian
    rw [Fin.sum_univ_three]
    have h (i : Fin 3) :
        (ContinuousLinearMap.adjoint (Y.sigma_plus i)).comp (Y.sigma_plus i) =
          Y.sigma_minus i * Y.sigma_plus i := by
      change star (Y.sigma_plus i) * Y.sigma_plus i = _
      rw [hAdjY i]
    rw [h 0, h 1, h 2]
  have hGaugeMinus :
      Y.sigma_minus = fun i => (u : E →L[ℂ] E) * X.sigma_minus i * (star u : E →L[ℂ] E) := by
    funext i
    rw [hAdjY i, hGauge i, star_mul, star_mul, star_star, ← hAdjX i, mul_assoc]
  have hGaugePlus :
      Y.sigma_plus = fun i => (u : E →L[ℂ] E) * X.sigma_plus i * (star u : E →L[ℂ] E) :=
    funext hGauge
  rw [hX00, hY00, hX11, hY11, hGaugeMinus, hGaugePlus]
  exact ⟨laplacian_unitary_conjugate X.sigma_minus u,
         laplacian_unitary_conjugate X.sigma_plus u⟩

end ZornPeirceDirichletGapBridge

end InfoGeometry.OperatorAlgebra.ChiralBlockSpectralGap
