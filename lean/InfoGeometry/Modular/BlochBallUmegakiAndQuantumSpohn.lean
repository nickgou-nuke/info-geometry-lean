/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
import InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Off-Diagonal Bloch-Ball Umegaki Relative Entropy & Quantum Spohn Dissipation ($\mathcal{G}_8$–$\mathcal{G}_{10}$)

This module closes the noncommutative off-diagonal $M_2(\mathbb{C})$ gap left explicitly open by
`InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants`, where `bregmanPhi` formalized only
the diagonal binary KL / longitudinal spin divergence on $\eta \in (-1, 1)$.

Reusing `InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiKernel`,
`InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetFunctionalCalculus` (`twoSheet`, `cfc_twoSheet`,
`twoSheet_isStrictlyPositive`), and the thermal GKSL semigroup `thermalSemigroupC` /
`thermalLindbladianOp` from `InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants`, this owner
proves on full self-adjoint unit-trace states $\rho \in M_2(\mathbb{C})$ inside the open Bloch ball
($\|\vec{r}(\rho)\|^2 = z^2 + 4|\rho_{01}|^2 < 1$):

* $\mathcal{G}_8$: **Exact Two-Sheet Spectral Projector & `CFC.log` Evaluation**:
  Constructs `spectralProjector ρ`, proves `IsStarProjection (spectralProjector ρ)`, derives
  $\rho = \mathrm{twoSheet}\,P\,\frac{1+r}{2}\,\frac{1-r}{2}$, `IsStrictlyPositive ρ`, and evaluates
  the genuine C*-algebraic `CFC.log ρ` and `CFC.log (gibbsDensityC θ)`.
* $\mathcal{G}_9$: **Full Noncommutative Umegaki Divergence & Coherence Pinching Pythagoras**:
  Evaluates `(Matrix.trace (umegakiKernel ρ (gibbsDensityC θ))).re` and proves
  $$D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = \big(\phi(r) - \phi(z)\big) + D_\phi(z \| \eta_\theta),$$
  with strict non-negativity of the off-diagonal coherence contribution
  `coherenceRelEntropy ρ ≥ 0` (`= 0 ↔ ρ 0 1 = 0`) and faithfulness
  `quantumUmegakiGibbs ρ θ = 0 ↔ ρ = gibbsDensityC θ`.
* $\mathcal{G}_{10}$: **Kolmogorov Forward Generator ODE, Three-Channel KMS Spohn Rate & Relaxation**:
  Proves `HasDerivAt (fun s => thermalSemigroupC γ ω θ s ρ i j) (thermalLindbladianOp γ ω θ (thermalSemigroupC γ ω θ t ρ) i j) t`,
  strict open-Bloch-ball invariance and `IsStrictlyPositive` preservation for `t ≥ 0`, the exact
  operator Spohn entropy production rate
  $$-\operatorname{Re}\operatorname{Tr}\!\big(\mathcal{L}(\sigma)(\log\sigma - \log\rho_\theta)\big)
    = \sigma_{\mathrm{KMS}}(\gamma,\theta,\sigma) \ge 0$$
  written explicitly as a sum of three positive logarithmic fluxes $(x - y)(\log x - \log y)$ with
  **strictly positive** dissipation whenever off-diagonal coherence $\sigma_{01} \ne 0$, the
  full-matrix Spohn derivative identity $\frac{d}{dt} D_{\mathrm{Umegaki}}(\rho(t) \| \rho_\theta) = -\sigma_{\mathrm{KMS}}(\rho(t))$,
  and global relaxation $\rho(t) \to \rho_\theta$, $D_{\mathrm{Umegaki}}(\rho(t) \| \rho_\theta) \to 0$.
-/

noncomputable section

open Filter _root_.Topology

namespace InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn

open InfoGeometry.Modular.GKSLGibbsAndDuallyFlatSpinCumulants
open InfoGeometry.OperatorAlgebra.NoncommutativeRenyi
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.MetaCompiler
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder

/-!
## Non-Commutativity Witnesses on $M_2(\mathbb{C})$ (OpenGauss T16)
-/

-- theorem-class: structure
/-- Closed $M_2(\mathbb{C})$ matrix non-commutativity witness. -/
theorem blochBall_matrix_noncommutative :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A := by
  refine ⟨mat2 (0 : ℂ) 1 0 0, mat2 (0 : ℂ) 0 1 0, ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
  simp only [mul2_00, mat2_00, mat2_01, mat2_10, mul_zero, add_zero, zero_add, one_mul] at h00
  exact one_ne_zero h00

-- theorem-class: structure
/-- Any nonzero off-diagonal coherence $\rho_{01} \neq 0$ fails to commute with the Gibbs state
`gibbsDensityC θ` whenever $\theta \neq 0$. -/
theorem coherent_not_commute_gibbs
    {θ : ℝ} (hθ : θ ≠ 0) {ρ : Matrix (Fin 2) (Fin 2) ℂ} (h01 : ρ 0 1 ≠ 0) :
    ρ * gibbsDensityC θ ≠ gibbsDensityC θ * ρ := by
  have h_bp_ne_bm : boltzmannPlus θ ≠ boltzmannMinus θ := by
    intro h_eq
    have h_diff : meanSpin θ = 0 := by
      rw [← (boltzmann_sum_and_diff θ).2, h_eq, sub_self]
    have h_rec := dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
    rw [h_diff] at h_rec
    dsimp [canonicalTheta] at h_rec
    norm_num at h_rec
    exact hθ h_rec.symm
  intro h_comm
  have h01_eq := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h_comm
  simp only [mul2_01, gibbsDensityC, mat2_00, mat2_01, mat2_11,
    mul_zero, add_zero, zero_mul, zero_add] at h01_eq
  have h_sub : ρ 0 1 * ((boltzmannPlus θ : ℂ) - (boltzmannMinus θ : ℂ)) = 0 := by
    linear_combination -h01_eq
  rcases mul_eq_zero.mp h_sub with h_zero | h_diff0
  · exact h01 h_zero
  · have h_diff_c : ((boltzmannPlus θ - boltzmannMinus θ : ℝ) : ℂ) = 0 := by
      push_cast; exact h_diff0
    exact h_bp_ne_bm (sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h_diff_c))

/-!
## Archetype $\mathcal{G}_8$: Bloch-Ball Spectral Projection & `CFC.log` Evaluation on $M_2(\mathbb{C})$
-/

section ArchetypeG8_BlochBallSpectralCFCLog

/-- Longitudinal Bloch coordinate $z(\rho) = \operatorname{Re}\operatorname{Tr}(\rho \Gamma_1)$. -/
def blochZ (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (Matrix.trace (ρ * pauliGamma1)).re

/-- Off-diagonal Bloch coherence squared $c(\rho) = 4|\rho_{01}|^2$. -/
def coherenceSq (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  4 * Complex.normSq (ρ 0 1)

/-- Squared Euclidean Bloch length $\|\vec{r}(\rho)\|^2 = z(\rho)^2 + 4|\rho_{01}|^2$. -/
def blochNormSq (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (blochZ ρ) ^ 2 + coherenceSq ρ

/-- Euclidean Bloch radius $r(\rho) = \sqrt{z(\rho)^2 + 4|\rho_{01}|^2}$. -/
noncomputable def blochRadius (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt (blochNormSq ρ)

/-- Spectral eigenprojector onto the $+r$ eigenspace of a self-adjoint unit-trace $2\times 2$ state,
falling back cleanly to $\mathrm{diag}(1, 0)$ at the maximally mixed state $r = 0$. -/
noncomputable def spectralProjector (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if blochRadius ρ = 0 then mat2 1 0 0 0
  else (blochRadius ρ)⁻¹ • (ρ - ((1 - blochRadius ρ) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

lemma pauliGamma1_mat2 : pauliGamma1 = mat2 (1 : ℂ) 0 0 (-1) := by
  dsimp [pauliGamma1]
  apply ext_mat2 <;>
    simp [InfoGeometry.Algebra.FiniteSpin.J_zero, Matrix.smul_apply, smul_eq_mul]

lemma blochNormSq_nonneg (ρ : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ blochNormSq ρ := by
  dsimp [blochNormSq, coherenceSq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))

lemma blochRadius_nonneg (ρ : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ blochRadius ρ :=
  Real.sqrt_nonneg _

lemma blochRadius_sq (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (blochRadius ρ) ^ 2 = blochNormSq ρ :=
  Real.sq_sqrt (blochNormSq_nonneg ρ)

lemma blochRadius_lt_one {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hb : blochNormSq ρ < 1) :
    blochRadius ρ < 1 := by
  rw [blochRadius, Real.sqrt_lt' zero_lt_one, one_pow]
  exact hb

lemma blochZ_abs_lt_one {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hb : blochNormSq ρ < 1) :
    -1 < blochZ ρ ∧ blochZ ρ < 1 := by
  have hc : 0 ≤ coherenceSq ρ := by
    dsimp [coherenceSq]; exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have hzsq : (blochZ ρ) ^ 2 < 1 := by
    dsimp [blochNormSq] at hb
    exact lt_of_le_of_lt (le_add_of_nonneg_right hc) hb
  have habs : |blochZ ρ| < 1 := by
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_lt' zero_lt_one, one_pow]
    exact hzsq
  exact abs_lt.mp habs

lemma blochRadius_pos_of_offDiag_ne {ρ : Matrix (Fin 2) (Fin 2) ℂ} (h01 : ρ 0 1 ≠ 0) :
    0 < blochRadius ρ := by
  have hns : 0 < Complex.normSq (ρ 0 1) := Complex.normSq_pos.mpr h01
  have hb_pos : 0 < blochNormSq ρ := by
    dsimp [blochNormSq, coherenceSq]
    nlinarith [sq_nonneg (blochZ ρ)]
  exact Real.sqrt_pos.mpr hb_pos

lemma trace_real_smul (c : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (c • M) = (c : ℂ) * Matrix.trace M := by
  rw [trace_fin2, trace_fin2]
  simp only [Matrix.smul_apply, Complex.real_smul]
  ring

lemma trace_one_mat2 : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
  rw [trace_fin2]; simp; norm_num

lemma trace_twoSheet_unitTrace {P : Matrix (Fin 2) (Fin 2) ℂ}
    (htrP : Matrix.trace P = 1) (a b : ℝ) :
    Matrix.trace (twoSheet P a b) = ((a + b : ℝ) : ℂ) := by
  dsimp [twoSheet]
  rw [Matrix.trace_add, trace_real_smul, trace_real_smul, Matrix.trace_sub,
    trace_one_mat2, htrP]
  push_cast; ring

lemma hermitian_unitTrace_entries {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) :
    ρ 0 0 = (((1 + blochZ ρ) / 2 : ℝ) : ℂ) ∧
    ρ 1 1 = (((1 - blochZ ρ) / 2 : ℝ) : ℂ) ∧
    ρ 1 0 = star (ρ 0 1) ∧
    Matrix.trace (ρ * pauliGamma1) = (blochZ ρ : ℂ) := by
  have hstar : star ρ = ρ := hsa.star_eq
  have h00_s : star (ρ 0 0) = ρ 0 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hstar
    simpa [Matrix.star_apply] using h
  have h11_s : star (ρ 1 1) = ρ 1 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hstar
    simpa [Matrix.star_apply] using h
  have h10_s : ρ 1 0 = star (ρ 0 1) := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hstar
    simpa [Matrix.star_apply] using h.symm
  have h00_im : (ρ 0 0).im = 0 := by
    have h := congrArg Complex.im h00_s
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have h11_im : (ρ 1 1).im = 0 := by
    have h := congrArg Complex.im h11_s
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  have h_tr_c : ρ 0 0 + ρ 1 1 = 1 := by
    rw [trace_fin2] at htr; exact htr
  have h_tr_re : (ρ 0 0).re + (ρ 1 1).re = 1 := by
    have h := congrArg Complex.re h_tr_c
    simp only [Complex.add_re, Complex.one_re] at h
    exact h
  have h_pg_c : Matrix.trace (ρ * pauliGamma1) = ρ 0 0 - ρ 1 1 := by
    rw [trace_fin2, mul2_00, mul2_11, pauliGamma1_mat2]
    simp only [mat2_00, mat2_01, mat2_10, mat2_11, mul_zero, add_zero]
    ring
  have h_bz_eq : blochZ ρ = (ρ 0 0).re - (ρ 1 1).re := by
    dsimp [blochZ]; rw [h_pg_c]; simp
  have h00_re : (ρ 0 0).re = (1 + blochZ ρ) / 2 := by linarith
  have h11_re : (ρ 1 1).re = (1 - blochZ ρ) / 2 := by linarith
  have h00 : ρ 0 0 = (((1 + blochZ ρ) / 2 : ℝ) : ℂ) :=
    Complex.ext (by simp [h00_re]) (by simp [h00_im])
  have h11 : ρ 1 1 = (((1 - blochZ ρ) / 2 : ℝ) : ℂ) :=
    Complex.ext (by simp [h11_re]) (by simp [h11_im])
  have h_pg : Matrix.trace (ρ * pauliGamma1) = (blochZ ρ : ℂ) := by
    rw [h_pg_c, h00, h11]
    push_cast; ring
  exact ⟨h00, h11, h10_s, h_pg⟩

lemma bloch_centered_sq_eq_scalar {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) :
    (ρ - (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (ρ - (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      (blochNormSq ρ / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
  have h_norm : ρ 0 1 * star (ρ 0 1) = (Complex.normSq (ρ 0 1) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have h_norm' : star (ρ 0 1) * ρ 0 1 = (Complex.normSq (ρ 0 1) : ℂ) := by
    rw [mul_comm, h_norm]
  apply ext_mat2
  · simp only [mul2_00, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      h00, h10, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte, mul_zero, mul_one, sub_zero]
    rw [h_norm]
    dsimp [blochNormSq, coherenceSq]
    push_cast; ring_nf
  · simp only [mul2_01, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      h00, h11, Fin.isValue, zero_ne_one, ↓reduceIte, mul_zero, mul_one, sub_zero]
    push_cast; ring_nf
  · simp only [mul2_10, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      h00, h11, h10, Fin.isValue, one_ne_zero, ↓reduceIte, mul_zero, mul_one, sub_zero]
    push_cast; ring_nf
  · simp only [mul2_11, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Complex.real_smul,
      h11, h10, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte, mul_zero, mul_one, sub_zero]
    rw [h_norm']
    dsimp [blochNormSq, coherenceSq]
    push_cast; ring_nf

-- theorem-class: bridge
/-- **Archetype $\mathcal{G}_8$: Bloch-Ball Two-Sheet Spectral Representation & Genuine `CFC.log`**:
For every self-adjoint unit-trace $\rho \in M_2(\mathbb{C})$ inside the open Bloch ball
`blochNormSq ρ < 1`:
1. `spectralProjector ρ` is a star projection (`IsStarProjection`) of trace `1`;
2. `twoSheet (spectralProjector ρ) ((1 + r)/2) ((1 - r)/2) = ρ`;
3. `IsStrictlyPositive ρ` holds in the ambient `CStarAlgebra`/`MatrixOrder`;
4. `CFC.log ρ = twoSheet (spectralProjector ρ) (Real.log ((1 + r)/2)) (Real.log ((1 - r)/2))`. -/
@[rep_depth operator]
theorem spectralProjector_twoSheet_and_cfc_log
    {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) :
    IsStarProjection (spectralProjector ρ) ∧
    Matrix.trace (spectralProjector ρ) = 1 ∧
    twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) = ρ ∧
    IsStrictlyPositive ρ ∧
    CFC.log ρ =
      twoSheet (spectralProjector ρ)
        (Real.log ((1 + blochRadius ρ) / 2))
        (Real.log ((1 - blochRadius ρ) / 2)) := by
  have h_decomp : IsStarProjection (spectralProjector ρ) ∧
      Matrix.trace (spectralProjector ρ) = 1 ∧
      twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) = ρ := by
    by_cases hr : blochRadius ρ = 0
    · have hbn0 : blochNormSq ρ = 0 := by
        rw [← blochRadius_sq ρ, hr]; ring
      have hc0 : coherenceSq ρ = 0 ∧ blochZ ρ = 0 := by
        have hns : 0 ≤ Complex.normSq (ρ 0 1) := Complex.normSq_nonneg _
        dsimp [blochNormSq, coherenceSq] at hbn0
        constructor
        · dsimp [coherenceSq]; nlinarith [sq_nonneg (blochZ ρ)]
        · nlinarith [sq_nonneg (blochZ ρ)]
      have h01_0 : ρ 0 1 = 0 := by
        dsimp [coherenceSq] at hc0
        exact Complex.normSq_eq_zero.mp (by linarith)
      rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
      have hρ_half : ((1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = ρ := by
        apply ext_mat2 <;>
          simp only [Matrix.smul_apply, Complex.real_smul, Matrix.one_apply,
            h00, h11, h10, hc0.2, h01_0, star_zero, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte] <;>
          push_cast <;> norm_num
      have hP_def : spectralProjector ρ = mat2 1 0 0 0 := by
        simp [spectralProjector, hr]
      rw [hP_def]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · change mat2 (1 : ℂ) 0 0 0 * mat2 1 0 0 0 = mat2 1 0 0 0
        apply ext_mat2 <;> simp [mul2_00, mul2_01, mul2_10, mul2_11]
      · change star (mat2 (1 : ℂ) 0 0 0) = mat2 1 0 0 0
        apply ext_mat2 <;> simp [Matrix.star_apply]
      · rw [trace_fin2]; simp
      · have h_half_eq : (1 + blochRadius ρ) / 2 = (1 - blochRadius ρ) / 2 := by
          rw [hr]; ring
        rw [h_half_eq, twoSheet_equal]
        have h_eq1 : (1 - blochRadius ρ) / 2 = (1 / 2 : ℝ) := by rw [hr]; ring
        rw [h_eq1, hρ_half]
    · set r := blochRadius ρ
      have hP_def : spectralProjector ρ =
          r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
        simp [spectralProjector, r, hr]
      rw [hP_def]
      have h_saP : IsSelfAdjoint
          (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
        rw [IsSelfAdjoint, star_smul, star_sub, star_smul, star_one, hsa.star_eq]
        simp only [star_trivial]
      let Δ := ρ - (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      have h_shift : ρ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
          Δ + (r / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        dsimp [Δ]
        have hs : ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
            (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
              (r / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [← sub_smul]; congr 1; ring
        rw [hs]; abel
      have h_sq_shift :
          (Δ + (r / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
            (Δ + (r / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
            r • (Δ + (r / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
        have hΔ2 : Δ * Δ = (r ^ 2 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [blochRadius_sq ρ]; exact bloch_centered_sq_eq_scalar hsa htr
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hΔ2]
        module
      have h_idemP : IsIdempotentElem
          (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
        change (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) *
            (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) = _
        rw [h_shift, smul_mul_assoc, mul_smul_comm, h_sq_shift, smul_smul, smul_smul]
        have h_scal : r⁻¹ * r⁻¹ * r = r⁻¹ := by
          rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]
        rw [h_scal]
      have h_trP : Matrix.trace
          (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) = 1 := by
        rw [trace_real_smul, Matrix.trace_sub, htr, trace_real_smul, trace_one_mat2]
        have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
        push_cast; field_simp [hr_c]; ring
      have h_recP :
          twoSheet (r⁻¹ • (ρ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)))
            ((1 + r) / 2) ((1 - r) / 2) = ρ := by
        rw [twoSheet_affine]
        have hd : (1 + r) / 2 - (1 - r) / 2 = r := by ring
        rw [hd, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel]
      exact ⟨⟨h_idemP, h_saP⟩, h_trP, h_recP⟩
  rcases h_decomp with ⟨hP, htrP, h2s⟩
  have hr_lt : blochRadius ρ < 1 := blochRadius_lt_one hb
  have hr_nn : 0 ≤ blochRadius ρ := blochRadius_nonneg ρ
  have hp_pos : 0 < (1 + blochRadius ρ) / 2 := by linarith
  have hm_pos : 0 < (1 - blochRadius ρ) / 2 := by linarith
  refine ⟨hP, htrP, h2s, ?_, ?_⟩
  · rw [← h2s]
    exact twoSheet_isStrictlyPositive hP hp_pos hm_pos
  · conv_lhs => rw [← h2s]
    rw [CFC.log, cfc_twoSheet hP]

lemma gibbsDensityC_eq_twoSheet (θ : ℝ) :
    gibbsDensityC θ = twoSheet (mat2 (1 : ℂ) 0 0 0) (boltzmannPlus θ) (boltzmannMinus θ) := by
  apply ext_mat2 <;>
    simp only [gibbsDensityC, twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, Complex.real_smul, mat2_00, mat2_01, mat2_10, mat2_11,
      Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte] <;>
    ring

-- theorem-class: bridge
/-- `gibbsDensityC θ` is strictly positive for all $\theta \in \mathbb{R}$, and its matrix
C*-logarithm equals the modular Hamiltonian operator $\theta\,\Gamma_1 - \psi(\theta)\,I_2$. -/
@[rep_depth operator]
theorem gibbsDensityC_strictlyPositive_and_cfc_log (θ : ℝ) :
    IsStrictlyPositive (gibbsDensityC θ) ∧
    CFC.log (gibbsDensityC θ) =
      (θ : ℂ) • pauliGamma1 - (cumulantPsi θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hP0 : IsStarProjection (mat2 (1 : ℂ) 0 0 0) :=
    ⟨by change mat2 (1 : ℂ) 0 0 0 * mat2 1 0 0 0 = _; apply ext_mat2 <;> simp [mul2_00, mul2_01, mul2_10, mul2_11],
     by change star (mat2 (1 : ℂ) 0 0 0) = _; apply ext_mat2 <;> simp [Matrix.star_apply]⟩
  rcases boltzmann_nonneg θ with ⟨hp_pos, hm_pos⟩
  have h_bp_log : Real.log (boltzmannPlus θ) = θ - cumulantPsi θ := by
    have hZ : partitionZ θ ≠ 0 := ne_of_gt (partitionZ_pos θ)
    have h_eq : boltzmannPlus θ = Real.exp θ / partitionZ θ := by
      dsimp [boltzmannPlus]; rw [one_add_meanSpin]; ring
    rw [h_eq, Real.log_div (ne_of_gt (Real.exp_pos θ)) hZ, Real.log_exp]; rfl
  have h_bm_log : Real.log (boltzmannMinus θ) = -θ - cumulantPsi θ := by
    have hZ : partitionZ θ ≠ 0 := ne_of_gt (partitionZ_pos θ)
    have h_eq : boltzmannMinus θ = Real.exp (-θ) / partitionZ θ := by
      dsimp [boltzmannMinus]; rw [one_sub_meanSpin]; ring
    rw [h_eq, Real.log_div (ne_of_gt (Real.exp_pos (-θ))) hZ, Real.log_exp]; rfl
  refine ⟨?_, ?_⟩
  · rw [gibbsDensityC_eq_twoSheet θ]
    exact twoSheet_isStrictlyPositive hP0 hp_pos hm_pos
  · rw [gibbsDensityC_eq_twoSheet θ, CFC.log, cfc_twoSheet hP0]
    apply ext_mat2
    · simp only [twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, smul_eq_mul, pauliGamma1_mat2,
        mat2_00, Fin.isValue, ↓reduceIte, h_bp_log, h_bm_log]
      push_cast; ring_nf
    · simp only [twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, smul_eq_mul, pauliGamma1_mat2,
        mat2_01, Fin.isValue, zero_ne_one, ↓reduceIte, h_bp_log, h_bm_log]
      push_cast; ring_nf
    · simp only [twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, smul_eq_mul, pauliGamma1_mat2,
        mat2_10, Fin.isValue, one_ne_zero, ↓reduceIte, h_bp_log, h_bm_log]
      push_cast; ring_nf
    · simp only [twoSheet, Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply,
        Matrix.smul_apply, Complex.real_smul, smul_eq_mul, pauliGamma1_mat2,
        mat2_11, Fin.isValue, ↓reduceIte, h_bp_log, h_bm_log]
      push_cast; ring_nf

end ArchetypeG8_BlochBallSpectralCFCLog

/-!
## Archetype $\mathcal{G}_9$: Exact Matrix `umegakiKernel` Trace & Coherence Pinching Pythagoras
-/

section ArchetypeG9_UmegakiKernelAndCoherencePythagoras

/-- Off-diagonal quantum coherence relative entropy
$D_{\mathrm{Umegaki}}(\rho \| \mathcal{P}_z(\rho)) = \phi(r(\rho)) - \phi(z(\rho)) \ge 0$
between $\rho$ and its $\Gamma_1$-pinched diagonal state. -/
noncomputable def coherenceRelEntropy (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  negEntropyPhi (blochRadius ρ) - negEntropyPhi (blochZ ρ)

/-- Full noncommutative Umegaki quantum relative entropy readout via
`InfoGeometry.OperatorAlgebra.NoncommutativeRenyi.umegakiKernel`:
$$D_{\mathrm{Umegaki}}(\rho \| \rho_{\mathrm{Gibbs}}(\theta)) =
  \operatorname{Re}\operatorname{Tr}\!\big(\rho\,(\log \rho - \log \rho_{\mathrm{Gibbs}}(\theta))\big).$$ -/
noncomputable def quantumUmegakiGibbs (ρ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) : ℝ :=
  (Matrix.trace (umegakiKernel ρ (gibbsDensityC θ))).re

lemma negEntropyPhi_even (η : ℝ) : negEntropyPhi (-η) = negEntropyPhi η := by
  dsimp [negEntropyPhi]
  rw [show 1 + -η = 1 - η by ring, show 1 - -η = 1 + η by ring]
  ring

lemma negEntropyPhi_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    0 ≤ negEntropyPhi b - negEntropyPhi a ∧ (negEntropyPhi b - negEntropyPhi a = 0 ↔ a = b) := by
  have ha_lo : -1 < a := by linarith [ha]
  have ha_hi : a < 1 := by linarith
  have hb_lo : -1 < b := by linarith
  have hb_pos := (bregman_umegaki_positivity_and_pythagorean_theorem.2.1 b a hb_lo hb ha_lo ha_hi)
  have h_th_nonneg : 0 ≤ canonicalTheta a := by
    dsimp [canonicalTheta]
    have h_ratio : 1 ≤ (1 + a) / (1 - a) := (one_le_div (by linarith)).mpr (by linarith)
    exact mul_nonneg (by norm_num) (Real.log_nonneg h_ratio)
  have h_breg_eq : negEntropyPhi b - negEntropyPhi a =
      bregmanPhi b a + canonicalTheta a * (b - a) := by
    dsimp [bregmanPhi]; ring
  have h_prod_nonneg : 0 ≤ canonicalTheta a * (b - a) := mul_nonneg h_th_nonneg (sub_nonneg.mpr hab)
  refine ⟨by rw [h_breg_eq]; linarith [hb_pos.1], ?_⟩
  constructor
  · intro h_zero
    have h_breg_zero : bregmanPhi b a = 0 := by rw [h_breg_eq] at h_zero; linarith [hb_pos.1]
    exact (hb_pos.2.mp h_breg_zero).symm
  · intro h_ab; subst h_ab; ring

-- theorem-class: divergence
/-- **Archetype $\mathcal{G}_9$: Exact Matrix `umegakiKernel` Trace & Coherence Pinching Pythagoras**:
For every self-adjoint unit-trace $\rho \in M_2(\mathbb{C})$ with `blochNormSq ρ < 1` and every $\theta \in \mathbb{R}$:
1. Exact complex matrix trace of `umegakiKernel ρ (gibbsDensityC θ)`:
   $\operatorname{Tr}(\rho(\log\rho - \log\rho_\theta)) = \phi(r(\rho)) + \psi(\theta) - \theta\,z(\rho)$;
2. Coherence-population pinching Pythagorean identity:
   $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = (\phi(r(\rho)) - \phi(z(\rho))) + D_\phi(z(\rho) \| \eta_\theta)$;
3. Coherence relative entropy is strictly non-negative and vanishes iff $\rho_{01} = 0$;
4. Full noncommutative Umegaki relative entropy is faithful:
   $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) \ge 0$, vanishing iff $\rho = \rho_{\mathrm{Gibbs}}(\theta)$. -/
@[rep_depth thermo]
theorem umegakiKernel_trace_and_coherence_pythagoras
    {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) (θ : ℝ) :
    Matrix.trace (umegakiKernel ρ (gibbsDensityC θ)) =
      ((negEntropyPhi (blochRadius ρ) + cumulantPsi θ - θ * blochZ ρ : ℝ) : ℂ) ∧
    quantumUmegakiGibbs ρ θ = coherenceRelEntropy ρ + bregmanPhi (blochZ ρ) (meanSpin θ) ∧
    (0 ≤ coherenceRelEntropy ρ ∧ (coherenceRelEntropy ρ = 0 ↔ ρ 0 1 = 0)) ∧
    (0 ≤ quantumUmegakiGibbs ρ θ ∧ (quantumUmegakiGibbs ρ θ = 0 ↔ ρ = gibbsDensityC θ)) := by
  rcases spectralProjector_twoSheet_and_cfc_log hsa htr hb with ⟨hP, htrP, h2s, _, hlogρ⟩
  rcases gibbsDensityC_strictlyPositive_and_cfc_log θ with ⟨_, hlogG⟩
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, hpg⟩
  have h_umegaki_eq : umegakiKernel ρ (gibbsDensityC θ) =
      ρ * CFC.log ρ - ρ * CFC.log (gibbsDensityC θ) := by
    rw [umegakiKernel_apply, CFC.log, CFC.log, mul_sub]
  have h_tr_ρlogρ : Matrix.trace (ρ * CFC.log ρ) = ((negEntropyPhi (blochRadius ρ) : ℝ) : ℂ) := by
    have h_mul : ρ * CFC.log ρ =
        twoSheet (spectralProjector ρ)
          (((1 + blochRadius ρ) / 2) * Real.log ((1 + blochRadius ρ) / 2))
          (((1 - blochRadius ρ) / 2) * Real.log ((1 - blochRadius ρ) / 2)) := by
      calc ρ * CFC.log ρ
        _ = twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) *
              twoSheet (spectralProjector ρ) (Real.log ((1 + blochRadius ρ) / 2))
                (Real.log ((1 - blochRadius ρ) / 2)) := by rw [h2s, hlogρ]
        _ = _ := twoSheet_mul (spectralProjector ρ) hP.isIdempotentElem.eq _ _ _ _
    rw [h_mul, trace_twoSheet_unitTrace htrP]
    rfl
  have h_tr_ρlogG : Matrix.trace (ρ * CFC.log (gibbsDensityC θ)) =
      ((θ * blochZ ρ - cumulantPsi θ : ℝ) : ℂ) := by
    rw [hlogG, mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, hpg,
      Matrix.mul_smul, Matrix.trace_smul, mul_one, htr, smul_eq_mul, smul_eq_mul]
    push_cast; ring
  have h_tr_tot : Matrix.trace (umegakiKernel ρ (gibbsDensityC θ)) =
      ((negEntropyPhi (blochRadius ρ) + cumulantPsi θ - θ * blochZ ρ : ℝ) : ℂ) := by
    rw [h_umegaki_eq, Matrix.trace_sub, h_tr_ρlogρ, h_tr_ρlogG]
    push_cast; ring
  have h_breg_z : bregmanPhi (blochZ ρ) (meanSpin θ) =
      negEntropyPhi (blochZ ρ) + cumulantPsi θ - θ * blochZ ρ := by
    have h_th : canonicalTheta (meanSpin θ) = θ :=
      dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
    have h_fy : cumulantPsi θ + negEntropyPhi (meanSpin θ) = θ * meanSpin θ :=
      dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 θ
    dsimp [bregmanPhi]
    rw [h_th]; linarith
  have h_pyth : quantumUmegakiGibbs ρ θ = coherenceRelEntropy ρ + bregmanPhi (blochZ ρ) (meanSpin θ) := by
    rw [quantumUmegakiGibbs, h_tr_tot, Complex.ofReal_re]
    dsimp [coherenceRelEntropy]
    linarith
  have h_coh : 0 ≤ coherenceRelEntropy ρ ∧ (coherenceRelEntropy ρ = 0 ↔ ρ 0 1 = 0) := by
    have h_abs_le_r : |blochZ ρ| ≤ blochRadius ρ := by
      have hsq : |blochZ ρ| ^ 2 ≤ (blochRadius ρ) ^ 2 := by
        rw [sq_abs, blochRadius_sq]
        dsimp [blochNormSq, coherenceSq]
        linarith [Complex.normSq_nonneg (ρ 0 1)]
      nlinarith [abs_nonneg (blochZ ρ), blochRadius_nonneg ρ]
    have h_mono := negEntropyPhi_mono_nonneg (abs_nonneg (blochZ ρ)) h_abs_le_r (blochRadius_lt_one hb)
    have h_phi_abs : negEntropyPhi |blochZ ρ| = negEntropyPhi (blochZ ρ) := by
      rcases le_total 0 (blochZ ρ) with hz_nn | hz_np
      · rw [abs_of_nonneg hz_nn]
      · rw [abs_of_nonpos hz_np, negEntropyPhi_even]
    have h_coh_eq : coherenceRelEntropy ρ = negEntropyPhi (blochRadius ρ) - negEntropyPhi |blochZ ρ| := by
      dsimp [coherenceRelEntropy]; rw [h_phi_abs]
    rw [h_coh_eq]
    refine ⟨h_mono.1, ?_⟩
    rw [h_mono.2]
    constructor
    · intro h_eq
      have hsq : (blochZ ρ) ^ 2 = (blochRadius ρ) ^ 2 := by rw [← h_eq, sq_abs]
      rw [blochRadius_sq] at hsq
      dsimp [blochNormSq, coherenceSq] at hsq
      have hns0 : Complex.normSq (ρ 0 1) = 0 := by linarith
      exact Complex.normSq_eq_zero.mp hns0
    · intro h01_0
      have hbn : blochNormSq ρ = (blochZ ρ) ^ 2 := by
        dsimp [blochNormSq, coherenceSq]; simp [h01_0]
      dsimp [blochRadius]; rw [hbn, Real.sqrt_sq_eq_abs]
  have hz_bounds := blochZ_abs_lt_one hb
  have hm_bounds := meanSpin_mem_Ioo θ
  have h_breg_pos :=
    bregman_umegaki_positivity_and_pythagorean_theorem.2.1
      (blochZ ρ) (meanSpin θ) hz_bounds.1 hz_bounds.2 hm_bounds.1 hm_bounds.2
  have h_faith : 0 ≤ quantumUmegakiGibbs ρ θ ∧ (quantumUmegakiGibbs ρ θ = 0 ↔ ρ = gibbsDensityC θ) := by
    rw [h_pyth]
    refine ⟨by linarith [h_coh.1, h_breg_pos.1], ?_⟩
    constructor
    · intro h_sum0
      have h_coh0 : coherenceRelEntropy ρ = 0 := by linarith [h_coh.1, h_breg_pos.1]
      have h_breg0 : bregmanPhi (blochZ ρ) (meanSpin θ) = 0 := by linarith [h_coh.1, h_breg_pos.1]
      have h01_0 : ρ 0 1 = 0 := h_coh.2.mp h_coh0
      have hz_eq : blochZ ρ = meanSpin θ := h_breg_pos.2.mp h_breg0
      apply ext_mat2
      · rw [h00, hz_eq]; rfl
      · rw [h01_0]; rfl
      · rw [h10, h01_0, star_zero]; rfl
      · rw [h11, hz_eq]; rfl
    · intro h_eq
      subst h_eq
      have hz_gibbs : blochZ (gibbsDensityC θ) = meanSpin θ := by
        have h_tr_gibbs : Matrix.trace (gibbsDensityC θ * pauliGamma1) = (meanSpin θ : ℂ) := by
          rw [trace_fin2, mul2_00, mul2_11, gibbsDensityC, pauliGamma1_mat2]
          simp only [mat2_00, mat2_01, mat2_10, mat2_11, mul_zero, add_zero]
          dsimp [boltzmannPlus, boltzmannMinus]
          push_cast; ring
        dsimp [blochZ]; rw [h_tr_gibbs]; simp
      have h01_gibbs : gibbsDensityC θ 0 1 = 0 := rfl
      rw [h_coh.2.mpr h01_gibbs, h_breg_pos.2.mpr hz_gibbs]; ring
  exact ⟨h_tr_tot, h_pyth, h_coh, h_faith⟩

end ArchetypeG9_UmegakiKernelAndCoherencePythagoras

/-!
## Archetype $\mathcal{G}_{10}$: Kolmogorov Forward ODE, Three-Channel KMS Spohn Dissipation & Relaxation
-/

section ArchetypeG10_KolmogorovODEAndQuantumSpohn

private lemma thermalLindbladianC_00 (γ ω θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalLindbladianC γ ω θ ρ 0 0 =
      -(rateMinus γ θ : ℂ) * ρ 0 0 + (ratePlus γ θ : ℂ) * ρ 1 1 := rfl

private lemma thermalLindbladianC_01 (γ ω θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalLindbladianC γ ω θ ρ 0 1 =
      -(((γ / 2 : ℝ) : ℂ) + Complex.I * (ω : ℂ)) * ρ 0 1 := rfl

private lemma thermalLindbladianC_10 (γ ω θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalLindbladianC γ ω θ ρ 1 0 =
      -(((γ / 2 : ℝ) : ℂ) - Complex.I * (ω : ℂ)) * ρ 1 0 := rfl

private lemma thermalLindbladianC_11 (γ ω θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalLindbladianC γ ω θ ρ 1 1 =
      (rateMinus γ θ : ℂ) * ρ 0 0 - (ratePlus γ θ : ℂ) * ρ 1 1 := rfl

private lemma thermalSemigroupC_00 (γ ω θ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalSemigroupC γ ω θ t ρ 0 0 =
      (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
        (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := rfl

private lemma thermalSemigroupC_01 (γ ω θ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalSemigroupC γ ω θ t ρ 0 1 =
      (Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ)) * ρ 0 1 := rfl

private lemma thermalSemigroupC_10 (γ ω θ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalSemigroupC γ ω θ t ρ 1 0 =
      (Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) * ρ 1 0 := rfl

private lemma thermalSemigroupC_11 (γ ω θ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalSemigroupC γ ω θ t ρ 1 1 =
      (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
        (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)) := rfl

-- theorem-class: conservation
/-- **Kolmogorov Forward Generator ODE on $M_2(\mathbb{C})$**:
Every matrix entry $(i, j)$ of $T_t(\rho)$ satisfies $\frac{d}{dt} T_t(\rho)_{ij} = (\mathcal{L}_{\gamma,\omega,\theta}(T_t(\rho)))_{ij}$
using the operator-algebraic Witt CAR generator `thermalLindbladianOp`. -/
@[rep_depth transport]
theorem hasDerivAt_thermalSemigroupC_eq_lindbladian
    (γ ω θ t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    HasDerivAt (fun s => thermalSemigroupC γ ω θ s ρ i j)
      (thermalLindbladianOp γ ω θ (thermalSemigroupC γ ω θ t ρ) i j) t := by
  rw [thermalLindbladianOp_eq_thermalLindbladianC]
  have hd_id : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
  have hd_id_c : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := hd_id.ofReal_comp
  have hd_epop : HasDerivAt (fun s : ℝ => (Real.exp (-γ * s) : ℂ))
      ((-γ * Real.exp (-γ * t) : ℝ) : ℂ) t := by
    have hd_lin : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
      simpa using hd_id.const_mul (-γ)
    have hr : HasDerivAt (fun s : ℝ => Real.exp (-γ * s)) (Real.exp (-γ * t) * (-γ)) t :=
      (Real.hasDerivAt_exp (-γ * t)).comp t hd_lin
    exact (hr.congr_deriv (by ring_nf)).ofReal_comp
  have hd_ecoh : HasDerivAt (fun s : ℝ => (Real.exp (-(γ / 2) * s) : ℂ))
      ((-(γ / 2) * Real.exp (-(γ / 2) * t) : ℝ) : ℂ) t := by
    have hd_lin : HasDerivAt (fun s : ℝ => -(γ / 2) * s) (-(γ / 2)) t := by
      simpa using hd_id.const_mul (-(γ / 2))
    have hr : HasDerivAt (fun s : ℝ => Real.exp (-(γ / 2) * s))
        (Real.exp (-(γ / 2) * t) * (-(γ / 2))) t :=
      (Real.hasDerivAt_exp (-(γ / 2) * t)).comp t hd_lin
    exact (hr.congr_deriv (by ring_nf)).ofReal_comp
  have hd_php : HasDerivAt (fun s : ℝ => Complex.exp (-Complex.I * (ω : ℂ) * (s : ℂ)))
      (-Complex.I * (ω : ℂ) * Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ))) t := by
    have h_arg : HasDerivAt (fun s : ℝ => -Complex.I * (ω : ℂ) * (s : ℂ))
        (-Complex.I * (ω : ℂ)) t := by
      simpa using hd_id_c.const_mul (-Complex.I * (ω : ℂ))
    exact ((Complex.hasDerivAt_exp _).comp t h_arg).congr_deriv (by ring_nf)
  have hd_phm : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ)))
      (Complex.I * (ω : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) t := by
    have h_arg : HasDerivAt (fun s : ℝ => Complex.I * (ω : ℂ) * (s : ℂ))
        (Complex.I * (ω : ℂ)) t := by
      simpa using hd_id_c.const_mul (Complex.I * (ω : ℂ))
    exact ((Complex.hasDerivAt_exp _).comp t h_arg).congr_deriv (by ring_nf)
  fin_cases i <;> fin_cases j
  · have hd00 := (hasDerivAt_const t ((boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1))).fun_add
      (hd_epop.mul_const (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
    refine hd00.congr_deriv ?_
    trans (-(rateMinus γ θ : ℂ) * ((boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1))) +
        (ratePlus γ θ : ℂ) * ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1))))
    · dsimp [ratePlus, rateMinus, boltzmannPlus, boltzmannMinus]; push_cast; ring_nf
    · rfl
  · have hd01 := (hd_ecoh.fun_mul hd_php).mul_const (ρ 0 1)
    refine hd01.congr_deriv ?_
    trans (-(((γ / 2 : ℝ) : ℂ) + Complex.I * (ω : ℂ)) *
        ((Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ)) * ρ 0 1))
    · push_cast; ring_nf
    · rfl
  · have hd10 := (hd_ecoh.fun_mul hd_phm).mul_const (ρ 1 0)
    refine hd10.congr_deriv ?_
    trans (-(((γ / 2 : ℝ) : ℂ) - Complex.I * (ω : ℂ)) *
        ((Real.exp (-(γ / 2) * t) : ℂ) * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) * ρ 1 0))
    · push_cast; ring_nf
    · rfl
  · have hd11 := (hasDerivAt_const t ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1))).fun_add
      (hd_epop.mul_const (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
    refine hd11.congr_deriv ?_
    trans ((rateMinus γ θ : ℂ) * ((boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1))) -
        (ratePlus γ θ : ℂ) * ((boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * t) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1))))
    · dsimp [ratePlus, rateMinus, boltzmannPlus, boltzmannMinus]; push_cast; ring_nf
    · rfl

lemma thermalSemigroupC_selfAdjoint_trace_coherence
    (γ ω θ t : ℝ) {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) :
    IsSelfAdjoint (thermalSemigroupC γ ω θ t ρ) ∧
    Matrix.trace (thermalSemigroupC γ ω θ t ρ) = 1 ∧
    blochZ (thermalSemigroupC γ ω θ t ρ) = etaTraj γ θ (blochZ ρ) t ∧
    coherenceSq (thermalSemigroupC γ ω θ t ρ) = Real.exp (-γ * t) * coherenceSq ρ := by
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
  have htr_c : ρ 0 0 + ρ 1 1 = 1 := by rw [trace_fin2] at htr; exact htr
  have h_star_php : star (Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ))) =
      Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1; simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have h_star_phm : star (Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) =
      Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ)) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1; simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have h_star_real : ∀ r : ℝ, star (r : ℂ) = (r : ℂ) := fun r => by
    simp [Complex.conj_ofReal]
  have h_sa_t : IsSelfAdjoint (thermalSemigroupC γ ω θ t ρ) := by
    change star (thermalSemigroupC γ ω θ t ρ) = thermalSemigroupC γ ω θ t ρ
    apply ext_mat2 <;>
      simp only [Matrix.star_apply, thermalSemigroupC_00, thermalSemigroupC_01,
        thermalSemigroupC_10, thermalSemigroupC_11, star_add, star_sub, star_mul,
        h_star_real, h00, h11, h10, star_star, h_star_php, h_star_phm] <;>
      ring
  have h_tr_t : Matrix.trace (thermalSemigroupC γ ω θ t ρ) = 1 := by
    rw [trace_fin2, thermalSemigroupC_00, thermalSemigroupC_11, htr_c, mul_one, mul_one]
    have h_bsum : (boltzmannPlus θ : ℂ) + (boltzmannMinus θ : ℂ) = 1 :=
      by exact_mod_cast (boltzmann_sum_and_diff θ).1
    linear_combination (1 - (Real.exp (-γ * t) : ℂ)) * h_bsum +
      (Real.exp (-γ * t) : ℂ) * htr_c
  have h_bz_t : blochZ (thermalSemigroupC γ ω θ t ρ) = etaTraj γ θ (blochZ ρ) t := by
    dsimp [blochZ]
    exact spinReadout_thermalSemigroupC_eq_etaTraj γ ω θ t ρ htr
  have h_coh_t : coherenceSq (thermalSemigroupC γ ω θ t ρ) = Real.exp (-γ * t) * coherenceSq ρ := by
    rw [coherenceSq, thermalSemigroupC_01, coherenceSq]
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
    have h_exp2 : Real.exp (-(γ / 2) * t) * Real.exp (-(γ / 2) * t) = Real.exp (-γ * t) := by
      rw [← Real.exp_add]; congr 1; ring
    have h_norm1 : Complex.normSq (Complex.exp (-Complex.I * (ω : ℂ) * (t : ℂ))) = 1 := by
      have h_arg : -Complex.I * (ω : ℂ) * (t : ℂ) = ((-ω * t : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [Complex.normSq_eq_norm_sq, h_arg, Complex.norm_exp_ofReal_mul_I]; norm_num
    rw [h_exp2, h_norm1]; ring
  exact ⟨h_sa_t, h_tr_t, h_bz_t, h_coh_t⟩

-- theorem-class: conservation
/-- For every $\gamma > 0$ and $t \ge 0$, the Witt CAR thermal semigroup preserves self-adjointness,
unit trace, and strict open-Bloch-ball interior membership ($\|\vec{r}\|^2 < 1$ and `IsStrictlyPositive`),
while contracting off-diagonal coherence exponentially as $e^{-\gamma t} c_0$. -/
@[rep_depth transport]
theorem thermalSemigroupC_preserves_blochBall
    {γ ω θ t : ℝ} {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hγ : 0 < γ) (ht : 0 ≤ t) (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1)
    (hb : blochNormSq ρ < 1) :
    IsSelfAdjoint (thermalSemigroupC γ ω θ t ρ) ∧
    Matrix.trace (thermalSemigroupC γ ω θ t ρ) = 1 ∧
    coherenceSq (thermalSemigroupC γ ω θ t ρ) = Real.exp (-γ * t) * coherenceSq ρ ∧
    blochNormSq (thermalSemigroupC γ ω θ t ρ) < 1 ∧
    IsStrictlyPositive (thermalSemigroupC γ ω θ t ρ) := by
  rcases thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hsa htr with
    ⟨h_sa_t, h_tr_t, h_bz_t, h_coh_t⟩
  have h_norm_lt : blochNormSq (thermalSemigroupC γ ω θ t ρ) < 1 := by
    rw [blochNormSq, h_bz_t, h_coh_t]
    set lam := Real.exp (-γ * t)
    set z0 := blochZ ρ
    set c0 := coherenceSq ρ
    set η_eq := meanSpin θ
    have hlam_pos : 0 < lam := Real.exp_pos _
    have hlam_le1 : lam ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hγ, ht])
    have h_eta_lt : η_eq ^ 2 < 1 := by
      rcases meanSpin_mem_Ioo θ with ⟨hm_lo, hm_hi⟩
      nlinarith [hm_lo, hm_hi]
    have hc0_nn : 0 ≤ c0 := by
      dsimp [c0, coherenceSq]; exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
    have h_alg : (etaTraj γ θ z0 t) ^ 2 + lam * c0 =
        (1 - lam) * η_eq ^ 2 + lam * blochNormSq ρ - lam * (1 - lam) * (z0 - η_eq) ^ 2 := by
      dsimp [etaTraj, lam, z0, c0, η_eq, blochNormSq]; ring
    have h_drop : 0 ≤ lam * (1 - lam) * (z0 - η_eq) ^ 2 :=
      mul_nonneg (mul_nonneg (le_of_lt hlam_pos) (sub_nonneg.mpr hlam_le1)) (sq_nonneg _)
    rw [h_alg]
    nlinarith [hb, h_eta_lt, h_drop, hlam_pos, hlam_le1]
  have h_pos_t := (spectralProjector_twoSheet_and_cfc_log h_sa_t h_tr_t h_norm_lt).2.2.2.1
  exact ⟨h_sa_t, h_tr_t, h_coh_t, h_norm_lt, h_pos_t⟩

/-- Elementary positive logarithmic flux $(x - y)(\log x - \log y) \ge 0$ for $x, y > 0$. -/
noncomputable def logFlux (x y : ℝ) : ℝ :=
  (x - y) * (Real.log x - Real.log y)

lemma logFlux_nonneg_and_eq_zero_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ logFlux x y ∧ (logFlux x y = 0 ↔ x = y) := by
  dsimp [logFlux]
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hlog : Real.log x < Real.log y := Real.log_lt_log hx hxy
    have hpos : 0 < (x - y) * (Real.log x - Real.log y) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr hxy) (sub_neg.mpr hlog)
    exact ⟨le_of_lt hpos, ⟨fun h0 => absurd h0 (ne_of_gt hpos), fun h => absurd h (ne_of_lt hxy)⟩⟩
  · simp
  · have hlog : Real.log y < Real.log x := Real.log_lt_log hy hyx
    have hpos : 0 < (x - y) * (Real.log x - Real.log y) :=
      mul_pos (sub_pos.mpr hyx) (sub_pos.mpr hlog)
    exact ⟨le_of_lt hpos, ⟨fun h0 => absurd h0 (ne_of_gt hpos), fun h => absurd h (ne_of_gt hyx)⟩⟩

/-- Three-channel KMS Spohn entropy production rate $\sigma_{\mathrm{KMS}}(\gamma,\theta,\sigma) \ge 0$
in the instantaneous eigenbasis of a Bloch state $\sigma$ with $0 < r(\sigma) < 1$. -/
noncomputable def quantumSpohnRate (γ θ : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  let r := blochRadius σ
  let z := blochZ σ
  let q := (r + z) / (2 * r)
  let lp := (1 + r) / 2
  let lm := (1 - r) / 2
  let pp := boltzmannPlus θ
  let pm := boltzmannMinus θ
  γ * (q ^ 2 * logFlux (lp * pm) (lm * pp) +
       (1 - q) ^ 2 * logFlux (lp * pp) (lm * pm) +
       q * (1 - q) * logFlux pp pm)

/-- Bloch-coordinate Jeffreys term for a faithful qubit state and the diagonal Gibbs state.
The `r² - z η` term includes transverse coherence through `r² = z² + coherenceSq`. -/
noncomputable def blochJeffreysTerm (θ : ℝ) (σ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  let r := blochRadius σ
  let z := blochZ σ
  (canonicalTheta r / r) * (r ^ 2 - z * meanSpin θ) - θ * (z - meanSpin θ)

-- theorem-class: conservation
/-- **Operator-Level Three-Channel KMS Spohn Rate & Strict Coherent Dissipation**:
For any $\gamma > 0$, $\omega \in \mathbb{R}$, $\theta \in \mathbb{R}$, and self-adjoint unit-trace
$\sigma \in M_2(\mathbb{C})$ with $0 < r(\sigma)$ and `blochNormSq σ < 1`:
1. Exact operator identity:
   $-\operatorname{Re}\operatorname{Tr}(\mathcal{L}_{\gamma,\omega,\theta}(\sigma)(\log\sigma - \log\rho_\theta)) = \sigma_{\mathrm{KMS}}(\gamma,\theta,\sigma)$;
2. Closed Bloch-coordinate formula:
   $\sigma_{\mathrm{KMS}}(\gamma,\theta,\sigma) = \gamma\left(\frac{\theta(r)}{2r}(r^2 + z^2 - 2z\eta_\theta) - \theta(z - \eta_\theta)\right)$;
3. Non-negativity: $\sigma_{\mathrm{KMS}}(\gamma,\theta,\sigma) \ge 0$;
4. **Strictly positive noncommutative coherence dissipation**: if $\sigma_{01} \ne 0$, then
   $\sigma_{\mathrm{KMS}}(\gamma,\theta,\sigma) > 0$. -/
@[rep_depth thermo, capstone]
theorem operator_spohn_rate_and_strict_coherent_dissipation
    {γ ω θ : ℝ} {σ : Matrix (Fin 2) (Fin 2) ℂ}
    (hγ : 0 < γ) (hsa : IsSelfAdjoint σ) (htr : Matrix.trace σ = 1)
    (hr_pos : 0 < blochRadius σ) (hb : blochNormSq σ < 1) :
    -(Matrix.trace (thermalLindbladianOp γ ω θ σ *
        (CFC.log σ - CFC.log (gibbsDensityC θ)))).re = quantumSpohnRate γ θ σ ∧
    quantumSpohnRate γ θ σ =
      γ * ((canonicalTheta (blochRadius σ) / (2 * blochRadius σ)) *
          ((blochRadius σ) ^ 2 + (blochZ σ) ^ 2 - 2 * blochZ σ * meanSpin θ) -
        θ * (blochZ σ - meanSpin θ)) ∧
    0 ≤ quantumSpohnRate γ θ σ ∧
    (σ 0 1 ≠ 0 → 0 < quantumSpohnRate γ θ σ) := by
  set r := blochRadius σ
  set z := blochZ σ
  set η_eq := meanSpin θ
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_lt : r < 1 := blochRadius_lt_one hb
  have hlp_pos : 0 < (1 + r) / 2 := by linarith
  have hlm_pos : 0 < (1 - r) / 2 := by linarith
  rcases boltzmann_nonneg θ with ⟨hpp_pos, hpm_pos⟩
  have h_log_r : Real.log ((1 + r) / 2) - Real.log ((1 - r) / 2) = 2 * canonicalTheta r := by
    rw [← Real.log_div (ne_of_gt hlp_pos) (ne_of_gt hlm_pos)]
    have h_div : ((1 + r) / 2) / ((1 - r) / 2) = (1 + r) / (1 - r) := by field_simp
    rw [h_div]; dsimp [canonicalTheta]; ring
  have h_log_th : Real.log (boltzmannPlus θ) - Real.log (boltzmannMinus θ) = 2 * θ := by
    have h_ratio : boltzmannPlus θ / boltzmannMinus θ = (1 + η_eq) / (1 - η_eq) := by
      dsimp [boltzmannPlus, boltzmannMinus, η_eq]; field_simp
    rw [← Real.log_div (ne_of_gt hpp_pos) (ne_of_gt hpm_pos), h_ratio]
    have h_rec := dually_flat_legendre_reciprocity_and_metric_inversion.1 θ
    dsimp [canonicalTheta] at h_rec
    linarith [h_rec]
  have h_spohn_alg :
      quantumSpohnRate γ θ σ =
        γ * ((canonicalTheta r / (2 * r)) * (r ^ 2 + z ^ 2 - 2 * z * η_eq) - θ * (z - η_eq)) := by
    dsimp [quantumSpohnRate, logFlux]
    change γ * (((r + z) / (2 * r)) ^ 2 *
        (((1 + r) / 2 * boltzmannMinus θ - (1 - r) / 2 * boltzmannPlus θ) *
          (Real.log ((1 + r) / 2 * boltzmannMinus θ) -
            Real.log ((1 - r) / 2 * boltzmannPlus θ))) +
      (1 - (r + z) / (2 * r)) ^ 2 *
        (((1 + r) / 2 * boltzmannPlus θ - (1 - r) / 2 * boltzmannMinus θ) *
          (Real.log ((1 + r) / 2 * boltzmannPlus θ) -
            Real.log ((1 - r) / 2 * boltzmannMinus θ))) +
      ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) *
        ((boltzmannPlus θ - boltzmannMinus θ) *
          (Real.log (boltzmannPlus θ) - Real.log (boltzmannMinus θ)))) = _
    rw [Real.log_mul (ne_of_gt hlp_pos) (ne_of_gt hpm_pos),
      Real.log_mul (ne_of_gt hlm_pos) (ne_of_gt hpp_pos),
      Real.log_mul (ne_of_gt hlp_pos) (ne_of_gt hpp_pos),
      Real.log_mul (ne_of_gt hlm_pos) (ne_of_gt hpm_pos)]
    have h1 : Real.log ((1 + r) / 2) + Real.log (boltzmannMinus θ) -
        (Real.log ((1 - r) / 2) + Real.log (boltzmannPlus θ)) = 2 * canonicalTheta r - 2 * θ := by
      linarith [h_log_r, h_log_th]
    have h2 : Real.log ((1 + r) / 2) + Real.log (boltzmannPlus θ) -
        (Real.log ((1 - r) / 2) + Real.log (boltzmannMinus θ)) = 2 * canonicalTheta r + 2 * θ := by
      linarith [h_log_r, h_log_th]
    rw [h1, h2, h_log_th]
    dsimp [boltzmannPlus, boltzmannMinus, η_eq]
    field_simp [hr_ne]; ring
  rcases spectralProjector_twoSheet_and_cfc_log hsa htr hb with ⟨_, _, _, _, hlogσ⟩
  rcases gibbsDensityC_strictlyPositive_and_cfc_log θ with ⟨_, hlogG⟩
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
  have hP_def : spectralProjector σ =
      r⁻¹ • (σ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simp [spectralProjector, r, hr_ne]
  have h_logσ_alg : CFC.log σ =
      (((Real.log ((1 + r) / 2) + Real.log ((1 - r) / 2)) / 2 - canonicalTheta r / r : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((2 * canonicalTheta r / r : ℝ) : ℂ) • σ := by
    have hlogσ' : CFC.log σ =
        twoSheet (spectralProjector σ) (Real.log ((1 + r) / 2)) (Real.log ((1 - r) / 2)) := hlogσ
    have h_lp_eq : Real.log ((1 + r) / 2) = Real.log ((1 - r) / 2) + 2 * canonicalTheta r := by
      linarith [h_log_r]
    have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_ne
    rw [hlogσ', hP_def, twoSheet_affine, h_log_r, h_lp_eq]
    apply ext_mat2 <;>
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Complex.real_smul, smul_eq_mul, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte] <;>
      push_cast <;> field_simp [hr_c] <;> ring
  have h_tr_L : Matrix.trace (thermalLindbladianOp γ ω θ σ) = 0 := by
    rw [thermalLindbladianOp_eq_thermalLindbladianC, trace_fin2,
      thermalLindbladianC_00, thermalLindbladianC_11]
    ring
  have h_tr_L_σ : Matrix.trace (thermalLindbladianOp γ ω θ σ * σ) =
      -((γ / 4 * (r ^ 2 + z ^ 2 - 2 * z * η_eq) : ℝ) : ℂ) := by
    rw [thermalLindbladianOp_eq_thermalLindbladianC, trace_fin2, mul2_00, mul2_11,
      thermalLindbladianC_00, thermalLindbladianC_01, thermalLindbladianC_10,
      thermalLindbladianC_11]
    have h_norm : σ 0 1 * star (σ 0 1) = (Complex.normSq (σ 0 1) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj]
    have hc_eq : (4 : ℂ) * (σ 0 1 * star (σ 0 1)) = ((r ^ 2 - z ^ 2 : ℝ) : ℂ) := by
      rw [h_norm]
      have hc_r : 4 * Complex.normSq (σ 0 1) = r ^ 2 - z ^ 2 := by
        rw [blochRadius_sq σ]; dsimp [blochNormSq, coherenceSq, z]; ring
      exact_mod_cast hc_r
    dsimp [ratePlus, rateMinus, boltzmannPlus, boltzmannMinus, z, η_eq] at hc_eq ⊢
    rw [h00, h11, h10]
    simp only [Complex.star_def] at hc_eq ⊢
    push_cast at hc_eq ⊢
    linear_combination (-(γ : ℂ) / 4) * hc_eq
  have h_tr_L_pg : Matrix.trace (thermalLindbladianOp γ ω θ σ * pauliGamma1) =
      ((-γ * (z - η_eq) : ℝ) : ℂ) := by
    rw [thermalLindbladianOp_eq_thermalLindbladianC, trace_fin2, mul2_00, mul2_11, pauliGamma1_mat2,
      thermalLindbladianC_00, thermalLindbladianC_11]
    simp only [mat2_00, mat2_01, mat2_10, mat2_11, mul_zero, add_zero]
    dsimp [ratePlus, rateMinus, boltzmannPlus, boltzmannMinus, z, η_eq]
    rw [h00, h11]
    push_cast; ring
  have h_op_id : -(Matrix.trace (thermalLindbladianOp γ ω θ σ *
      (CFC.log σ - CFC.log (gibbsDensityC θ)))).re = quantumSpohnRate γ θ σ := by
    rw [h_spohn_alg, mul_sub, Matrix.trace_sub, h_logσ_alg, hlogG]
    rw [mul_add, Matrix.trace_add, Matrix.mul_smul, mul_one, Matrix.trace_smul, h_tr_L,
      smul_zero, zero_add, Matrix.mul_smul, Matrix.trace_smul, h_tr_L_σ, smul_eq_mul]
    rw [mul_sub (thermalLindbladianOp γ ω θ σ), Matrix.trace_sub, Matrix.mul_smul,
      Matrix.trace_smul, h_tr_L_pg, Matrix.mul_smul, mul_one, Matrix.trace_smul, h_tr_L,
      smul_zero, sub_zero, smul_eq_mul]
    have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_ne
    have h_simp_c :
        (((2 * canonicalTheta r / r : ℝ) : ℂ) * -((γ / 4 * (r ^ 2 + z ^ 2 - 2 * z * η_eq) : ℝ) : ℂ) -
          ((θ : ℂ) * ((-γ * (z - η_eq) : ℝ) : ℂ))) =
          ((-(γ * ((canonicalTheta r / (2 * r)) * (r ^ 2 + z ^ 2 - 2 * z * η_eq) -
            θ * (z - η_eq))) : ℝ) : ℂ) := by
      push_cast; field_simp [hr_c]; ring
    rw [h_simp_c, Complex.ofReal_re, neg_neg]
  have hf1 := logFlux_nonneg_and_eq_zero_iff (mul_pos hlp_pos hpm_pos) (mul_pos hlm_pos hpp_pos)
  have hf2 := logFlux_nonneg_and_eq_zero_iff (mul_pos hlp_pos hpp_pos) (mul_pos hlm_pos hpm_pos)
  have hf3 := logFlux_nonneg_and_eq_zero_iff hpp_pos hpm_pos
  have hz_sq_le : z ^ 2 ≤ r ^ 2 := by
    rw [blochRadius_sq σ]; dsimp [blochNormSq, coherenceSq, z]
    linarith [Complex.normSq_nonneg (σ 0 1)]
  have hz_bounds_r : -r ≤ z ∧ z ≤ r := by
    have hz_abs : |z| ≤ r := by nlinarith [abs_nonneg z, hr_pos, sq_abs z]
    exact abs_le.mp hz_abs
  have hq_nn : 0 ≤ (r + z) / (2 * r) :=
    div_nonneg (by linarith [hz_bounds_r.1]) (by linarith)
  have h1q_nn : 0 ≤ 1 - (r + z) / (2 * r) := by
    have : 1 - (r + z) / (2 * r) = (r - z) / (2 * r) := by field_simp [hr_ne]; ring
    rw [this]; exact div_nonneg (by linarith [hz_bounds_r.2]) (by linarith)
  have h_spohn_nonneg : 0 ≤ quantumSpohnRate γ θ σ := by
    dsimp [quantumSpohnRate]
    refine mul_nonneg (le_of_lt hγ) (add_nonneg (add_nonneg ?_ ?_) ?_)
    · exact mul_nonneg (sq_nonneg _) hf1.1
    · exact mul_nonneg (sq_nonneg _) hf2.1
    · exact mul_nonneg (mul_nonneg hq_nn h1q_nn) hf3.1
  have h_strict_coh : σ 0 1 ≠ 0 → 0 < quantumSpohnRate γ θ σ := by
    intro h01
    have hns : 0 < Complex.normSq (σ 0 1) := Complex.normSq_pos.mpr h01
    have hz_sq_lt : z ^ 2 < r ^ 2 := by
      rw [blochRadius_sq σ]; dsimp [blochNormSq, coherenceSq]; linarith
    have hz_lt_r : -r < z ∧ z < r := ⟨by nlinarith, by nlinarith⟩
    have hq_pos : 0 < (r + z) / (2 * r) := div_pos (by linarith) (by linarith)
    have h1q_pos : 0 < 1 - (r + z) / (2 * r) := by
      have : 1 - (r + z) / (2 * r) = (r - z) / (2 * r) := by field_simp [hr_ne]; ring
      rw [this]; exact div_pos (by linarith) (by linarith)
    rcases lt_or_eq_of_le h_spohn_nonneg with h_lt | h_eq
    · exact h_lt
    · exfalso
      have ht1 : ((r + z) / (2 * r)) ^ 2 * logFlux ((1 + r) / 2 * boltzmannMinus θ)
          ((1 - r) / 2 * boltzmannPlus θ) ≥ 0 := mul_nonneg (sq_nonneg _) hf1.1
      have ht2 : (1 - (r + z) / (2 * r)) ^ 2 * logFlux ((1 + r) / 2 * boltzmannPlus θ)
          ((1 - r) / 2 * boltzmannMinus θ) ≥ 0 := mul_nonneg (sq_nonneg _) hf2.1
      have ht3 : ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) *
          logFlux (boltzmannPlus θ) (boltzmannMinus θ) ≥ 0 :=
        mul_nonneg (mul_nonneg (le_of_lt hq_pos) (le_of_lt h1q_pos)) hf3.1
      have h_sum0 :
          ((r + z) / (2 * r)) ^ 2 * logFlux ((1 + r) / 2 * boltzmannMinus θ)
            ((1 - r) / 2 * boltzmannPlus θ) +
          (1 - (r + z) / (2 * r)) ^ 2 * logFlux ((1 + r) / 2 * boltzmannPlus θ)
            ((1 - r) / 2 * boltzmannMinus θ) +
          ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) *
            logFlux (boltzmannPlus θ) (boltzmannMinus θ) = 0 := by
        have hq0 : quantumSpohnRate γ θ σ = 0 := h_eq.symm
        dsimp [quantumSpohnRate] at hq0
        exact (mul_eq_zero.mp hq0).resolve_left (ne_of_gt hγ)
      have h_lf1_0 : logFlux ((1 + r) / 2 * boltzmannMinus θ) ((1 - r) / 2 * boltzmannPlus θ) = 0 :=
        (mul_eq_zero.mp (by linarith : ((r + z) / (2 * r)) ^ 2 *
          logFlux ((1 + r) / 2 * boltzmannMinus θ) ((1 - r) / 2 * boltzmannPlus θ) = 0)).resolve_left
          (pow_ne_zero 2 (ne_of_gt hq_pos))
      have h_lf2_0 : logFlux ((1 + r) / 2 * boltzmannPlus θ) ((1 - r) / 2 * boltzmannMinus θ) = 0 :=
        (mul_eq_zero.mp (by linarith : (1 - (r + z) / (2 * r)) ^ 2 *
          logFlux ((1 + r) / 2 * boltzmannPlus θ) ((1 - r) / 2 * boltzmannMinus θ) = 0)).resolve_left
          (pow_ne_zero 2 (ne_of_gt h1q_pos))
      have h_lf3_0 : logFlux (boltzmannPlus θ) (boltzmannMinus θ) = 0 :=
        (mul_eq_zero.mp (by linarith : ((r + z) / (2 * r)) * (1 - (r + z) / (2 * r)) *
          logFlux (boltzmannPlus θ) (boltzmannMinus θ) = 0)).resolve_left
          (ne_of_gt (mul_pos hq_pos h1q_pos))
      have hp_eq := hf3.2.mp h_lf3_0
      have h1_eq := hf1.2.mp h_lf1_0
      rw [hp_eq] at h1_eq
      have hr0 : r = 0 := by
        have h_cancel : ((1 + r) / 2 - (1 - r) / 2) * boltzmannMinus θ = 0 := by linarith
        have hsub : (1 + r) / 2 - (1 - r) / 2 = 0 :=
          (mul_eq_zero.mp h_cancel).resolve_right (ne_of_gt hpm_pos)
        linarith
      exact hr_ne hr0
  refine ⟨h_op_id, h_spohn_alg, h_spohn_nonneg, h_strict_coh⟩

-- theorem-class: identity
/-- The KMS Spohn rate equals the Bloch Jeffreys term minus half of the transverse coherence
contribution. This is the full-matrix correction to the one-dimensional Jeffreys formula. -/
@[rep_depth thermo]
theorem quantumSpohnRate_eq_blochJeffreys_minus_coherence
    {γ ω θ : ℝ} {σ : Matrix (Fin 2) (Fin 2) ℂ}
    (hγ : 0 < γ) (hsa : IsSelfAdjoint σ) (htr : Matrix.trace σ = 1)
    (hr_pos : 0 < blochRadius σ) (hb : blochNormSq σ < 1) :
    quantumSpohnRate γ θ σ =
      γ * (blochJeffreysTerm θ σ -
        (canonicalTheta (blochRadius σ) / (2 * blochRadius σ)) * coherenceSq σ) := by
  have h_rates := operator_spohn_rate_and_strict_coherent_dissipation
    (γ := γ) (ω := ω) (θ := θ) (σ := σ) hγ hsa htr hr_pos hb
  have h_rate := h_rates.2.1
  have h_coh : coherenceSq σ = (blochRadius σ) ^ 2 - (blochZ σ) ^ 2 := by
    rw [blochRadius_sq]
    dsimp [blochNormSq]
    ring_nf
  rw [h_rate, h_coh]
  dsimp [blochJeffreysTerm]
  have hr_ne : blochRadius σ ≠ 0 := ne_of_gt hr_pos
  field_simp [hr_ne]
  ring_nf

-- theorem-class: conservation
/-- **Master Noncommutative $M_2(\mathbb{C})$ Spohn Entropy Production & Gibbs Relaxation Law ($\mathcal{G}_{10}$)**:
For every $\gamma > 0$, $\omega \in \mathbb{R}$, $\theta \in \mathbb{R}$, and self-adjoint unit-trace
initial state $\rho \in M_2(\mathbb{C})$ in the open Bloch ball `blochNormSq ρ < 1`:
1. At every $t \ge 0$ where $r(T_t(\rho)) > 0$ (automatic for all $t \ge 0$ when $\rho_{01} \ne 0$):
   $$\frac{d}{dt} D_{\mathrm{Umegaki}}(T_t(\rho) \| \rho_\theta) = -\sigma_{\mathrm{KMS}}(\gamma,\theta,T_t(\rho)) \le 0,$$
   with **strictly negative** entropy production rate whenever $\rho_{01} \ne 0$;
2. Entrywise convergence of the full matrix trajectory: $\lim_{t \to +\infty} T_t(\rho)_{ij} = \rho_{\mathrm{Gibbs}}(\theta)_{ij}$;
3. Global noncommutative Umegaki divergence relaxation:
   $\lim_{t \to +\infty} D_{\mathrm{Umegaki}}(T_t(\rho) \| \rho_\theta) = 0$. -/
@[rep_depth thermo, capstone]
theorem master_bloch_umegaki_spohn_and_gibbs_relaxation
    {γ ω θ : ℝ} {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hγ : 0 < γ) (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) :
    (∀ t : ℝ, 0 ≤ t → 0 < blochRadius (thermalSemigroupC γ ω θ t ρ) →
      HasDerivAt (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ)
        (-quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ)) t ∧
      -quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ) ≤ 0) ∧
    (ρ 0 1 ≠ 0 → ∀ t : ℝ, 0 ≤ t →
      0 < blochRadius (thermalSemigroupC γ ω θ t ρ) ∧
      0 < quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ)) ∧
    (∀ i j : Fin 2,
      Tendsto (fun s => thermalSemigroupC γ ω θ s ρ i j) atTop (𝓝 (gibbsDensityC θ i j))) ∧
    Tendsto (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ) atTop (𝓝 0) := by
  have h_bloch_formula : ∀ s : ℝ,
      blochNormSq (thermalSemigroupC γ ω θ s ρ) =
        (etaTraj γ θ (blochZ ρ) s) ^ 2 + Real.exp (-γ * s) * coherenceSq ρ := by
    intro s
    rcases thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ s hsa htr with ⟨_, _, h_bz_s, h_coh_s⟩
    rw [blochNormSq, h_bz_s, h_coh_s]
  have h_radius_t_fun : ∀ s : ℝ,
      blochRadius (thermalSemigroupC γ ω θ s ρ) =
        Real.sqrt ((etaTraj γ θ (blochZ ρ) s) ^ 2 + Real.exp (-γ * s) * coherenceSq ρ) := by
    intro s; rw [blochRadius, h_bloch_formula s]
  have h_umegaki_formula : ∀ s : ℝ, blochNormSq (thermalSemigroupC γ ω θ s ρ) < 1 →
      quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ =
        negEntropyPhi (blochRadius (thermalSemigroupC γ ω θ s ρ)) + cumulantPsi θ -
          θ * etaTraj γ θ (blochZ ρ) s := by
    intro s hb_s
    rcases thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ s hsa htr with ⟨hsa_s, htr_s, h_bz_s, _⟩
    have h_tr_s := (umegakiKernel_trace_and_coherence_pythagoras hsa_s htr_s hb_s θ).1
    rw [quantumUmegakiGibbs, h_tr_s, Complex.ofReal_re, h_bz_s]
  have h_cont_fn : Continuous (fun s : ℝ =>
      (etaTraj γ θ (blochZ ρ) s) ^ 2 + Real.exp (-γ * s) * coherenceSq ρ) := by
    unfold etaTraj; fun_prop
  have h_ode_and_sign : ∀ t : ℝ, 0 ≤ t → 0 < blochRadius (thermalSemigroupC γ ω θ t ρ) →
      HasDerivAt (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ)
        (-quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ)) t ∧
      -quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ) ≤ 0 := by
    intro t ht hr_t_pos
    have h_pres := @thermalSemigroupC_preserves_blochBall γ ω θ t ρ hγ ht hsa htr hb
    have hsa_t := h_pres.1
    have htr_t := h_pres.2.1
    have hb_t := h_pres.2.2.2.1
    have h_spohn_t := @operator_spohn_rate_and_strict_coherent_dissipation γ ω θ
      (thermalSemigroupC γ ω θ t ρ) hγ hsa_t htr_t hr_t_pos hb_t
    set f : ℝ → ℝ := fun s => (etaTraj γ θ (blochZ ρ) s) ^ 2 + Real.exp (-γ * s) * coherenceSq ρ
    have hf_lt1 : f t < 1 := by simpa [f, h_bloch_formula t] using hb_t
    have hf_pos : 0 < f t := by
      change 0 < (etaTraj γ θ (blochZ ρ) t) ^ 2 + Real.exp (-γ * t) * coherenceSq ρ
      rw [← h_bloch_formula t, ← blochRadius_sq]
      exact sq_pos_of_pos hr_t_pos
    have h_ev : ∀ᶠ s in 𝓝 t,
        quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ =
          negEntropyPhi (Real.sqrt (f s)) + cumulantPsi θ - θ * etaTraj γ θ (blochZ ρ) s := by
      have h_lt_ev : ∀ᶠ s in 𝓝 t, f s < 1 := h_cont_fn.continuousAt.eventually_lt continuousAt_const hf_lt1
      filter_upwards [h_lt_ev] with s hs_lt
      have hb_s : blochNormSq (thermalSemigroupC γ ω θ s ρ) < 1 := by rwa [h_bloch_formula s]
      rw [h_umegaki_formula s hb_s, h_radius_t_fun s]
    have hd_eta : HasDerivAt (etaTraj γ θ (blochZ ρ))
        (-γ * (etaTraj γ θ (blochZ ρ) t - meanSpin θ)) t := by
      have hd_lin : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
        simpa using (hasDerivAt_id t).const_mul (-γ)
      have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-γ * s)) (Real.exp (-γ * t) * (-γ)) t :=
        (Real.hasDerivAt_exp (-γ * t)).comp t hd_lin
      have h_mul := (hasDerivAt_const t (meanSpin θ)).fun_add
        (h_exp.mul_const (blochZ ρ - meanSpin θ))
      unfold etaTraj
      exact h_mul.congr_deriv (by ring_nf)
    have hd_exp_c : HasDerivAt (fun s : ℝ => Real.exp (-γ * s) * coherenceSq ρ)
        (-γ * coherenceSq (thermalSemigroupC γ ω θ t ρ)) t := by
      have hd_lin : HasDerivAt (fun s : ℝ => -γ * s) (-γ) t := by
        simpa using (hasDerivAt_id t).const_mul (-γ)
      have h_exp : HasDerivAt (fun s : ℝ => Real.exp (-γ * s)) (Real.exp (-γ * t) * (-γ)) t :=
        (Real.hasDerivAt_exp (-γ * t)).comp t hd_lin
      have hc_t := h_pres.2.2.1
      exact (h_exp.mul_const (coherenceSq ρ)).congr_deriv (by rw [hc_t]; ring_nf)
    have hd_f : HasDerivAt f
        (-γ * ((blochRadius (thermalSemigroupC γ ω θ t ρ)) ^ 2 +
          (blochZ (thermalSemigroupC γ ω θ t ρ)) ^ 2 -
          2 * blochZ (thermalSemigroupC γ ω θ t ρ) * meanSpin θ)) t := by
      have h_sq_eta := hd_eta.pow 2
      have hd_sum := h_sq_eta.fun_add hd_exp_c
      have h_bz_t : etaTraj γ θ (blochZ ρ) t = blochZ (thermalSemigroupC γ ω θ t ρ) :=
        (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hsa htr).2.2.1.symm
      have hc_r : coherenceSq (thermalSemigroupC γ ω θ t ρ) =
          (blochRadius (thermalSemigroupC γ ω θ t ρ)) ^ 2 -
            (blochZ (thermalSemigroupC γ ω θ t ρ)) ^ 2 := by
        rw [blochRadius_sq]; dsimp [blochNormSq]; ring_nf
      exact hd_sum.congr_deriv (by rw [h_bz_t, hc_r]; ring_nf)
    have hd_r : HasDerivAt (fun s => Real.sqrt (f s))
        ((-γ * ((blochRadius (thermalSemigroupC γ ω θ t ρ)) ^ 2 +
          (blochZ (thermalSemigroupC γ ω θ t ρ)) ^ 2 -
          2 * blochZ (thermalSemigroupC γ ω θ t ρ) * meanSpin θ)) /
          (2 * blochRadius (thermalSemigroupC γ ω θ t ρ))) t := by
      have h_sqrt := HasDerivAt.sqrt hd_f (ne_of_gt hf_pos)
      have h_sq_r : Real.sqrt (f t) = blochRadius (thermalSemigroupC γ ω θ t ρ) :=
        (h_radius_t_fun t).symm
      simpa only [h_sq_r] using h_sqrt
    have hr_lo : -1 < blochRadius (thermalSemigroupC γ ω θ t ρ) :=
      lt_of_lt_of_le (by norm_num) (blochRadius_nonneg (thermalSemigroupC γ ω θ t ρ))
    have hr_hi : blochRadius (thermalSemigroupC γ ω θ t ρ) < 1 := blochRadius_lt_one hb_t
    have hd_phi_base : HasDerivAt negEntropyPhi
        (canonicalTheta (blochRadius (thermalSemigroupC γ ω θ t ρ))) (Real.sqrt (f t)) := by
      rw [← h_radius_t_fun t]
      exact dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.1
        (blochRadius (thermalSemigroupC γ ω θ t ρ)) hr_lo hr_hi
    have hd_phi := hd_phi_base.comp t hd_r
    have hd_tot := (hd_phi.fun_add (hasDerivAt_const t (cumulantPsi θ))).fun_sub
      (hd_eta.const_mul θ)
    have h_deriv_eq :
        canonicalTheta (blochRadius (thermalSemigroupC γ ω θ t ρ)) *
          ((-γ * ((blochRadius (thermalSemigroupC γ ω θ t ρ)) ^ 2 +
            (blochZ (thermalSemigroupC γ ω θ t ρ)) ^ 2 -
            2 * blochZ (thermalSemigroupC γ ω θ t ρ) * meanSpin θ)) /
            (2 * blochRadius (thermalSemigroupC γ ω θ t ρ))) + 0 -
          θ * (-γ * (etaTraj γ θ (blochZ ρ) t - meanSpin θ)) =
          -quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ) := by
      have h_bz_t : etaTraj γ θ (blochZ ρ) t = blochZ (thermalSemigroupC γ ω θ t ρ) :=
        (thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hsa htr).2.2.1.symm
      rw [h_spohn_t.2.1, h_bz_t]
      have hr_ne : blochRadius (thermalSemigroupC γ ω θ t ρ) ≠ 0 := ne_of_gt hr_t_pos
      field_simp [hr_ne]; ring_nf
    have hd_final : HasDerivAt (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ)
        (-quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ)) t :=
      (hd_tot.congr_deriv h_deriv_eq).congr_of_eventuallyEq h_ev
    exact ⟨hd_final, neg_nonpos.mpr h_spohn_t.2.2.1⟩
  have h_coh_traj : ρ 0 1 ≠ 0 → ∀ t : ℝ, 0 ≤ t →
      0 < blochRadius (thermalSemigroupC γ ω θ t ρ) ∧
      0 < quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ) := by
    intro h01 t ht
    have h_pres := @thermalSemigroupC_preserves_blochBall γ ω θ t ρ hγ ht hsa htr hb
    have hc_pos : 0 < coherenceSq (thermalSemigroupC γ ω θ t ρ) := by
      rw [h_pres.2.2.1]
      dsimp [coherenceSq]
      exact mul_pos (Real.exp_pos _) (mul_pos (by norm_num) (Complex.normSq_pos.mpr h01))
    have hb_pos : 0 < blochNormSq (thermalSemigroupC γ ω θ t ρ) := by
      dsimp [blochNormSq]; nlinarith [sq_nonneg (blochZ (thermalSemigroupC γ ω θ t ρ))]
    have hr_pos : 0 < blochRadius (thermalSemigroupC γ ω θ t ρ) := Real.sqrt_pos.mpr hb_pos
    have h01_t : thermalSemigroupC γ ω θ t ρ 0 1 ≠ 0 := by
      intro h01z
      have : coherenceSq (thermalSemigroupC γ ω θ t ρ) = 0 := by
        dsimp [coherenceSq]; simp [h01z]
      linarith
    exact ⟨hr_pos, (@operator_spohn_rate_and_strict_coherent_dissipation γ ω θ
      (thermalSemigroupC γ ω θ t ρ) hγ h_pres.1 h_pres.2.1 hr_pos h_pres.2.2.2.1).2.2.2 h01_t⟩
  have h_neg_lim : Tendsto (fun s : ℝ => Real.exp (-γ * s)) atTop (𝓝 0) := by
    have h_mul_top : Tendsto (fun s : ℝ => γ * s) atTop atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos hγ).mpr Filter.tendsto_id
    have h_neg_bot : Tendsto (fun s : ℝ => -(γ * s)) atTop Filter.atBot :=
      Filter.tendsto_neg_atBot_iff.mpr h_mul_top
    have h_eq : (fun s : ℝ => Real.exp (-γ * s)) = (fun s : ℝ => Real.exp (-(γ * s))) := by
      ext s; ring_nf
    rw [h_eq]
    exact Real.tendsto_exp_atBot.comp h_neg_bot
  have h_ecoh_lim : Tendsto (fun s : ℝ => Real.exp (-(γ / 2) * s)) atTop (𝓝 0) := by
    have hγ2 : 0 < γ / 2 := half_pos hγ
    have h_mul_top : Tendsto (fun s : ℝ => (γ / 2) * s) atTop atTop :=
      (Filter.tendsto_const_mul_atTop_of_pos hγ2).mpr Filter.tendsto_id
    have h_neg_bot : Tendsto (fun s : ℝ => -((γ / 2) * s)) atTop Filter.atBot :=
      Filter.tendsto_neg_atBot_iff.mpr h_mul_top
    have h_eq : (fun s : ℝ => Real.exp (-(γ / 2) * s)) = (fun s : ℝ => Real.exp (-((γ / 2) * s))) := by
      ext s; ring_nf
    rw [h_eq]
    exact Real.tendsto_exp_atBot.comp h_neg_bot
  have h_mat_lim : ∀ i j : Fin 2,
      Tendsto (fun s => thermalSemigroupC γ ω θ s ρ i j) atTop (𝓝 (gibbsDensityC θ i j)) := by
    have htr_c : ρ 0 0 + ρ 1 1 = 1 := by rw [trace_fin2] at htr; exact htr
    have h_exp_c : Tendsto (fun s : ℝ => (Real.exp (-γ * s) : ℂ)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun s : ℝ => (Real.exp (-γ * s) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp h_neg_lim
      simpa only [Complex.ofReal_zero] using h0
    have h_ecoh_norm : Tendsto (fun s : ℝ => ‖(Real.exp (-(γ / 2) * s) : ℂ) *
        Complex.exp (-Complex.I * (ω : ℂ) * (s : ℂ))‖) atTop (𝓝 0) := by
      have h_eq : (fun s : ℝ => ‖(Real.exp (-(γ / 2) * s) : ℂ) *
          Complex.exp (-Complex.I * (ω : ℂ) * (s : ℂ))‖) =
          fun s : ℝ => Real.exp (-(γ / 2) * s) := by
        ext s
        have h_arg : -Complex.I * (ω : ℂ) * (s : ℂ) = ((-ω * s : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _)),
          h_arg, Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [h_eq]; exact h_ecoh_lim
    have h_prod_01 : Tendsto (fun s : ℝ => (Real.exp (-(γ / 2) * s) : ℂ) *
        Complex.exp (-Complex.I * (ω : ℂ) * (s : ℂ)) * ρ 0 1) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_zero_iff_norm_tendsto_zero.mpr h_ecoh_norm).mul_const (ρ 0 1)
    have h_ecoh_norm' : Tendsto (fun s : ℝ => ‖(Real.exp (-(γ / 2) * s) : ℂ) *
        Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ))‖) atTop (𝓝 0) := by
      have h_eq : (fun s : ℝ => ‖(Real.exp (-(γ / 2) * s) : ℂ) *
          Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ))‖) =
          fun s : ℝ => Real.exp (-(γ / 2) * s) := by
        ext s
        have h_arg : Complex.I * (ω : ℂ) * (s : ℂ) = ((ω * s : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _)),
          h_arg, Complex.norm_exp_ofReal_mul_I, mul_one]
      rw [h_eq]; exact h_ecoh_lim
    have h_prod_10 : Tendsto (fun s : ℝ => (Real.exp (-(γ / 2) * s) : ℂ) *
        Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ)) * ρ 1 0) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_zero_iff_norm_tendsto_zero.mpr h_ecoh_norm').mul_const (ρ 1 0)
    intro i j
    fin_cases i <;> fin_cases j
    · change Tendsto (fun s => (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * s) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
        atTop (𝓝 (boltzmannPlus θ : ℂ))
      rw [htr_c, mul_one]
      simpa only [zero_mul, add_zero] using
        tendsto_const_nhds.add (h_exp_c.mul_const (ρ 0 0 - (boltzmannPlus θ : ℂ)))
    · change Tendsto (fun s => (Real.exp (-(γ / 2) * s) : ℂ) *
          Complex.exp (-Complex.I * (ω : ℂ) * (s : ℂ)) * ρ 0 1) atTop (𝓝 0)
      exact h_prod_01
    · change Tendsto (fun s => (Real.exp (-(γ / 2) * s) : ℂ) *
          Complex.exp (Complex.I * (ω : ℂ) * (s : ℂ)) * ρ 1 0) atTop (𝓝 0)
      exact h_prod_10
    · change Tendsto (fun s => (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1) +
          (Real.exp (-γ * s) : ℂ) * (ρ 1 1 - (boltzmannMinus θ : ℂ) * (ρ 0 0 + ρ 1 1)))
        atTop (𝓝 (boltzmannMinus θ : ℂ))
      rw [htr_c, mul_one]
      simpa only [zero_mul, add_zero] using
        tendsto_const_nhds.add (h_exp_c.mul_const (ρ 1 1 - (boltzmannMinus θ : ℂ)))
  have h_umegaki_lim :
      Tendsto (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ) atTop (𝓝 0) := by
    have h_eta_lim : Tendsto (etaTraj γ θ (blochZ ρ)) atTop (𝓝 (meanSpin θ)) := by
      unfold etaTraj
      simpa using (tendsto_const_nhds.add (h_neg_lim.mul_const _))
    have h_rad_lim : Tendsto (fun s => blochRadius (thermalSemigroupC γ ω θ s ρ))
        atTop (𝓝 |meanSpin θ|) := by
      have h_fn_eq : (fun s => blochRadius (thermalSemigroupC γ ω θ s ρ)) =
          fun s => Real.sqrt ((etaTraj γ θ (blochZ ρ) s) ^ 2 + Real.exp (-γ * s) * coherenceSq ρ) :=
        funext h_radius_t_fun
      rw [h_fn_eq]
      have h_inner : Tendsto
          (fun s => (etaTraj γ θ (blochZ ρ) s) ^ 2 + Real.exp (-γ * s) * coherenceSq ρ)
          atTop (𝓝 ((meanSpin θ) ^ 2 + 0 * coherenceSq ρ)) :=
        (h_eta_lim.pow 2).add (h_neg_lim.mul_const _)
      have h_sqrt := Real.continuous_sqrt.continuousAt.tendsto.comp h_inner
      simpa only [Function.comp_def, zero_mul, add_zero, Real.sqrt_sq_eq_abs] using h_sqrt
    have hm_abs_lo : -1 < |meanSpin θ| := by
      linarith [abs_nonneg (meanSpin θ)]
    have hm_abs_hi : |meanSpin θ| < 1 := by
      rcases meanSpin_mem_Ioo θ with ⟨hm_lo, hm_hi⟩
      exact abs_lt.mpr ⟨hm_lo, hm_hi⟩
    have h_phi_cont : ContinuousAt negEntropyPhi |meanSpin θ| :=
      (dually_flat_legendre_reciprocity_and_metric_inversion.2.2.2.1 _ hm_abs_lo hm_abs_hi).continuousAt
    have h_phi_lim : Tendsto (fun s => negEntropyPhi (blochRadius (thermalSemigroupC γ ω θ s ρ)))
        atTop (𝓝 (negEntropyPhi |meanSpin θ|)) :=
      h_phi_cont.tendsto.comp h_rad_lim
    have h_target_lim : Tendsto (fun s =>
        negEntropyPhi (blochRadius (thermalSemigroupC γ ω θ s ρ)) + cumulantPsi θ -
          θ * etaTraj γ θ (blochZ ρ) s) atTop (𝓝 0) := by
      have h_fy : negEntropyPhi |meanSpin θ| + cumulantPsi θ - θ * meanSpin θ = 0 := by
        have h_abs_eq : negEntropyPhi |meanSpin θ| = negEntropyPhi (meanSpin θ) := by
          rcases le_total 0 (meanSpin θ) with hnn | hnp
          · rw [abs_of_nonneg hnn]
          · rw [abs_of_nonpos hnp, negEntropyPhi_even]
        have h_id := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 θ
        rw [h_abs_eq]; linarith
      rw [← h_fy]
      exact (h_phi_lim.add tendsto_const_nhds).sub (h_eta_lim.const_mul θ)
    have h_ev_eq : ∀ᶠ s in atTop,
        negEntropyPhi (blochRadius (thermalSemigroupC γ ω θ s ρ)) + cumulantPsi θ -
          θ * etaTraj γ θ (blochZ ρ) s =
        quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ := by
      refine (eventually_ge_atTop (0 : ℝ)).mono fun s hs => ?_
      have hb_s := (@thermalSemigroupC_preserves_blochBall γ ω θ s ρ hγ hs hsa htr hb).2.2.2.1
      exact (h_umegaki_formula s hb_s).symm
    exact h_target_lim.congr' h_ev_eq
  exact ⟨h_ode_and_sign, h_coh_traj, h_mat_lim, h_umegaki_lim⟩

-- theorem-class: identity
/-- Full-matrix Umegaki entropy production with its exact coherence correction to the Jeffreys
term, along the forward thermal semigroup on every faithful state in the open Bloch ball. -/
@[rep_depth thermo, capstone]
theorem master_bloch_quantum_spohn_jeffreys_coherence_lag
    {γ ω θ : ℝ} {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hγ : 0 < γ) (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1)
    (hb : blochNormSq ρ < 1) :
    ∀ t : ℝ, 0 ≤ t → 0 < blochRadius (thermalSemigroupC γ ω θ t ρ) →
      HasDerivAt
        (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ)
        (-γ * (blochJeffreysTerm θ (thermalSemigroupC γ ω θ t ρ) -
          (canonicalTheta (blochRadius (thermalSemigroupC γ ω θ t ρ)) /
            (2 * blochRadius (thermalSemigroupC γ ω θ t ρ))) *
              coherenceSq (thermalSemigroupC γ ω θ t ρ))) t := by
  intro t ht hr_t
  have h_deriv := (master_bloch_umegaki_spohn_and_gibbs_relaxation
    hγ hsa htr hb).1 t ht hr_t |>.1
  have h_pres := @thermalSemigroupC_preserves_blochBall γ ω θ t ρ hγ ht hsa htr hb
  have h_rate := quantumSpohnRate_eq_blochJeffreys_minus_coherence
    (γ := γ) (ω := ω) (θ := θ) (σ := thermalSemigroupC γ ω θ t ρ)
    hγ h_pres.1 h_pres.2.1 hr_t h_pres.2.2.2.1
  rw [h_rate] at h_deriv
  convert h_deriv using 1; ring_nf

end ArchetypeG10_KolmogorovODEAndQuantumSpohn

/-!
## Welded Acyclic Causal Poset $(\mathfrak{P}, \prec) = (Y_0 \prec \dots \prec Y_9)$ & Socratic Rungs 1–4

Closes the binary cut between the algebraic $\star$-ring GKSL core ($\mathcal{G}_1$), the
Witt CAR Lindblad semigroup ($\mathcal{G}_2, \mathcal{G}_3$), the full 3D Bloch cumulant geometry
($\Psi_3, \Phi_3$), diagonal pinching orthogonality ($\Delta_{\mathrm{pinch}}$), Larmor equipotential
vorticity, and the exact coherence-corrected quantum Spohn–Jeffreys law on $\mathbb{B}^3 \subset M_2(\mathbb{C})$.
-/

section WeldedCoagulaPoset_Y0_Y9

/-!
### Pure Scalar Helper Lemmas for 3D Bloch Cumulants, KMS Ratio & Coherence Lag
-/

private lemma canonicalTheta_neg (η : ℝ) : canonicalTheta (-η) = -canonicalTheta η := by
  dsimp [canonicalTheta]
  have h_inv : (1 + -η) / (1 - -η) = ((1 + η) / (1 - η))⁻¹ := by rw [inv_div]; ring
  rw [h_inv, Real.log_inv]
  ring

private lemma canonicalTheta_pos_of_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < canonicalTheta r := by
  dsimp [canonicalTheta]
  have hden : 0 < 1 - r := by linarith [hr1]
  have hgt : 1 < (1 + r) / (1 - r) := (one_lt_div hden).mpr (by linarith [hr0])
  exact mul_pos (by norm_num) (Real.log_pos hgt)

private lemma canonicalTheta_abs_mul_self {r z : ℝ} (hr0 : 0 < r) (hrsq : z ^ 2 = r ^ 2) :
    (canonicalTheta r / r) * z = canonicalTheta z := by
  have hr_ne : r ≠ 0 := ne_of_gt hr0
  have hz_abs : z = r ∨ z = -r := sq_eq_sq_iff_eq_or_eq_neg.mp hrsq
  rcases hz_abs with rfl | rfl
  · field_simp [hr_ne]
  · rw [canonicalTheta_neg]
    field_simp [hr_ne]

private lemma spohn_diag_eq_zero_iff_real {γ θ r z : ℝ} (hγ : 0 < γ)
    (hr0 : 0 < r) (hrsq : z ^ 2 = r ^ 2) (hz_lo : -1 < z) (hz_hi : z < 1) :
    γ * ((canonicalTheta r / (2 * r)) * (r ^ 2 + z ^ 2 - 2 * z * meanSpin θ) -
      θ * (z - meanSpin θ)) = 0 ↔ z = meanSpin θ := by
  have h_eq1 :
      (canonicalTheta r / (2 * r)) * (r ^ 2 + z ^ 2 - 2 * z * meanSpin θ) - θ * (z - meanSpin θ) =
        (z - meanSpin θ) * ((canonicalTheta r / r) * z - θ) := by
    have hsub : r ^ 2 + z ^ 2 - 2 * z * meanSpin θ = 2 * z * (z - meanSpin θ) := by
      linarith [hrsq]
    rw [hsub]
    ring
  rw [h_eq1, canonicalTheta_abs_mul_self hr0 hrsq, mul_eq_zero]
  constructor
  · intro h
    rcases h with hγ0 | hprod
    · linarith [hγ]
    · rcases mul_eq_zero.mp hprod with hz | hcth
      · linarith
      · have hcz : canonicalTheta z = θ := by linarith
        have h_inv := dually_flat_legendre_reciprocity_and_metric_inversion.2.1 z hz_lo hz_hi
        rw [hcz] at h_inv
        exact h_inv.symm
  · intro hz
    right
    rw [hz, sub_self, zero_mul]

private lemma cumulantPsi_even (θ : ℝ) : cumulantPsi (-θ) = cumulantPsi θ := by
  dsimp [cumulantPsi, partitionZ]
  rw [neg_neg, add_comm]

private lemma meanSpin_pos_of_pos {θ : ℝ} (hθ : 0 < θ) : 0 < meanSpin θ := by
  dsimp [meanSpin]
  have hZ : 0 < partitionZ θ := partitionZ_pos θ
  have hlt : -θ < θ := by linarith [hθ]
  have hexp : Real.exp (-θ) < Real.exp θ := Real.exp_lt_exp.mpr hlt
  exact div_pos (sub_pos.mpr hexp) hZ

private lemma meanSpin_neg_of_neg {θ : ℝ} (hθ : θ < 0) : meanSpin θ < 0 := by
  dsimp [meanSpin]
  have hZ : 0 < partitionZ θ := partitionZ_pos θ
  have hlt : θ < -θ := by linarith [hθ]
  have hexp : Real.exp θ < Real.exp (-θ) := Real.exp_lt_exp.mpr hlt
  exact div_neg_of_neg_of_pos (sub_neg.mpr hexp) hZ

private lemma negEntropyPhi_half_log_add {r : ℝ} (hr_lo : -1 < r) (hr_hi : r < 1) :
    (Real.log ((1 + r) / 2) + Real.log ((1 - r) / 2)) / 2 =
      negEntropyPhi r - r * canonicalTheta r := by
  have h1 : 0 < (1 + r) / 2 := by linarith [hr_lo]
  have h2 : 0 < (1 - r) / 2 := by linarith [hr_hi]
  have h_div : ((1 + r) / 2) / ((1 - r) / 2) = (1 + r) / (1 - r) := by field_simp
  dsimp [negEntropyPhi, canonicalTheta]
  rw [← h_div, Real.log_div (ne_of_gt h1) (ne_of_gt h2)]
  ring

private lemma jeffreys_trace_combine_real {r z η θ : ℝ}
    (hr_lo : -1 < r) (hr_hi : r < 1) (hr_ne : r ≠ 0) :
    (negEntropyPhi r + cumulantPsi θ - θ * z) +
      ((-cumulantPsi θ + θ * η) -
        (((Real.log ((1 + r) / 2) + Real.log ((1 - r) / 2)) / 2 - canonicalTheta r / r) +
          (2 * canonicalTheta r / r) * ((1 + z * η) / 2))) =
      (canonicalTheta r / r) * (r ^ 2 - z * η) - θ * (z - η) := by
  rw [negEntropyPhi_half_log_add hr_lo hr_hi]
  field_simp [hr_ne]
  ring

private lemma factor_two_canonicalTheta_pos {γ r : ℝ} (hγ : 0 < γ) (hr0 : 0 < r) (hr1 : r < 1) :
    0 < γ / 2 * r * canonicalTheta r := by
  have hct : 0 < canonicalTheta r := canonicalTheta_pos_of_pos hr0 hr1
  exact mul_pos (mul_pos (div_pos hγ (by norm_num)) hr0) hct

private lemma backward_exp_lt_one {γ t : ℝ} (hγ : 0 < γ) (ht : t < 0) :
    Real.exp (γ * t / 4) ^ 2 < 1 := by
  have hneg : γ * t / 4 < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hγ ht) (by norm_num)
  have hlt1 : Real.exp (γ * t / 4) < 1 := Real.exp_lt_one_iff.mpr hneg
  have hpos : 0 < Real.exp (γ * t / 4) := Real.exp_pos _
  nlinarith

private lemma backward_exp_gt_one {γ t η : ℝ} (hγ : 0 < γ) (ht : t < 0) :
    1 < η ^ 2 + Real.exp (-γ * t) * Real.exp (γ * t / 4) ^ 2 := by
  have h_prod : Real.exp (-γ * t) * Real.exp (γ * t / 4) ^ 2 = Real.exp (-(γ * t / 2)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpos_arg : 0 < -(γ * t / 2) := by
    have hneg : γ * t / 2 < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hγ ht) (by norm_num)
    linarith
  have hgt1 : 1 < Real.exp (-(γ * t / 2)) := Real.one_lt_exp_iff.mpr hpos_arg
  rw [h_prod]
  linarith [sq_nonneg η]

private lemma exp_neg_half_ne_exp_neg {γ : ℝ} (hγ : 0 < γ) :
    Real.exp (-γ) ≠ Real.exp (-(γ / 2)) := by
  intro h_eq
  have h_arg := Real.exp_injective h_eq
  linarith [hγ]

private lemma sq_lt_one_of_Ioo {z : ℝ} (h1 : -1 < z) (h2 : z < 1) : z ^ 2 < 1 := by
  nlinarith [h1, h2]

private lemma kms_ratio_real {β ω : ℝ} (hβ : 0 < β) (hω : 0 < ω) :
    let θ := -(β * ω) / 2
    θ < 0 ∧ boltzmannPlus θ < boltzmannMinus θ ∧
      boltzmannPlus θ / boltzmannMinus θ = Real.exp (-(β * ω)) := by
  intro θ
  have hθ_neg : θ < 0 := by
    dsimp [θ]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hβ hω)) (by norm_num)
  have h_mean_neg : meanSpin θ < 0 := meanSpin_neg_of_neg hθ_neg
  have h_bp_lt : boltzmannPlus θ < boltzmannMinus θ := by
    dsimp [boltzmannPlus, boltzmannMinus]
    linarith
  have h_ratio : boltzmannPlus θ / boltzmannMinus θ = Real.exp (-(β * ω)) := by
    dsimp [boltzmannPlus, boltzmannMinus]
    rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [one_add_meanSpin, one_sub_meanSpin]
    have hZ : partitionZ θ ≠ 0 := ne_of_gt (partitionZ_pos θ)
    have h_en : Real.exp (-θ) ≠ 0 := ne_of_gt (Real.exp_pos (-θ))
    have h_div : (2 * Real.exp θ / partitionZ θ) / (2 * Real.exp (-θ) / partitionZ θ) =
        Real.exp (2 * θ) := by
      have h1 : (2 * Real.exp θ / partitionZ θ) / (2 * Real.exp (-θ) / partitionZ θ) =
          Real.exp θ / Real.exp (-θ) := by field_simp
      rw [h1, ← Real.exp_sub]
      congr 1; ring
    rw [h_div]
    congr 1
    dsimp [θ]; ring
  exact ⟨hθ_neg, h_bp_lt, h_ratio⟩

/-!
### Causal Poset $(\mathfrak{P}, \prec) = (Y_0 \prec \dots \prec Y_9)$
-/

/-- Nodes of the welded 3D noncommutative quantum-thermodynamic causal poset $(\mathfrak{P}, \prec)$
connecting the $\star$-ring GKSL core ($Y_0$) cleanly to the full 3D coherence-corrected
Umegaki–Spohn synthesis ($Y_9$). -/
inductive WeldedQuantumSpohnArchetype
  | Y0
  | Y1
  | Y2
  | Y3
  | Y4
  | Y5
  | Y6
  | Y7
  | Y8
  | Y9
  deriving DecidableEq, Repr, Inhabited

/-- Topological index $0 \dots 9$ witnessing acyclicity of $(\mathfrak{P}, \prec)$. -/
def WeldedQuantumSpohnArchetype.idx : WeldedQuantumSpohnArchetype → ℕ
  | .Y0 => 0
  | .Y1 => 1
  | .Y2 => 2
  | .Y3 => 3
  | .Y4 => 4
  | .Y5 => 5
  | .Y6 => 6
  | .Y7 => 7
  | .Y8 => 8
  | .Y9 => 9

/-- Exact transitive-reflexive reachability of the covering relations
$Y_0 \prec \{Y_1, Y_3\}$, $Y_1 \prec \{Y_2, Y_4\}$, $Y_3 \prec Y_4$, $\{Y_2, Y_4\} \prec Y_5 \prec Y_6 \prec Y_7$,
$\{Y_4, Y_7\} \prec Y_8 \prec Y_9$. -/
def weldedPosetLE (a b : WeldedQuantumSpohnArchetype) : Prop :=
  match a with
  | .Y0 => True
  | .Y1 => b = .Y1 ∨ b = .Y2 ∨ 4 ≤ b.idx
  | .Y2 => b = .Y2 ∨ 5 ≤ b.idx
  | .Y3 => 3 ≤ b.idx
  | .Y4 => 4 ≤ b.idx
  | .Y5 => 5 ≤ b.idx
  | .Y6 => 6 ≤ b.idx
  | .Y7 => 7 ≤ b.idx
  | .Y8 => 8 ≤ b.idx
  | .Y9 => 9 ≤ b.idx

instance : DecidableRel weldedPosetLE := fun a b => by
  cases a <;> dsimp [weldedPosetLE] <;> infer_instance

private lemma weldedPosetLE_idx_le {a b : WeldedQuantumSpohnArchetype} (h : weldedPosetLE a b) :
    a.idx ≤ b.idx := by
  cases a <;> cases b <;>
    first
    | decide
    | exact False.elim (by simp [weldedPosetLE, WeldedQuantumSpohnArchetype.idx] at h)

private lemma weldedPosetLE_idx_eq {a b : WeldedQuantumSpohnArchetype}
    (h : a.idx = b.idx) : a = b := by
  cases a <;> cases b <;>
    first
    | rfl
    | exact False.elim (by simp [WeldedQuantumSpohnArchetype.idx] at h)

instance : PartialOrder WeldedQuantumSpohnArchetype where
  le := weldedPosetLE
  le_refl a := by cases a <;> simp [weldedPosetLE, WeldedQuantumSpohnArchetype.idx]
  le_trans a b c hab hbc := by
    have hbc_idx := weldedPosetLE_idx_le hbc
    cases a
    · exact True.intro
    · dsimp [weldedPosetLE] at hab ⊢
      rcases hab with rfl | rfl | hb4
      · exact hbc
      · dsimp [weldedPosetLE] at hbc
        rcases hbc with rfl | hc5
        · right; left; rfl
        · right; right; omega
      · right; right; omega
    · dsimp [weldedPosetLE] at hab ⊢
      rcases hab with rfl | hb5
      · exact hbc
      · right; omega
    all_goals
      dsimp [weldedPosetLE] at hab ⊢
      omega
  le_antisymm a b hab hba := by
    apply weldedPosetLE_idx_eq
    exact le_antisymm (weldedPosetLE_idx_le hab) (weldedPosetLE_idx_le hba)

-- theorem-class: bridge
/-- `Y0` is the bottom element, `Y9` is the top element, strict order `<` strictly increases
the topological index `idx`, and incomparable branches (`Y1 ≰ Y3`, `Y2 ∦ Y4`) separate
dynamical/Heisenberg ($Y_1, Y_2$) from Bloch–cumulant geometry ($Y_3, Y_4$). -/
@[rep_depth thermo]
theorem weldedPoset_acyclic_and_bounds :
    (∀ a b : WeldedQuantumSpohnArchetype, a < b → a.idx < b.idx) ∧
    (∀ x : WeldedQuantumSpohnArchetype, .Y0 ≤ x ∧ x ≤ .Y9) ∧
    ¬(WeldedQuantumSpohnArchetype.Y1 ≤ .Y3) ∧
    ¬(WeldedQuantumSpohnArchetype.Y2 ≤ .Y4) ∧
    ¬(WeldedQuantumSpohnArchetype.Y4 ≤ .Y2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hle : a.idx ≤ b.idx := weldedPosetLE_idx_le hab.1
    have hne : a ≠ b := hab.ne
    have hidx_ne : a.idx ≠ b.idx := fun h => hne (weldedPosetLE_idx_eq h)
    omega
  · intro x
    refine ⟨True.intro, ?_⟩
    change weldedPosetLE x .Y9
    cases x <;> decide
  · change ¬weldedPosetLE .Y1 .Y3; decide
  · change ¬weldedPosetLE .Y2 .Y4; decide
  · change ¬weldedPosetLE .Y4 .Y2; decide

/-!
### $Y_0 \prec Y_1$ & Rung 1: Witt CAR `gkslGen2` Realization, Physical KMS Alignment, and Carré du Champ $1:2$ Damping Ratio
-/

/-- Pauli flip matrix $\sigma_x = F_+ + F_- = \bigl(\begin{smallmatrix} 0 & 1 \\ 1 & 0 \end{smallmatrix}\bigr)$. -/
def pauliSigmaX : InfoGeometry.Algebra.FiniteSpin.Mat2C :=
  wittFPlus + wittFMinus

/-- Pauli transverse matrix $\sigma_y = -i(F_+ - F_-) = \bigl(\begin{smallmatrix} 0 & -i \\ i & 0 \end{smallmatrix}\bigr)$. -/
def pauliSigmaY : InfoGeometry.Algebra.FiniteSpin.Mat2C :=
  (-Complex.I) • (wittFPlus - wittFMinus)

/-- Physical positive-temperature KMS inverse-temperature alignment $\theta = -\beta\omega / 2$
for Hamiltonian $H = \frac{\omega}{2}\Gamma_1$. -/
def kmsBoltzmannTheta (β ω : ℝ) : ℝ := -(β * ω) / 2

/-- Dual Heisenberg dissipator $\mathcal{D}_{\gamma,\theta}^\dagger(A)$ of the Witt CAR thermal
Lindblad semigroup. -/
def thermalHeisenbergDissipator (γ θ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((ratePlus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFPlus A +
    ((rateMinus γ θ : ℂ) / 2) • heisenbergDissipator2 wittFMinus A

-- theorem-class: conservation
/-- **$Y_0 \prec Y_1$ & Socratic Rung 1 (Witt CAR `gkslGen2` Bridge & Heisenberg Carré du Champ Ratio)**:
1. `wittFPlus`, `wittFMinus`, `pauliSigmaX`, `pauliSigmaY`, and `pauliGamma1` obey exact Witt CAR and
   Pauli Clifford square identities;
2. `thermalLindbladianOp` is the exact $\mathcal{G}_1$ `gkslGen2` operator evaluation with jump channels
   $\sqrt{\gamma_+ / 2}\,F_+$ and $\sqrt{\gamma_- / 2}\,F_-$;
3. For $\beta > 0$ and $\omega_{\mathrm{pos}} > 0$, the KMS Boltzmann parameter `kmsBoltzmannTheta β ω_pos` is negative,
   yielding ground-state population dominance $p_+ < p_-$ with $p_+ / p_- = e^{-\beta\omega_{\mathrm{pos}}}$;
4. Evaluating `algebraic_gksl_star_unital_and_carre_du_champ` on $\sigma_x$ vs. $\Gamma_1$ proves
   why transverse coherences decay at $\gamma/2$ while longitudinal population decays at $\gamma$,
   with equilibrium $\Gamma_1$ carré du champ expectation $2\gamma(1 - \eta_\theta^2)$. -/
@[rep_depth operator]
theorem wittCAR_gkslGen2_and_carre_du_champ_damping_ratio
    {γ : ℝ} (hγ : 0 ≤ γ) (ω θ : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (wittFPlusᴴ = wittFMinus ∧
      ⁅wittFPlus, wittFMinus⁆ = pauliGamma1 ∧
      pauliSigmaX * pauliSigmaX = 1 ∧
      pauliSigmaY * pauliSigmaY = 1 ∧
      pauliGamma1 * pauliGamma1 = 1) ∧
    (thermalLindbladianOp γ ω θ ρ =
      gkslGen2 (-(Complex.I * (ω : ℂ) / 2) • pauliGamma1)
        ((Real.sqrt (ratePlus γ θ / 2) : ℂ) • wittFPlus) ρ +
      lindbladDissipator2 ((Real.sqrt (rateMinus γ θ / 2) : ℂ) • wittFMinus) ρ) ∧
    (∀ β ω_pos : ℝ, 0 < β → 0 < ω_pos →
      kmsBoltzmannTheta β ω_pos < 0 ∧
      boltzmannPlus (kmsBoltzmannTheta β ω_pos) < boltzmannMinus (kmsBoltzmannTheta β ω_pos) ∧
      boltzmannPlus (kmsBoltzmannTheta β ω_pos) / boltzmannMinus (kmsBoltzmannTheta β ω_pos) =
        Real.exp (-(β * ω_pos))) ∧
    (thermalHeisenbergDissipator γ θ 1 = 0 ∧
      thermalHeisenbergDissipator γ θ (pauliSigmaX * pauliSigmaX) -
        (thermalHeisenbergDissipator γ θ pauliSigmaX * pauliSigmaX +
         pauliSigmaX * thermalHeisenbergDissipator γ θ pauliSigmaX) =
        (ratePlus γ θ : ℂ) • (star ⁅wittFPlus, pauliSigmaX⁆ * ⁅wittFPlus, pauliSigmaX⁆) +
        (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, pauliSigmaX⁆ * ⁅wittFMinus, pauliSigmaX⁆) ∧
      (ratePlus γ θ : ℂ) • (star ⁅wittFPlus, pauliSigmaX⁆ * ⁅wittFPlus, pauliSigmaX⁆) +
        (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, pauliSigmaX⁆ * ⁅wittFMinus, pauliSigmaX⁆) =
        (γ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      thermalHeisenbergDissipator γ θ pauliSigmaX = -((γ / 2 : ℝ) : ℂ) • pauliSigmaX ∧
      thermalHeisenbergDissipator γ θ pauliSigmaY = -((γ / 2 : ℝ) : ℂ) • pauliSigmaY ∧
      thermalHeisenbergDissipator γ θ pauliGamma1 =
        -(γ : ℂ) • (pauliGamma1 - (meanSpin θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      Matrix.trace (gibbsDensityC θ *
        ((ratePlus γ θ : ℂ) • (star ⁅wittFPlus, pauliGamma1⁆ * ⁅wittFPlus, pauliGamma1⁆) +
         (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, pauliGamma1⁆ * ⁅wittFMinus, pauliGamma1⁆))) =
        ((2 * γ * (1 - (meanSpin θ) ^ 2) : ℝ) : ℂ)) := by
  have h_car : wittFPlusᴴ = wittFMinus ∧
      ⁅wittFPlus, wittFMinus⁆ = pauliGamma1 ∧
      pauliSigmaX * pauliSigmaX = 1 ∧
      pauliSigmaY * pauliSigmaY = 1 ∧
      pauliGamma1 * pauliGamma1 = 1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · apply ext_mat2 <;>
        simp [wittFPlus, wittFMinus, InfoGeometry.Algebra.FiniteSpin.J_plus,
          InfoGeometry.Algebra.FiniteSpin.J_minus, Matrix.conjTranspose_apply]
    · rw [Ring.lie_def]
      apply ext_mat2 <;>
        simp [wittFPlus, wittFMinus, pauliGamma1_mat2,
          InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus]
    · apply ext_mat2 <;>
        simp [pauliSigmaX, wittFPlus, wittFMinus,
          InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus]
    · apply ext_mat2 <;>
        simp [pauliSigmaY, wittFPlus, wittFMinus,
          InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus]
    · apply ext_mat2 <;> simp [pauliGamma1_mat2]
  have h_gksl : thermalLindbladianOp γ ω θ ρ =
      gkslGen2 (-(Complex.I * (ω : ℂ) / 2) • pauliGamma1)
        ((Real.sqrt (ratePlus γ θ / 2) : ℂ) • wittFPlus) ρ +
      lindbladDissipator2 ((Real.sqrt (rateMinus γ θ / 2) : ℂ) • wittFMinus) ρ := by
    have hbp_nn : 0 ≤ ratePlus γ θ / 2 := by
      dsimp [ratePlus]
      exact div_nonneg (mul_nonneg hγ (le_of_lt (boltzmann_nonneg θ).1)) (by norm_num)
    have hbm_nn : 0 ≤ rateMinus γ θ / 2 := by
      dsimp [rateMinus]
      exact div_nonneg (mul_nonneg hγ (le_of_lt (boltzmann_nonneg θ).2)) (by norm_num)
    have h_sqp : (Real.sqrt (ratePlus γ θ / 2) : ℂ) * (Real.sqrt (ratePlus γ θ / 2) : ℂ) =
        ((ratePlus γ θ : ℂ) / 2) := by
      exact_mod_cast Real.mul_self_sqrt hbp_nn
    have h_sqm : (Real.sqrt (rateMinus γ θ / 2) : ℂ) * (Real.sqrt (rateMinus γ θ / 2) : ℂ) =
        ((rateMinus γ θ : ℂ) / 2) := by
      exact_mod_cast Real.mul_self_sqrt hbm_nn
    have h_diss_scale : ∀ (c r : ℂ) (L : Matrix (Fin 2) (Fin 2) ℂ),
        star c = c → c * c = r →
        r • lindbladDissipator2 L ρ = lindbladDissipator2 (c • L) ρ := by
      intro c r L hsc hcc
      dsimp [lindbladDissipator2]
      rw [two_mul, two_mul]
      simp only [star_smul, hsc, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub,
        smul_smul, hcc]
    rw [thermalLindbladianOp, gkslGen2]
    have h_lie : (-(Complex.I * (ω : ℂ) / 2)) • ⁅pauliGamma1, ρ⁆ =
        ⁅-(Complex.I * (ω : ℂ) / 2) • pauliGamma1, ρ⁆ := by
      simp only [Ring.lie_def, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    have h_dp : ((ratePlus γ θ : ℂ) / 2) • lindbladDissipator2 wittFPlus ρ =
        lindbladDissipator2 ((Real.sqrt (ratePlus γ θ / 2) : ℂ) • wittFPlus) ρ :=
      h_diss_scale _ _ wittFPlus (Complex.conj_ofReal _) h_sqp
    have h_dm : ((rateMinus γ θ : ℂ) / 2) • lindbladDissipator2 wittFMinus ρ =
        lindbladDissipator2 ((Real.sqrt (rateMinus γ θ / 2) : ℂ) • wittFMinus) ρ :=
      h_diss_scale _ _ wittFMinus (Complex.conj_ofReal _) h_sqm
    rw [h_lie, h_dp, h_dm, add_assoc]
  have h_kms : ∀ β ω_pos : ℝ, 0 < β → 0 < ω_pos →
      kmsBoltzmannTheta β ω_pos < 0 ∧
      boltzmannPlus (kmsBoltzmannTheta β ω_pos) < boltzmannMinus (kmsBoltzmannTheta β ω_pos) ∧
      boltzmannPlus (kmsBoltzmannTheta β ω_pos) / boltzmannMinus (kmsBoltzmannTheta β ω_pos) =
        Real.exp (-(β * ω_pos)) := by
    intro β ω_pos hβ hω_pos
    simpa [kmsBoltzmannTheta] using kms_ratio_real hβ hω_pos
  have h_g1p := algebraic_gksl_star_unital_and_carre_du_champ
    (J := (0 : Matrix (Fin 2) (Fin 2) ℂ)) (by rw [star_zero, neg_zero]) wittFPlus ρ pauliSigmaX
  have h_g1m := algebraic_gksl_star_unital_and_carre_du_champ
    (J := (0 : Matrix (Fin 2) (Fin 2) ℂ)) (by rw [star_zero, neg_zero]) wittFMinus ρ pauliSigmaX
  have h_sa_sx : star pauliSigmaX = pauliSigmaX := by
    apply ext_mat2 <;>
      simp [pauliSigmaX, wittFPlus, wittFMinus,
        InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus,
        Matrix.star_apply]
  have h_unital : thermalHeisenbergDissipator γ θ 1 = 0 := by
    dsimp [thermalHeisenbergDissipator]
    rw [h_g1p.2.2.1, h_g1m.2.2.1, smul_zero, smul_zero, add_zero]
  have h_cdc_id :
      thermalHeisenbergDissipator γ θ (pauliSigmaX * pauliSigmaX) -
        (thermalHeisenbergDissipator γ θ pauliSigmaX * pauliSigmaX +
         pauliSigmaX * thermalHeisenbergDissipator γ θ pauliSigmaX) =
        (ratePlus γ θ : ℂ) • (star ⁅wittFPlus, pauliSigmaX⁆ * ⁅wittFPlus, pauliSigmaX⁆) +
        (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, pauliSigmaX⁆ * ⁅wittFMinus, pauliSigmaX⁆) := by
    have hp_cdc := h_g1p.2.2.2
    have hm_cdc := h_g1m.2.2.2
    rw [h_sa_sx] at hp_cdc hm_cdc
    have h_rearr :
        thermalHeisenbergDissipator γ θ (pauliSigmaX * pauliSigmaX) -
          (thermalHeisenbergDissipator γ θ pauliSigmaX * pauliSigmaX +
           pauliSigmaX * thermalHeisenbergDissipator γ θ pauliSigmaX) =
        ((ratePlus γ θ : ℂ) / 2) •
          (heisenbergDissipator2 wittFPlus (pauliSigmaX * pauliSigmaX) -
            (heisenbergDissipator2 wittFPlus pauliSigmaX * pauliSigmaX +
             pauliSigmaX * heisenbergDissipator2 wittFPlus pauliSigmaX)) +
        ((rateMinus γ θ : ℂ) / 2) •
          (heisenbergDissipator2 wittFMinus (pauliSigmaX * pauliSigmaX) -
            (heisenbergDissipator2 wittFMinus pauliSigmaX * pauliSigmaX +
             pauliSigmaX * heisenbergDissipator2 wittFMinus pauliSigmaX)) := by
      dsimp [thermalHeisenbergDissipator]
      simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_add]
      abel
    rw [h_rearr, hp_cdc, hm_cdc, two_mul, two_mul, smul_add, smul_add,
      ← add_smul, ← add_smul, add_halves, add_halves]
  have h_sum_rates : (ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ) = (γ : ℂ) := by
    have hr : ratePlus γ θ + rateMinus γ θ = γ := by
      dsimp [ratePlus, rateMinus]
      rw [← mul_add, (boltzmann_sum_and_diff θ).1, mul_one]
    exact_mod_cast hr
  have h_diff_rates : (ratePlus γ θ : ℂ) - (rateMinus γ θ : ℂ) = (γ : ℂ) * (meanSpin θ : ℂ) := by
    have hr : ratePlus γ θ - rateMinus γ θ = γ * meanSpin θ := by
      dsimp [ratePlus, rateMinus]
      rw [← mul_sub, (boltzmann_sum_and_diff θ).2]
    exact_mod_cast hr
  have h_half_sum : (ratePlus γ θ : ℂ) / 2 + (rateMinus γ θ : ℂ) / 2 = ((γ / 2 : ℝ) : ℂ) := by
    push_cast; linear_combination (1 / 2 : ℂ) * h_sum_rates
  have hwfp : wittFPlus = mat2 0 1 0 0 := by
    apply ext_mat2 <;> simp [wittFPlus, InfoGeometry.Algebra.FiniteSpin.J_plus]
  have hwfm : wittFMinus = mat2 0 0 1 0 := by
    apply ext_mat2 <;> simp [wittFMinus, InfoGeometry.Algebra.FiniteSpin.J_minus]
  have hpsx : pauliSigmaX = mat2 0 1 1 0 := by
    rw [pauliSigmaX, hwfp, hwfm]; apply ext_mat2 <;> simp
  have hpsy : pauliSigmaY = mat2 0 (-Complex.I) Complex.I 0 := by
    rw [pauliSigmaY, hwfp, hwfm]; apply ext_mat2 <;> simp
  have hpg1 : pauliGamma1 = mat2 1 0 0 (-1) := by
    apply ext_mat2 <;> simp [pauliGamma1_mat2]
  have h_cdc_sx :
      (ratePlus γ θ : ℂ) • (star ⁅wittFPlus, pauliSigmaX⁆ * ⁅wittFPlus, pauliSigmaX⁆) +
        (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, pauliSigmaX⁆ * ⁅wittFMinus, pauliSigmaX⁆) =
        (γ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h_px : star ⁅wittFPlus, pauliSigmaX⁆ * ⁅wittFPlus, pauliSigmaX⁆ = 1 := by
      rw [Ring.lie_def]
      apply ext_mat2 <;>
        simp [pauliSigmaX, wittFPlus, wittFMinus,
          InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus,
          Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two]
    have h_mx : star ⁅wittFMinus, pauliSigmaX⁆ * ⁅wittFMinus, pauliSigmaX⁆ = 1 := by
      rw [Ring.lie_def]
      apply ext_mat2 <;>
        simp [pauliSigmaX, wittFPlus, wittFMinus,
          InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus,
          Matrix.star_apply, Matrix.mul_apply, Fin.sum_univ_two]
    rw [h_px, h_mx, ← add_smul, h_sum_rates]
  have h_dx : thermalHeisenbergDissipator γ θ pauliSigmaX = -((γ / 2 : ℝ) : ℂ) • pauliSigmaX := by
    have h_dpx : heisenbergDissipator2 wittFPlus pauliSigmaX = -pauliSigmaX := by
      rw [heisenbergDissipator2, two_mul, hwfp, hpsx]
      apply ext_mat2 <;>
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
          mul2_00, mul2_01, mul2_10, mul2_11, Matrix.star_apply,
          mat2_00, mat2_01, mat2_10, mat2_11] <;>
        simp
    have h_dmx : heisenbergDissipator2 wittFMinus pauliSigmaX = -pauliSigmaX := by
      rw [heisenbergDissipator2, two_mul, hwfm, hpsx]
      apply ext_mat2 <;>
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
          mul2_00, mul2_01, mul2_10, mul2_11, Matrix.star_apply,
          mat2_00, mat2_01, mat2_10, mat2_11] <;>
        simp
    dsimp [thermalHeisenbergDissipator]
    rw [h_dpx, h_dmx, smul_neg, smul_neg, ← neg_add, ← add_smul, h_half_sum, ← neg_smul]
  have h_dy : thermalHeisenbergDissipator γ θ pauliSigmaY = -((γ / 2 : ℝ) : ℂ) • pauliSigmaY := by
    have h_dpy : heisenbergDissipator2 wittFPlus pauliSigmaY = -pauliSigmaY := by
      rw [heisenbergDissipator2, two_mul, hwfp, hpsy]
      apply ext_mat2 <;>
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
          mul2_00, mul2_01, mul2_10, mul2_11, Matrix.star_apply,
          mat2_00, mat2_01, mat2_10, mat2_11] <;>
        simp
    have h_dmy : heisenbergDissipator2 wittFMinus pauliSigmaY = -pauliSigmaY := by
      rw [heisenbergDissipator2, two_mul, hwfm, hpsy]
      apply ext_mat2 <;>
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply,
          mul2_00, mul2_01, mul2_10, mul2_11, Matrix.star_apply,
          mat2_00, mat2_01, mat2_10, mat2_11] <;>
        simp
    dsimp [thermalHeisenbergDissipator]
    rw [h_dpy, h_dmy, smul_neg, smul_neg, ← neg_add, ← add_smul, h_half_sum, ← neg_smul]
  have h_dz : thermalHeisenbergDissipator γ θ pauliGamma1 =
      -(γ : ℂ) • (pauliGamma1 - (meanSpin θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    have h_dpz : heisenbergDissipator2 wittFPlus pauliGamma1 = mat2 0 0 0 4 := by
      rw [heisenbergDissipator2, two_mul, hwfp, hpg1]
      apply ext_mat2 <;>
        simp only [Matrix.sub_apply, Matrix.add_apply,
          mul2_00, mul2_01, mul2_10, mul2_11, Matrix.star_apply,
          mat2_00, mat2_01, mat2_10, mat2_11] <;>
        simp
      norm_num
    have h_dmz : heisenbergDissipator2 wittFMinus pauliGamma1 = mat2 (-4) 0 0 0 := by
      rw [heisenbergDissipator2, two_mul, hwfm, hpg1]
      apply ext_mat2 <;>
        simp only [Matrix.sub_apply, Matrix.add_apply,
          mul2_00, mul2_01, mul2_10, mul2_11, Matrix.star_apply,
          mat2_00, mat2_01, mat2_10, mat2_11] <;>
        simp
      norm_num
    have h_r00 : ((rateMinus γ θ : ℂ) / 2) * (-4) = -(γ : ℂ) * (1 - (meanSpin θ : ℂ)) := by
      calc ((rateMinus γ θ : ℂ) / 2) * (-4) = -(2 * (rateMinus γ θ : ℂ)) := by ring_nf
        _ = -(((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) -
              ((ratePlus γ θ : ℂ) - (rateMinus γ θ : ℂ))) := by ring_nf
        _ = -(γ : ℂ) * (1 - (meanSpin θ : ℂ)) := by rw [h_sum_rates, h_diff_rates]; ring_nf
    have h_r11 : ((ratePlus γ θ : ℂ) / 2) * 4 = -(γ : ℂ) * (-1 - (meanSpin θ : ℂ)) := by
      calc ((ratePlus γ θ : ℂ) / 2) * 4 = 2 * (ratePlus γ θ : ℂ) := by ring_nf
        _ = ((ratePlus γ θ : ℂ) + (rateMinus γ θ : ℂ)) +
              ((ratePlus γ θ : ℂ) - (rateMinus γ θ : ℂ)) := by ring_nf
        _ = -(γ : ℂ) * (-1 - (meanSpin θ : ℂ)) := by rw [h_sum_rates, h_diff_rates]; ring_nf
    dsimp [thermalHeisenbergDissipator]
    rw [h_dpz, h_dmz]
    apply ext_mat2 <;> simp [pauliGamma1_mat2]
    · linear_combination -h_r00
    · linear_combination h_r11
  have h_gibbs_cdc :
      Matrix.trace (gibbsDensityC θ *
        ((ratePlus γ θ : ℂ) • (star ⁅wittFPlus, pauliGamma1⁆ * ⁅wittFPlus, pauliGamma1⁆) +
         (rateMinus γ θ : ℂ) • (star ⁅wittFMinus, pauliGamma1⁆ * ⁅wittFMinus, pauliGamma1⁆))) =
        ((2 * γ * (1 - (meanSpin θ) ^ 2) : ℝ) : ℂ) := by
    have h_pz : star ⁅wittFPlus, pauliGamma1⁆ * ⁅wittFPlus, pauliGamma1⁆ = mat2 0 0 0 4 := by
      rw [Ring.lie_def, hwfp, hpg1]
      apply ext_mat2 <;>
        simp only [Matrix.sub_apply, mul2_00, mul2_01, mul2_10, mul2_11, Matrix.star_apply,
          mat2_00, mat2_01, mat2_10, mat2_11] <;>
        simp
      norm_num
    have h_mz : star ⁅wittFMinus, pauliGamma1⁆ * ⁅wittFMinus, pauliGamma1⁆ = mat2 4 0 0 0 := by
      rw [Ring.lie_def, hwfm, hpg1]
      apply ext_mat2 <;>
        simp only [Matrix.sub_apply, mul2_00, mul2_01, mul2_10, mul2_11, Matrix.star_apply,
          mat2_00, mat2_01, mat2_10, mat2_11] <;>
        simp
      norm_num
    rw [h_pz, h_mz, trace_fin2]
    simp only [gibbsDensityC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, mat2_00, mat2_01, mat2_10, mat2_11, mul_zero,
      add_zero, zero_add]
    dsimp [ratePlus, rateMinus, boltzmannPlus, boltzmannMinus]
    push_cast; ring_nf
  exact ⟨h_car, h_gksl, h_kms, h_unital, h_cdc_id, h_cdc_sx, h_dx, h_dy, h_dz, h_gibbs_cdc⟩

/-!
### $Y_2$ & Rung 2: Full 3D Bloch Ball Manifold, Purity/Determinant Defect, and Forward Positivity Monoid $\mathbb{R}_{\ge 0}$
-/

/-- 3D Bloch density operator parameterization
$\rho(x, y, z) = \frac{1}{2}(I_2 + x\sigma_x + y\sigma_y + z\Gamma_1) \in M_2(\mathbb{C})$. -/
def blochState (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (x : ℂ) • pauliSigmaX +
      (y : ℂ) • pauliSigmaY + (z : ℂ) • pauliGamma1)

lemma blochState_selfAdjoint_trace_coords (x y z : ℝ) :
    IsSelfAdjoint (blochState x y z) ∧
    Matrix.trace (blochState x y z) = 1 ∧
    blochZ (blochState x y z) = z ∧
    coherenceSq (blochState x y z) = x ^ 2 + y ^ 2 ∧
    blochNormSq (blochState x y z) = x ^ 2 + y ^ 2 + z ^ 2 := by
  have h_sa : IsSelfAdjoint (blochState x y z) := by
    change star (blochState x y z) = blochState x y z
    apply ext_mat2 <;>
      simp [blochState, pauliSigmaX, pauliSigmaY, pauliGamma1_mat2, wittFPlus, wittFMinus,
        InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus,
        Matrix.star_apply] <;>
      ring_nf
  have h_tr : Matrix.trace (blochState x y z) = 1 := by
    rw [trace_fin2]
    simp [blochState, pauliSigmaX, pauliSigmaY, pauliGamma1_mat2, wittFPlus, wittFMinus,
      InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus]
    ring_nf
  have h_z : blochZ (blochState x y z) = z := by
    dsimp [blochZ]
    rw [trace_fin2, mul2_00, mul2_11]
    simp [blochState, pauliSigmaX, pauliSigmaY, pauliGamma1_mat2, wittFPlus, wittFMinus,
      InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus]
    ring_nf
  have h_coh : coherenceSq (blochState x y z) = x ^ 2 + y ^ 2 := by
    dsimp [coherenceSq]
    have h01 : blochState x y z 0 1 = (((x / 2 : ℝ) : ℂ) + ((-(y / 2) : ℝ) : ℂ) * Complex.I) := by
      simp [blochState, pauliSigmaX, pauliSigmaY, pauliGamma1_mat2, wittFPlus, wittFMinus,
        InfoGeometry.Algebra.FiniteSpin.J_plus, InfoGeometry.Algebra.FiniteSpin.J_minus]
      ring_nf
    rw [h01, Complex.normSq_add_mul_I]
    ring_nf
  have h_norm : blochNormSq (blochState x y z) = x ^ 2 + y ^ 2 + z ^ 2 := by
    rw [blochNormSq, h_z, h_coh]; ring_nf
  exact ⟨h_sa, h_tr, h_z, h_coh, h_norm⟩

lemma purity_defect_and_det_bloch {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) :
    (Matrix.trace (ρ * ρ - ρ)).re = -(1 - blochNormSq ρ) / 2 ∧
    (Matrix.det ρ).re = (1 - blochNormSq ρ) / 4 := by
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
  have h_norm : ρ 0 1 * star (ρ 0 1) = (Complex.normSq (ρ 0 1) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  have h_sq_re : ((ρ 0 1 * star (ρ 0 1) : ℂ)).re = coherenceSq ρ / 4 := by
    rw [h_norm, Complex.ofReal_re]
    dsimp [coherenceSq]; ring_nf
  have h_tr : (Matrix.trace (ρ * ρ - ρ)).re = -(1 - blochNormSq ρ) / 2 := by
    rw [Matrix.trace_sub, htr, Complex.sub_re, Complex.one_re, trace_fin2, mul2_00, mul2_11,
      h00, h11, h10, mul_comm (star (ρ 0 1)) (ρ 0 1)]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h_sq_re ⊢
    rw [h_sq_re]
    dsimp [blochNormSq]
    ring_nf
  have h_det : (Matrix.det ρ).re = (1 - blochNormSq ρ) / 4 := by
    rw [Matrix.det_fin_two, h00, h11, h10]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h_sq_re ⊢
    rw [h_sq_re]
    dsimp [blochNormSq]
    ring_nf
  exact ⟨h_tr, h_det⟩

-- theorem-class: conservation
/-- **$Y_2$ & Socratic Rung 2 (Forward-Only Positivity Monoid $\mathbb{R}_{\ge 0}$ vs. Backward Aporia)**:
For every $\gamma > 0$ and $\omega, \theta, t \in \mathbb{R}$:
1. If $t < 0$, the interior Bloch state $\rho_0 = \frac{1}{2}(I_2 + e^{\gamma t / 4}\sigma_x) \in \mathbb{B}^3$
   exits the Bloch ball under $T_t$, flipping purity defect $\operatorname{Re}\operatorname{Tr}(T_t(\rho_0)^2 - T_t(\rho_0)) > 0$
   and $\operatorname{Re}\det T_t(\rho_0) < 0$;
2. $T_t$ preserves the open Bloch ball $\mathbb{B}^3$ **if and only if** $t \ge 0$. -/
@[rep_depth transport]
theorem forward_monoid_positivity_iff_and_backward_aporia
    {γ : ℝ} (hγ : 0 < γ) (ω θ t : ℝ) :
    (t < 0 →
      let ρ₀ := blochState (Real.exp (γ * t / 4)) 0 0
      IsSelfAdjoint ρ₀ ∧
      Matrix.trace ρ₀ = 1 ∧
      blochNormSq ρ₀ < 1 ∧
      1 < blochNormSq (thermalSemigroupC γ ω θ t ρ₀) ∧
      0 < (Matrix.trace (thermalSemigroupC γ ω θ t ρ₀ * thermalSemigroupC γ ω θ t ρ₀ -
        thermalSemigroupC γ ω θ t ρ₀)).re ∧
      (Matrix.det (thermalSemigroupC γ ω θ t ρ₀)).re < 0) ∧
    ((∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      IsSelfAdjoint ρ → Matrix.trace ρ = 1 → blochNormSq ρ < 1 →
      blochNormSq (thermalSemigroupC γ ω θ t ρ) < 1) ↔ 0 ≤ t) := by
  have h_back : t < 0 →
      let ρ₀ := blochState (Real.exp (γ * t / 4)) 0 0
      IsSelfAdjoint ρ₀ ∧
      Matrix.trace ρ₀ = 1 ∧
      blochNormSq ρ₀ < 1 ∧
      1 < blochNormSq (thermalSemigroupC γ ω θ t ρ₀) ∧
      0 < (Matrix.trace (thermalSemigroupC γ ω θ t ρ₀ * thermalSemigroupC γ ω θ t ρ₀ -
        thermalSemigroupC γ ω θ t ρ₀)).re ∧
      (Matrix.det (thermalSemigroupC γ ω θ t ρ₀)).re < 0 := by
    intro ht ρ₀
    have h0 := blochState_selfAdjoint_trace_coords (Real.exp (γ * t / 4)) 0 0
    have h_norm0 : blochNormSq ρ₀ < 1 := by
      rw [h0.2.2.2.2]
      simpa using backward_exp_lt_one hγ ht
    have h_tc := thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t h0.1 h0.2.1
    have h_norm_t : 1 < blochNormSq (thermalSemigroupC γ ω θ t ρ₀) := by
      rw [blochNormSq, h_tc.2.2.1, h_tc.2.2.2, h0.2.2.2.1]
      simpa using backward_exp_gt_one (η := etaTraj γ θ (blochZ ρ₀) t) hγ ht
    have h_pd := purity_defect_and_det_bloch h_tc.1 h_tc.2.1
    have h_tr_pos : 0 < (Matrix.trace (thermalSemigroupC γ ω θ t ρ₀ * thermalSemigroupC γ ω θ t ρ₀ -
        thermalSemigroupC γ ω θ t ρ₀)).re := by
      rw [h_pd.1]
      have h1 : 0 < blochNormSq (thermalSemigroupC γ ω θ t ρ₀) - 1 := sub_pos.mpr h_norm_t
      have h2 : -(1 - blochNormSq (thermalSemigroupC γ ω θ t ρ₀)) / 2 =
          (blochNormSq (thermalSemigroupC γ ω θ t ρ₀) - 1) / 2 := by ring_nf
      rw [h2]
      exact div_pos h1 (by norm_num)
    have h_det_neg : (Matrix.det (thermalSemigroupC γ ω θ t ρ₀)).re < 0 := by
      rw [h_pd.2]
      exact div_neg_of_neg_of_pos (sub_neg.mpr h_norm_t) (by norm_num)
    exact ⟨h0.1, h0.2.1, h_norm0, h_norm_t, h_tr_pos, h_det_neg⟩
  refine ⟨h_back, ?_⟩
  constructor
  · intro h_all
    by_contra ht_neg
    have ht : t < 0 := lt_of_not_ge ht_neg
    have h_ex := h_back ht
    have h_lt := h_all _ h_ex.1 h_ex.2.1 h_ex.2.2.1
    exact (lt_asymm h_ex.2.2.2.1 h_lt).elim
  · intro ht ρ hsa htr hb
    exact (thermalSemigroupC_preserves_blochBall hγ ht hsa htr hb).2.2.2.1

/-!
### $Y_3$: Full 3D Spin Cumulant Potential $\Psi_3(\boldsymbol{\theta})$, Dual Negentropy $\Phi_3(\mathbf{r})$ & Diagonal Specialization
-/

/-- Euclidean 3D norm $\|\mathbf{v}\| = \sqrt{v_x^2 + v_y^2 + v_z^2}$. -/
noncomputable def vec3Norm (vx vy vz : ℝ) : ℝ :=
  Real.sqrt (vx ^ 2 + vy ^ 2 + vz ^ 2)

/-- Full 3D spin cumulant generating potential $\Psi_3(\boldsymbol{\theta}) = \log(e^{\|\boldsymbol{\theta}\|} + e^{-\|\boldsymbol{\theta}\|})$. -/
noncomputable def cumulantPsi3 (θx θy θz : ℝ) : ℝ :=
  cumulantPsi (vec3Norm θx θy θz)

/-- Full 3D Bloch negentropy $\Phi_3(\mathbf{r}) = \phi(\|\mathbf{r}\|)$. -/
noncomputable def negEntropyPhi3 (x y z : ℝ) : ℝ :=
  negEntropyPhi (vec3Norm x y z)

/-- 3D natural Legendre canonical coordinate $\boldsymbol{\theta}(\mathbf{r}) = \frac{\mathrm{artanh}(r)}{r}\mathbf{r}$ on $\mathbb{B}^3$. -/
noncomputable def blochNaturalTheta (x y z : ℝ) : ℝ × ℝ × ℝ :=
  let r := vec3Norm x y z
  if r = 0 then (0, 0, 0)
  else
    let k := canonicalTheta r / r
    (k * x, k * y, k * z)

/-- 3D Bloch expectation map $\nabla \Psi_3(\boldsymbol{\theta}) = \frac{\tanh\|\boldsymbol{\theta}\|}{\|\boldsymbol{\theta}\|}\boldsymbol{\theta}$. -/
noncomputable def blochExpectationFromTheta (θx θy θz : ℝ) : ℝ × ℝ × ℝ :=
  let th := vec3Norm θx θy θz
  if th = 0 then (0, 0, 0)
  else
    let s := meanSpin th / th
    (s * θx, s * θy, s * θz)

-- theorem-class: duality
/-- **Archetype $Y_3$: Full 3D Spin Cumulant Legendre Reciprocity & 1D Diagonal Specialization**:
1. Along the diagonal axis $(0, 0, \theta)$ and $(0, 0, z)$, $\Psi_3$ and $\Phi_3$ restrict identically
   to $\psi(\theta)$ and $\phi(z)$ (for all signs $\theta, z \in \mathbb{R}$);
2. On the entire 3D open Bloch ball $x^2 + y^2 + z^2 < 1$, `blochNaturalTheta` and `blochExpectationFromTheta`
   are mutual inverses and satisfy the 3D Fenchel–Young identity
   $\Psi_3(\boldsymbol{\theta}) + \Phi_3(\mathbf{r}) = \boldsymbol{\theta}\cdot\mathbf{r}$. -/
@[rep_depth thermo]
theorem bloch3D_cumulant_legendre_and_diagonal_specialization :
    (∀ θ z : ℝ, cumulantPsi3 0 0 θ = cumulantPsi θ ∧ negEntropyPhi3 0 0 z = negEntropyPhi z) ∧
    (∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 < 1 →
      let th := blochNaturalTheta x y z
      cumulantPsi3 th.1 th.2.1 th.2.2 + negEntropyPhi3 x y z =
        th.1 * x + th.2.1 * y + th.2.2 * z ∧
      blochExpectationFromTheta th.1 th.2.1 th.2.2 = (x, y, z)) ∧
    (∀ θx θy θz : ℝ,
      let rvec := blochExpectationFromTheta θx θy θz
      rvec.1 ^ 2 + rvec.2.1 ^ 2 + rvec.2.2 ^ 2 < 1 ∧
      blochNaturalTheta rvec.1 rvec.2.1 rvec.2.2 = (θx, θy, θz)) := by
  have h_vec_zero : ∀ a b c : ℝ, vec3Norm a b c = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
    intro a b c h
    dsimp [vec3Norm] at h
    have hsq : a ^ 2 + b ^ 2 + c ^ 2 = 0 := by
      have := congrArg (fun t => t ^ 2) h
      rw [Real.sq_sqrt (by positivity), zero_pow (by norm_num)] at this
      exact this
    have ha : a = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c])
    have hb : b = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c])
    have hc : c = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c])
    exact ⟨ha, hb, hc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro θ z
    have hv : ∀ t : ℝ, vec3Norm 0 0 t = |t| := fun t => by
      dsimp [vec3Norm]
      simp [Real.sqrt_sq_eq_abs]
    constructor
    · dsimp [cumulantPsi3]; rw [hv]
      rcases le_total 0 θ with hnn | hnp
      · rw [abs_of_nonneg hnn]
      · rw [abs_of_nonpos hnp, cumulantPsi_even]
    · dsimp [negEntropyPhi3]; rw [hv]
      rcases le_total 0 z with hnn | hnp
      · rw [abs_of_nonneg hnn]
      · rw [abs_of_nonpos hnp, negEntropyPhi_even]
  · intro x y z hr2
    dsimp [blochNaturalTheta]
    by_cases hr0 : vec3Norm x y z = 0
    · rcases h_vec_zero x y z hr0 with ⟨rfl, rfl, rfl⟩
      constructor
      · simp only [vec3Norm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
          Real.sqrt_zero, ↓reduceIte, cumulantPsi3, negEntropyPhi3, mul_zero]
        have hpsi0 : cumulantPsi 0 = Real.log 2 := by
          dsimp [cumulantPsi, partitionZ]; norm_num
        have hphi0 : negEntropyPhi 0 = -Real.log 2 := by
          dsimp [negEntropyPhi]
          rw [show (1 + (0 : ℝ)) / 2 = (2 : ℝ)⁻¹ by norm_num,
            show (1 - (0 : ℝ)) / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
          ring
        rw [hpsi0, hphi0]; ring
      · simp [blochExpectationFromTheta, vec3Norm]
    · set r := vec3Norm x y z
      have hr_pos : 0 < r := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr0)
      have hr_lt : r < 1 := by
        dsimp [r, vec3Norm]
        rw [Real.sqrt_lt' zero_lt_one, one_pow]
        exact hr2
      have hct_pos : 0 < canonicalTheta r := canonicalTheta_pos_of_pos hr_pos hr_lt
      set k := canonicalTheta r / r
      have hk_pos : 0 < k := div_pos hct_pos hr_pos
      have h_th_norm : vec3Norm (k * x) (k * y) (k * z) = canonicalTheta r := by
        dsimp [vec3Norm]
        have h_sq_id : (k * x) ^ 2 + (k * y) ^ 2 + (k * z) ^ 2 = (canonicalTheta r) ^ 2 := by
          have hrsq : r ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
          have h_expand : (k * x) ^ 2 + (k * y) ^ 2 + (k * z) ^ 2 = k ^ 2 * r ^ 2 := by
            rw [hrsq]; ring
          rw [h_expand]
          dsimp [k]; field_simp [ne_of_gt hr_pos]
        rw [h_sq_id, Real.sqrt_sq (le_of_lt hct_pos)]
      have h_m_eq : meanSpin (canonicalTheta r) = r :=
        dually_flat_legendre_reciprocity_and_metric_inversion.2.1 r (by linarith) hr_lt
      have h_fy := dually_flat_legendre_reciprocity_and_metric_inversion.2.2.1 (canonicalTheta r)
      rw [h_m_eq] at h_fy
      have h_th_ne : vec3Norm (k * x) (k * y) (k * z) ≠ 0 := by
        rw [h_th_norm]; exact ne_of_gt hct_pos
      simp only [hr0, ↓reduceIte]
      constructor
      · dsimp [cumulantPsi3, negEntropyPhi3]
        rw [h_th_norm]
        change cumulantPsi (canonicalTheta r) + negEntropyPhi r =
          k * x * x + k * y * y + k * z * z
        rw [h_fy]
        have hrsq : r ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)
        have : k * x * x + k * y * y + k * z * z = k * r ^ 2 := by rw [hrsq]; ring
        rw [this]; dsimp [k]; field_simp [ne_of_gt hr_pos]
      · dsimp [blochExpectationFromTheta]
        simp only [h_th_ne, ↓reduceIte]
        rw [h_th_norm, h_m_eq]
        have h_prod : (r / canonicalTheta r) * (canonicalTheta r / r) = 1 := by
          field_simp [ne_of_gt hr_pos, ne_of_gt hct_pos]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · calc (r / canonicalTheta r) * (k * x) = ((r / canonicalTheta r) * k) * x := by ring
            _ = x := by rw [show (r / canonicalTheta r) * k = 1 by dsimp [k]; exact h_prod, one_mul]
        · calc (r / canonicalTheta r) * (k * y) = ((r / canonicalTheta r) * k) * y := by ring
            _ = y := by rw [show (r / canonicalTheta r) * k = 1 by dsimp [k]; exact h_prod, one_mul]
        · calc (r / canonicalTheta r) * (k * z) = ((r / canonicalTheta r) * k) * z := by ring
            _ = z := by rw [show (r / canonicalTheta r) * k = 1 by dsimp [k]; exact h_prod, one_mul]
  · intro θx θy θz
    dsimp [blochExpectationFromTheta]
    by_cases hth0 : vec3Norm θx θy θz = 0
    · rcases h_vec_zero θx θy θz hth0 with ⟨rfl, rfl, rfl⟩
      simp [blochNaturalTheta, vec3Norm]
    · set th := vec3Norm θx θy θz
      have hth_pos : 0 < th := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hth0)
      have hm_pos : 0 < meanSpin th := meanSpin_pos_of_pos hth_pos
      have hm_bounds := meanSpin_mem_Ioo th
      set s := meanSpin th / th
      have h_r_norm : vec3Norm (s * θx) (s * θy) (s * θz) = meanSpin th := by
        dsimp [vec3Norm]
        have h_sq_id : (s * θx) ^ 2 + (s * θy) ^ 2 + (s * θz) ^ 2 = (meanSpin th) ^ 2 := by
          have hthsq : th ^ 2 = θx ^ 2 + θy ^ 2 + θz ^ 2 := Real.sq_sqrt (by positivity)
          have h_expand : (s * θx) ^ 2 + (s * θy) ^ 2 + (s * θz) ^ 2 = s ^ 2 * th ^ 2 := by
            rw [hthsq]; ring
          rw [h_expand]; dsimp [s]; field_simp [ne_of_gt hth_pos]
        rw [h_sq_id, Real.sqrt_sq (le_of_lt hm_pos)]
      have h_r2 : (s * θx) ^ 2 + (s * θy) ^ 2 + (s * θz) ^ 2 < 1 := by
        have hsq_eq : (vec3Norm (s * θx) (s * θy) (s * θz)) ^ 2 =
            (s * θx) ^ 2 + (s * θy) ^ 2 + (s * θz) ^ 2 := Real.sq_sqrt (by positivity)
        rw [h_r_norm] at hsq_eq
        rw [← hsq_eq]
        nlinarith [hm_bounds.1, hm_bounds.2]
      have hr_ne : vec3Norm (s * θx) (s * θy) (s * θz) ≠ 0 := by
        rw [h_r_norm]; exact ne_of_gt hm_pos
      have h_cth : canonicalTheta (meanSpin th) = th :=
        dually_flat_legendre_reciprocity_and_metric_inversion.1 th
      simp only [hth0, ↓reduceIte]
      refine ⟨h_r2, ?_⟩
      dsimp [blochNaturalTheta]
      simp only [hr_ne, ↓reduceIte]
      rw [h_r_norm, h_cth]
      have h_prod : (th / meanSpin th) * (meanSpin th / th) = 1 := by
        field_simp [ne_of_gt hth_pos, ne_of_gt hm_pos]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · calc (th / meanSpin th) * (s * θx) = ((th / meanSpin th) * s) * θx := by ring
          _ = θx := by rw [show (th / meanSpin th) * s = 1 by dsimp [s]; exact h_prod, one_mul]
      · calc (th / meanSpin th) * (s * θy) = ((th / meanSpin th) * s) * θy := by ring
          _ = θy := by rw [show (th / meanSpin th) * s = 1 by dsimp [s]; exact h_prod, one_mul]
      · calc (th / meanSpin th) * (s * θz) = ((th / meanSpin th) * s) * θz := by ring
          _ = θz := by rw [show (th / meanSpin th) * s = 1 by dsimp [s]; exact h_prod, one_mul]

/-!
### $Y_4$–$Y_9$ & Rungs 3–4: Diagonal Pinching, Larmor Vorticity, Quantum Jeffreys, & Exact Coherence-Corrected Spohn Law
-/

/-- Diagonal Cartan pinching channel
$\Delta_{\mathrm{pinch}}(\rho) = \frac{1}{2}(\rho + \Gamma_1 \rho \Gamma_1)$. -/
def diagPinch (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • (ρ + pauliGamma1 * ρ * pauliGamma1)

lemma diagPinch_eq_mat2 (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    diagPinch ρ = mat2 (ρ 0 0) 0 0 (ρ 1 1) := by
  apply ext_mat2 <;>
    simp [diagPinch, pauliGamma1_mat2] <;>
    ring_nf

private lemma blochZ_gibbsDensityC (θ : ℝ) : blochZ (gibbsDensityC θ) = meanSpin θ := by
  dsimp [blochZ]
  rw [trace_fin2, mul2_00, mul2_11, pauliGamma1_mat2]
  simp only [gibbsDensityC, mat2_00, mat2_01, mat2_10, mat2_11,
    boltzmannPlus, boltzmannMinus, mul_one, mul_zero, add_zero, zero_add, mul_neg,
    Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  ring_nf

-- theorem-class: divergence
/-- **Archetype $Y_4$ & Socratic Rung 3 (Pinching Idempotence, Kernel Orthogonality & Operator `umegakiKernel` Pythagoras)**:
1. `diagPinch` is an idempotent projector whose complement $\rho - \Delta_{\mathrm{pinch}}(\rho)$ is
   supported purely on the Witt ladders $F_\pm$, strictly non-identity on $\sigma_x$;
2. On $\mathbb{B}^3$, $\Delta_{\mathrm{pinch}}(\rho) = \rho_{\mathrm{Gibbs}}(\theta(z))$ is strictly positive;
3. $\operatorname{Tr}((\rho - \Delta_{\mathrm{pinch}}(\rho))(\log\Delta_{\mathrm{pinch}}(\rho) - \log\rho_{\mathrm{Gibbs}}(\theta))) = 0$;
4. Both summands of $D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) = D_{\mathrm{Umegaki}}(\rho \| \Delta_{\mathrm{pinch}}(\rho)) + D_{\mathrm{Umegaki}}(\Delta_{\mathrm{pinch}}(\rho) \| \rho_\theta)$
   hold directly via `umegakiKernel`, equal respectively to `coherenceRelEntropy ρ` and `bregmanPhi (blochZ ρ) (meanSpin θ)`. -/
@[rep_depth thermo]
theorem pinching_idempotence_orthogonality_and_operator_pythagoras
    {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) (θ : ℝ) :
    (diagPinch (diagPinch ρ) = diagPinch ρ ∧
      ρ - diagPinch ρ = ρ 0 1 • wittFPlus + ρ 1 0 • wittFMinus ∧
      (diagPinch ρ = ρ ↔ ρ 0 1 = 0 ∧ ρ 1 0 = 0) ∧
      diagPinch pauliSigmaX ≠ pauliSigmaX) ∧
    (diagPinch ρ = gibbsDensityC (canonicalTheta (blochZ ρ)) ∧
      IsStrictlyPositive (diagPinch ρ)) ∧
    Matrix.trace ((ρ - diagPinch ρ) * (CFC.log (diagPinch ρ) - CFC.log (gibbsDensityC θ))) = 0 ∧
    ((Matrix.trace (umegakiKernel ρ (diagPinch ρ))).re = coherenceRelEntropy ρ ∧
      (Matrix.trace (umegakiKernel (diagPinch ρ) (gibbsDensityC θ))).re =
        bregmanPhi (blochZ ρ) (meanSpin θ) ∧
      (Matrix.trace (umegakiKernel ρ (gibbsDensityC θ))).re =
        (Matrix.trace (umegakiKernel ρ (diagPinch ρ))).re +
        (Matrix.trace (umegakiKernel (diagPinch ρ) (gibbsDensityC θ))).re) := by
  have h_idem : diagPinch (diagPinch ρ) = diagPinch ρ := by
    rw [diagPinch_eq_mat2, diagPinch_eq_mat2]
    apply ext_mat2 <;> simp
  have h_offdiag : ρ - diagPinch ρ = ρ 0 1 • wittFPlus + ρ 1 0 • wittFMinus := by
    rw [diagPinch_eq_mat2]
    apply ext_mat2 <;>
      simp [wittFPlus, wittFMinus, InfoGeometry.Algebra.FiniteSpin.J_plus,
        InfoGeometry.Algebra.FiniteSpin.J_minus]
  have h_iff_diag : diagPinch ρ = ρ ↔ ρ 0 1 = 0 ∧ ρ 1 0 = 0 := by
    rw [diagPinch_eq_mat2]
    constructor
    · intro h
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
      have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
      simp at h01 h10
      exact ⟨h01.symm, h10.symm⟩
    · intro h
      apply ext_mat2 <;> simp [h.1, h.2]
  have h_not_sx : diagPinch pauliSigmaX ≠ pauliSigmaX := by
    intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    rw [diagPinch_eq_mat2] at h01
    simp [pauliSigmaX, wittFPlus, wittFMinus, InfoGeometry.Algebra.FiniteSpin.J_plus,
      InfoGeometry.Algebra.FiniteSpin.J_minus] at h01
  set θ_z := canonicalTheta (blochZ ρ)
  have hz_bounds := blochZ_abs_lt_one hb
  have hm_z : meanSpin θ_z = blochZ ρ :=
    dually_flat_legendre_reciprocity_and_metric_inversion.2.1 (blochZ ρ) hz_bounds.1 hz_bounds.2
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, _, _⟩
  have h_pinch_gibbs : diagPinch ρ = gibbsDensityC θ_z := by
    rw [diagPinch_eq_mat2]
    apply ext_mat2 <;>
      simp [gibbsDensityC, boltzmannPlus, boltzmannMinus, hm_z, h00, h11]
  have h_pinch_pos : IsStrictlyPositive (diagPinch ρ) := by
    rw [h_pinch_gibbs]
    exact (gibbsDensityC_strictlyPositive_and_cfc_log θ_z).1
  have h_orth :
      Matrix.trace ((ρ - diagPinch ρ) * (CFC.log (diagPinch ρ) - CFC.log (gibbsDensityC θ))) = 0 := by
    have h_log_pz := (gibbsDensityC_strictlyPositive_and_cfc_log θ_z).2
    have h_log_g := (gibbsDensityC_strictlyPositive_and_cfc_log θ).2
    rw [h_offdiag, h_pinch_gibbs, h_log_pz, h_log_g, trace_fin2, mul2_00, mul2_11]
    simp [pauliGamma1_mat2, wittFPlus, wittFMinus, InfoGeometry.Algebra.FiniteSpin.J_plus,
      InfoGeometry.Algebra.FiniteSpin.J_minus]
  have h_coh_umegaki : (Matrix.trace (umegakiKernel ρ (diagPinch ρ))).re = coherenceRelEntropy ρ := by
    rw [h_pinch_gibbs]
    have h_pyth := (umegakiKernel_trace_and_coherence_pythagoras hsa htr hb θ_z).2.1
    have h_breg_z : bregmanPhi (blochZ ρ) (meanSpin θ_z) = 0 := by
      rw [hm_z]
      exact (bregman_umegaki_positivity_and_pythagorean_theorem.2.1
        (blochZ ρ) (blochZ ρ) hz_bounds.1 hz_bounds.2 hz_bounds.1 hz_bounds.2).2.mpr rfl
    change quantumUmegakiGibbs ρ θ_z = coherenceRelEntropy ρ
    rw [h_pyth, h_breg_z, add_zero]
  have h_pinch_sa : IsSelfAdjoint (gibbsDensityC θ_z) := by
    change star (gibbsDensityC θ_z) = gibbsDensityC θ_z
    apply ext_mat2 <;> simp [gibbsDensityC, Matrix.star_apply, Complex.conj_ofReal]
  have h_pinch_tr : Matrix.trace (gibbsDensityC θ_z) = 1 := by
    rw [trace_fin2]
    simp [gibbsDensityC, boltzmannPlus, boltzmannMinus]; ring_nf
  have h_pinch_z : blochZ (gibbsDensityC θ_z) = blochZ ρ := by
    rw [blochZ_gibbsDensityC, hm_z]
  have h_pinch_norm : blochNormSq (gibbsDensityC θ_z) < 1 := by
    have h01 : gibbsDensityC θ_z 0 1 = 0 := rfl
    dsimp [blochNormSq, coherenceSq]
    rw [h_pinch_z, h01, Complex.normSq_zero, mul_zero, add_zero]
    exact sq_lt_one_of_Ioo hz_bounds.1 hz_bounds.2
  have h_pop_umegaki :
      (Matrix.trace (umegakiKernel (diagPinch ρ) (gibbsDensityC θ))).re =
        bregmanPhi (blochZ ρ) (meanSpin θ) := by
    rw [h_pinch_gibbs]
    have h_p2 := umegakiKernel_trace_and_coherence_pythagoras h_pinch_sa h_pinch_tr h_pinch_norm θ
    have h_c0 : coherenceRelEntropy (gibbsDensityC θ_z) = 0 := h_p2.2.2.1.2.mpr rfl
    change quantumUmegakiGibbs (gibbsDensityC θ_z) θ = bregmanPhi (blochZ ρ) (meanSpin θ)
    rw [h_p2.2.1, h_c0, zero_add, h_pinch_z]
  have h_sum :
      (Matrix.trace (umegakiKernel ρ (gibbsDensityC θ))).re =
        (Matrix.trace (umegakiKernel ρ (diagPinch ρ))).re +
        (Matrix.trace (umegakiKernel (diagPinch ρ) (gibbsDensityC θ))).re := by
    rw [h_coh_umegaki, h_pop_umegaki]
    exact (umegakiKernel_trace_and_coherence_pythagoras hsa htr hb θ).2.1
  exact ⟨⟨h_idem, h_offdiag, h_iff_diag, h_not_sx⟩, ⟨h_pinch_gibbs, h_pinch_pos⟩,
    h_orth, ⟨h_coh_umegaki, h_pop_umegaki, h_sum⟩⟩

/-- Predicate expressing that the forward relaxation curve $t \mapsto T_t(\rho)$ moves
along a straight affine $m$-geodesic segment in $M_2(\mathbb{C})$ toward $\rho_{\mathrm{Gibbs}}(\theta)$. -/
def IsAffineMGeodesicToGibbs (γ ω θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ lam : ℝ → ℝ, ∀ t : ℝ, 0 ≤ t →
    thermalSemigroupC γ ω θ t ρ - gibbsDensityC θ = (lam t : ℂ) • (ρ - gibbsDensityC θ)

private lemma cfc_log_eq_affine_of_pos
    {σ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint σ) (htr : Matrix.trace σ = 1)
    (hr_pos : 0 < blochRadius σ) (hb : blochNormSq σ < 1) :
    CFC.log σ =
      (((Real.log ((1 + blochRadius σ) / 2) + Real.log ((1 - blochRadius σ) / 2)) / 2 -
          canonicalTheta (blochRadius σ) / blochRadius σ : ℝ) : ℂ) •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((2 * canonicalTheta (blochRadius σ) / blochRadius σ : ℝ) : ℂ) • σ := by
  set r := blochRadius σ
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_lt : r < 1 := blochRadius_lt_one hb
  have hlp_pos : 0 < (1 + r) / 2 := by linarith
  have hlm_pos : 0 < (1 - r) / 2 := by linarith
  have h_log_r : Real.log ((1 + r) / 2) - Real.log ((1 - r) / 2) = 2 * canonicalTheta r := by
    rw [← Real.log_div (ne_of_gt hlp_pos) (ne_of_gt hlm_pos)]
    have h_div : ((1 + r) / 2) / ((1 - r) / 2) = (1 + r) / (1 - r) := by field_simp
    rw [h_div]; dsimp [canonicalTheta]; ring
  have h_lp_eq : Real.log ((1 + r) / 2) = Real.log ((1 - r) / 2) + 2 * canonicalTheta r := by
    linarith [h_log_r]
  have hlogσ := (spectralProjector_twoSheet_and_cfc_log hsa htr hb).2.2.2.2
  have hP_def : spectralProjector σ =
      r⁻¹ • (σ - ((1 - r) / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    simp [spectralProjector, r, hr_ne]
  have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_ne
  rw [hlogσ, hP_def, twoSheet_affine, h_log_r, h_lp_eq]
  dsimp only [r] at hr_c ⊢
  apply ext_mat2 <;>
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Complex.real_smul, smul_eq_mul, Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte] <;>
    push_cast <;> field_simp [hr_c] <;> ring_nf

-- theorem-class: symmetry
/-- **Archetype $Y_5$ & Socratic Rung 4 (Larmor Equipotential Orthogonality & Affine $m$-Geodesic Characterization)**:
For $\gamma > 0$ and any open-Bloch-ball state $\rho \in \mathbb{B}^3$:
1. *Equipotential Larmor Orthogonality*: $\operatorname{Tr}\!\big((-\frac{i\omega}{2}[\Gamma_1, \rho])(\log\rho - \log\rho_\theta)\big) = 0$;
2. *Parabolic Envelope*: $(z(T_t(\rho)) - \eta_\theta) c(\rho) = (z(\rho) - \eta_\theta) c(T_t(\rho))$ for all $t$;
3. *Exact $m$-Geodesic Aporia*: $T_t(\rho)$ traces an affine $m$-geodesic segment toward $\rho_\theta$ in
   $M_2(\mathbb{C})$ **if and only if** either $\rho_{01} = 0$ (classical diagonal relaxation) or
   $(z(\rho) = \eta_\theta \land \omega = 0)$ (purely dephasing equatorial ray without Larmor rotation). -/
@[rep_depth transport]
theorem larmor_equipotential_orthogonality_and_affine_m_geodesic_iff
    {γ : ℝ} (hγ : 0 < γ) (ω θ : ℝ) {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) :
    Matrix.trace ((-(Complex.I * (ω : ℂ) / 2) • ⁅pauliGamma1, ρ⁆) *
      (CFC.log ρ - CFC.log (gibbsDensityC θ))) = 0 ∧
    (∀ t : ℝ, (blochZ (thermalSemigroupC γ ω θ t ρ) - meanSpin θ) * coherenceSq ρ =
      (blochZ ρ - meanSpin θ) * coherenceSq (thermalSemigroupC γ ω θ t ρ)) ∧
    (IsAffineMGeodesicToGibbs γ ω θ ρ ↔
      (ρ 0 1 = 0 ∨ (blochZ ρ = meanSpin θ ∧ ω = 0))) := by
  have h_larmor_orth :
      Matrix.trace ((-(Complex.I * (ω : ℂ) / 2) • ⁅pauliGamma1, ρ⁆) *
        (CFC.log ρ - CFC.log (gibbsDensityC θ))) = 0 := by
    have h_comm_right : ∀ A B C : Matrix (Fin 2) (Fin 2) ℂ, B * C = C * B →
        Matrix.trace (⁅A, B⁆ * C) = 0 := by
      intro A B C hBC
      rw [Ring.lie_def, sub_mul, Matrix.trace_sub, Matrix.mul_assoc A B C, hBC,
        ← Matrix.mul_assoc A C B, Matrix.trace_mul_comm (A * C) B,
        ← Matrix.mul_assoc B A C, sub_self]
    have h_comm_left : ∀ A B C : Matrix (Fin 2) (Fin 2) ℂ, A * C = C * A →
        Matrix.trace (⁅A, B⁆ * C) = 0 := by
      intro A B C hAC
      rw [Ring.lie_def, sub_mul, Matrix.trace_sub, Matrix.mul_assoc, Matrix.trace_mul_comm A (B * C),
        Matrix.mul_assoc, Matrix.mul_assoc, ← hAC, ← Matrix.mul_assoc B A C, sub_self]
    have h_rho_log : ρ * CFC.log ρ = CFC.log ρ * ρ := by
      rcases spectralProjector_twoSheet_and_cfc_log hsa htr hb with ⟨hP, _, h2s, _, hlogρ⟩
      calc ρ * CFC.log ρ
        _ = twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) *
              twoSheet (spectralProjector ρ) (Real.log ((1 + blochRadius ρ) / 2))
                (Real.log ((1 - blochRadius ρ) / 2)) := by rw [h2s, hlogρ]
        _ = twoSheet (spectralProjector ρ)
              (((1 + blochRadius ρ) / 2) * Real.log ((1 + blochRadius ρ) / 2))
              (((1 - blochRadius ρ) / 2) * Real.log ((1 - blochRadius ρ) / 2)) :=
            twoSheet_mul _ hP.isIdempotentElem.eq _ _ _ _
        _ = twoSheet (spectralProjector ρ)
              (Real.log ((1 + blochRadius ρ) / 2) * ((1 + blochRadius ρ) / 2))
              (Real.log ((1 - blochRadius ρ) / 2) * ((1 - blochRadius ρ) / 2)) := by
            rw [mul_comm ((1 + blochRadius ρ) / 2), mul_comm ((1 - blochRadius ρ) / 2)]
        _ = twoSheet (spectralProjector ρ) (Real.log ((1 + blochRadius ρ) / 2))
              (Real.log ((1 - blochRadius ρ) / 2)) *
              twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) :=
            (twoSheet_mul _ hP.isIdempotentElem.eq _ _ _ _).symm
        _ = CFC.log ρ * ρ := by rw [← hlogρ, h2s]
    have h_pg_logG : pauliGamma1 * CFC.log (gibbsDensityC θ) =
        CFC.log (gibbsDensityC θ) * pauliGamma1 := by
      rw [(gibbsDensityC_strictlyPositive_and_cfc_log θ).2]
      apply ext_mat2 <;> simp [pauliGamma1_mat2]
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_sub, Matrix.trace_sub,
      h_comm_right pauliGamma1 ρ (CFC.log ρ) h_rho_log,
      h_comm_left pauliGamma1 ρ (CFC.log (gibbsDensityC θ)) h_pg_logG,
      sub_zero, mul_zero]
  have h_parabola : ∀ t : ℝ,
      (blochZ (thermalSemigroupC γ ω θ t ρ) - meanSpin θ) * coherenceSq ρ =
        (blochZ ρ - meanSpin θ) * coherenceSq (thermalSemigroupC γ ω θ t ρ) := by
    intro t
    have h_tc := thermalSemigroupC_selfAdjoint_trace_coherence γ ω θ t hsa htr
    rw [h_tc.2.2.1, h_tc.2.2.2]
    dsimp [etaTraj]
    ring_nf
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
  have h_tr_c : ρ 0 0 + ρ 1 1 = 1 := by rw [trace_fin2] at htr; exact htr
  have h_geod_iff : IsAffineMGeodesicToGibbs γ ω θ ρ ↔
      (ρ 0 1 = 0 ∨ (blochZ ρ = meanSpin θ ∧ ω = 0)) := by
    constructor
    · rintro ⟨lam, hlam⟩
      by_cases h01 : ρ 0 1 = 0
      · exact Or.inl h01
      · right
        have hω : ω = 0 := by
          by_contra hω_ne
          set t₀ : ℝ := Real.pi / (2 * |ω|)
          have habs_pos : 0 < |ω| := abs_pos.mpr hω_ne
          have ht₀_pos : 0 < t₀ := div_pos Real.pi_pos (mul_pos (by norm_num) habs_pos)
          have h_at_t₀ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1)
            (hlam t₀ (le_of_lt ht₀_pos))
          simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_01, gibbsDensityC, mat2_01, sub_zero] at h_at_t₀
          have h_cancel : ((Real.exp (-(γ / 2) * t₀) : ℂ) *
              Complex.exp (-Complex.I * (ω : ℂ) * (t₀ : ℂ))) = (lam t₀ : ℂ) :=
            mul_right_cancel₀ h01 h_at_t₀
          have h_im := congrArg Complex.im h_cancel
          have h_arg : -Complex.I * (ω : ℂ) * (t₀ : ℂ) = ((-(ω * t₀) : ℝ) : ℂ) * Complex.I := by
            push_cast; ring_nf
          rw [h_arg, Complex.exp_ofReal_mul_I] at h_im
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
            Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_mul,
            zero_add, Real.sin_neg] at h_im
          have h_exp_ne : Real.exp (-(γ / 2) * t₀) ≠ 0 := ne_of_gt (Real.exp_pos _)
          have h_sin_neg : -Real.sin (ω * t₀) = 0 := by
            have := mul_eq_zero.mp h_im
            rcases this with h0 | hsin
            · exact absurd h0 h_exp_ne
            · exact hsin
          have h_sin0 : Real.sin (ω * t₀) = 0 := neg_eq_zero.mp h_sin_neg
          rcases lt_or_gt_of_ne hω_ne with hω_neg | hω_pos
          · have hwt : ω * t₀ = -(Real.pi / 2) := by
              dsimp [t₀]
              rw [abs_of_neg hω_neg]
              field_simp [hω_ne]
            rw [hwt, Real.sin_neg, Real.sin_pi_div_two] at h_sin0
            norm_num at h_sin0
          · have hwt : ω * t₀ = Real.pi / 2 := by
              dsimp [t₀]
              rw [abs_of_pos hω_pos]
              field_simp [hω_ne]
            rw [hwt, Real.sin_pi_div_two] at h_sin0
            norm_num at h_sin0
        have h_at_1_01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) (hlam 1 zero_le_one)
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_01, gibbsDensityC, mat2_01, sub_zero, hω, Complex.ofReal_zero,
          mul_zero, zero_mul, Complex.exp_zero, mul_one] at h_at_1_01
        have h_lam1_c : (Real.exp (-(γ / 2)) : ℂ) = (lam 1 : ℂ) :=
          mul_right_cancel₀ h01 h_at_1_01
        have h_lam1 : lam 1 = Real.exp (-(γ / 2)) :=
          (Complex.ofReal_injective h_lam1_c).symm
        have h_at_1_00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (hlam 1 zero_le_one)
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          thermalSemigroupC_00, h_tr_c, mul_one, gibbsDensityC, mat2_00, h_lam1] at h_at_1_00
        have h_lhs_00 :
            (boltzmannPlus θ : ℂ) + (Real.exp (-γ) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ)) -
              (boltzmannPlus θ : ℂ) =
              (Real.exp (-γ) : ℂ) * (ρ 0 0 - (boltzmannPlus θ : ℂ)) := by
          abel
        rw [h_lhs_00] at h_at_1_00
        have h_re_00 := congrArg Complex.re h_at_1_00
        rw [h00] at h_re_00
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
          zero_mul, sub_zero] at h_re_00
        have h_diff_0 : (Real.exp (-γ) - Real.exp (-(γ / 2))) *
            ((1 + blochZ ρ) / 2 - boltzmannPlus θ) = 0 := by
          have := sub_eq_zero.mpr h_re_00
          dsimp [boltzmannPlus] at this ⊢
          linear_combination this
        have h_exp_diff_ne : Real.exp (-γ) - Real.exp (-(γ / 2)) ≠ 0 :=
          sub_ne_zero.mpr (exp_neg_half_ne_exp_neg hγ)
        have h_bp_eq : (1 + blochZ ρ) / 2 - boltzmannPlus θ = 0 :=
          (mul_eq_zero.mp h_diff_0).resolve_left h_exp_diff_ne
        have hz_eq : blochZ ρ = meanSpin θ := by
          dsimp [boltzmannPlus] at h_bp_eq
          linear_combination 2 * h_bp_eq
        exact ⟨hz_eq, hω⟩
    · rintro (h01 | ⟨hz_eq, hω⟩)
      · refine ⟨fun t => Real.exp (-γ * t), fun t _ => ?_⟩
        have h10_zero : ρ 1 0 = 0 := by rw [h10, h01, star_zero]
        apply ext_mat2
        · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_00, h_tr_c, mul_one, gibbsDensityC, mat2_00]
          abel
        · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_01, gibbsDensityC, mat2_01, h01, mul_zero, sub_zero]
        · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_10, gibbsDensityC, mat2_10, h10_zero, mul_zero, sub_zero]
        · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_11, h_tr_c, mul_one, gibbsDensityC, mat2_11]
          abel
      · refine ⟨fun t => Real.exp (-(γ / 2) * t), fun t _ => ?_⟩
        have h00_eq : ρ 0 0 = (boltzmannPlus θ : ℂ) := by
          rw [h00]; dsimp [boltzmannPlus]; rw [hz_eq]
        have h11_eq : ρ 1 1 = (boltzmannMinus θ : ℂ) := by
          rw [h11]; dsimp [boltzmannMinus]; rw [hz_eq]
        apply ext_mat2
        · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_00, h_tr_c, mul_one, gibbsDensityC, mat2_00]
          rw [h00_eq]
          simp only [sub_self, mul_zero, add_zero]
        · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_01, gibbsDensityC, mat2_01, hω, Complex.ofReal_zero, mul_zero,
            zero_mul, Complex.exp_zero, mul_one, sub_zero]
        · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_10, gibbsDensityC, mat2_10, hω, Complex.ofReal_zero, mul_zero,
            zero_mul, Complex.exp_zero, mul_one, sub_zero]
        · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
            thermalSemigroupC_11, h_tr_c, mul_one, gibbsDensityC, mat2_11]
          rw [h11_eq]
          simp only [sub_self, mul_zero, add_zero]
  exact ⟨h_larmor_orth, h_parabola, h_geod_iff⟩

/-- Operator-level symmetrized quantum Jeffreys divergence
$J_{\mathrm{Umegaki}}(\rho, \rho_\theta) = D_{\mathrm{Umegaki}}(\rho \| \rho_\theta) + D_{\mathrm{Umegaki}}(\rho_\theta \| \rho)$
defined via `umegakiKernel`. -/
noncomputable def quantumJeffreysGibbs (ρ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) : ℝ :=
  (Matrix.trace (umegakiKernel ρ (gibbsDensityC θ))).re +
  (Matrix.trace (umegakiKernel (gibbsDensityC θ) ρ)).re

private lemma quantumJeffreysGibbs_eq_blochJeffreysTerm
    {σ : Matrix (Fin 2) (Fin 2) ℂ}
    (hsa : IsSelfAdjoint σ) (htr : Matrix.trace σ = 1) (hb : blochNormSq σ < 1) (θ : ℝ) :
    quantumJeffreysGibbs σ θ = blochJeffreysTerm θ σ := by
  have h_fwd := (umegakiKernel_trace_and_coherence_pythagoras hsa htr hb θ).1
  rcases gibbsDensityC_strictlyPositive_and_cfc_log θ with ⟨_, hlogG⟩
  rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, _, _⟩
  have h_tr_G : Matrix.trace (gibbsDensityC θ) = 1 := by
    rw [trace_fin2]
    simp [gibbsDensityC, boltzmannPlus, boltzmannMinus]
    ring_nf
  have h_tr_G_pg : Matrix.trace (gibbsDensityC θ * pauliGamma1) = (meanSpin θ : ℂ) := by
    rw [trace_fin2, mul2_00, mul2_11, gibbsDensityC, pauliGamma1_mat2]
    simp [boltzmannPlus, boltzmannMinus]
    ring_nf
  have h_tr_G_logG :
      Matrix.trace (gibbsDensityC θ * cfc Real.log (gibbsDensityC θ)) =
        ((θ * meanSpin θ - cumulantPsi θ : ℝ) : ℂ) := by
    change Matrix.trace (gibbsDensityC θ * CFC.log (gibbsDensityC θ)) = _
    rw [hlogG, mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul, h_tr_G_pg,
      Matrix.mul_smul, mul_one, Matrix.trace_smul, h_tr_G, smul_eq_mul, smul_eq_mul]
    push_cast; ring_nf
  by_cases hr0 : blochRadius σ = 0
  · have hbn0 : blochNormSq σ = 0 := by
      have hsq := blochRadius_sq σ
      rw [hr0] at hsq
      simpa using hsq.symm
    have hz0 : blochZ σ = 0 := by
      have hns : 0 ≤ coherenceSq σ := by
        dsimp [coherenceSq]; exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
      dsimp [blochNormSq] at hbn0
      exact sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (blochZ σ), hns])
    have hlogσ := (spectralProjector_twoSheet_and_cfc_log hsa htr hb).2.2.2.2
    have h_two_eq : CFC.log σ = (Real.log (1 / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [hlogσ, hr0]
      have ha1 : (1 + (0 : ℝ)) / 2 = (1 / 2 : ℝ) := by norm_num
      have ha2 : (1 - (0 : ℝ)) / 2 = (1 / 2 : ℝ) := by norm_num
      rw [add_zero, sub_zero, twoSheet_equal]
      apply ext_mat2 <;> simp [Complex.real_smul]
    have h_tr_G_logσ : Matrix.trace (gibbsDensityC θ * cfc Real.log σ) =
        ((Real.log (1 / 2) : ℝ) : ℂ) := by
      change Matrix.trace (gibbsDensityC θ * CFC.log σ) = _
      rw [h_two_eq, Matrix.mul_smul, mul_one, Matrix.trace_smul, h_tr_G, smul_eq_mul, mul_one]
    have h_phi0 : negEntropyPhi 0 = Real.log (1 / 2) := by
      dsimp [negEntropyPhi]
      norm_num; ring_nf
    rw [quantumJeffreysGibbs, h_fwd, umegakiKernel_apply, mul_sub, Matrix.trace_sub, h_tr_G_logG,
      h_tr_G_logσ]
    simp only [Complex.ofReal_re, Complex.sub_re]
    dsimp [blochJeffreysTerm]
    rw [hr0, hz0, h_phi0]
    simp only [mul_zero, zero_mul, sub_zero]
    ring_nf
  · have hr_pos : 0 < blochRadius σ := lt_of_le_of_ne (blochRadius_nonneg σ) (Ne.symm hr0)
    have hr_lt : blochRadius σ < 1 := blochRadius_lt_one hb
    have hr_lo : -1 < blochRadius σ := by linarith [hr_pos]
    have h_logσ_alg := cfc_log_eq_affine_of_pos hsa htr hr_pos hb
    have h_tr_G_σ : Matrix.trace (gibbsDensityC θ * σ) =
        (((1 + blochZ σ * meanSpin θ) / 2 : ℝ) : ℂ) := by
      rw [trace_fin2, mul2_00, mul2_11, gibbsDensityC, h00, h11]
      simp only [mat2_00, mat2_01, mat2_10, mat2_11, zero_mul, add_zero, zero_add]
      dsimp [boltzmannPlus, boltzmannMinus]
      push_cast; ring_nf
    have h_tr_G_logσ : Matrix.trace (gibbsDensityC θ * cfc Real.log σ) =
        ((((Real.log ((1 + blochRadius σ) / 2) + Real.log ((1 - blochRadius σ) / 2)) / 2 -
            canonicalTheta (blochRadius σ) / blochRadius σ) +
          (2 * canonicalTheta (blochRadius σ) / blochRadius σ) *
            ((1 + blochZ σ * meanSpin θ) / 2) : ℝ) : ℂ) := by
      change Matrix.trace (gibbsDensityC θ * CFC.log σ) = _
      rw [h_logσ_alg, mul_add, Matrix.trace_add, Matrix.mul_smul, mul_one, Matrix.trace_smul,
        h_tr_G, Matrix.mul_smul, Matrix.trace_smul, h_tr_G_σ, smul_eq_mul, smul_eq_mul, mul_one]
      push_cast; ring_nf
    rw [quantumJeffreysGibbs, h_fwd, umegakiKernel_apply, mul_sub, Matrix.trace_sub, h_tr_G_logG,
      h_tr_G_logσ]
    simp only [Complex.ofReal_re, Complex.sub_re]
    dsimp [blochJeffreysTerm]
    rw [← jeffreys_trace_combine_real (z := blochZ σ) (η := meanSpin θ) (θ := θ) hr_lo hr_lt hr0]
    ring_nf

-- theorem-class: conservation
/-- **Archetypes $Y_6$ & $Y_7$ (Quantum Jeffreys Identity, Factor-of-2 Coherent Overprediction & Strict Relaxation Characterization)**:
1. `quantumJeffreysGibbs σ θ = blochJeffreysTerm θ σ` identically on the open Bloch ball;
2. *Factor-of-2 Refutation Witness*: at $\theta = 0$ on a purely transverse coherent state
   $\rho_{\mathrm{coh}} = \frac{1}{2}(I_2 + r\sigma_x)$ ($0 < r < 1$), the classical Jeffreys rate
   $\gamma\,J_{\mathrm{Umegaki}}(\rho_{\mathrm{coh}}, I_2/2)$ strictly equals $2\,\sigma_{\mathrm{KMS}}$;
3. For $\gamma > 0$ and $0 < r(\sigma) < 1$: $\sigma_{\mathrm{KMS}}(\gamma,\theta,\sigma) = 0 \iff \sigma = \rho_{\mathrm{Gibbs}}(\theta)$,
   and $\sigma_{\mathrm{KMS}}(\gamma,\theta,\sigma) = \gamma\,J_{\mathrm{Umegaki}}(\sigma, \rho_\theta) \iff \sigma_{01} = 0$. -/
@[rep_depth thermo]
theorem symmetrized_umegaki_jeffreys_factor_two_and_diagonal_iff
    {γ : ℝ} (hγ : 0 < γ) (θ : ℝ) :
    (∀ σ : Matrix (Fin 2) (Fin 2) ℂ,
      IsSelfAdjoint σ → Matrix.trace σ = 1 → blochNormSq σ < 1 →
      quantumJeffreysGibbs σ θ = blochJeffreysTerm θ σ) ∧
    (∀ r : ℝ, 0 < r → r < 1 →
      let ρ_coh := blochState r 0 0
      quantumSpohnRate γ 0 ρ_coh = (γ / 2) * r * canonicalTheta r ∧
      γ * quantumJeffreysGibbs ρ_coh 0 = 2 * quantumSpohnRate γ 0 ρ_coh ∧
      0 < quantumSpohnRate γ 0 ρ_coh) ∧
    (∀ σ : Matrix (Fin 2) (Fin 2) ℂ,
      IsSelfAdjoint σ → Matrix.trace σ = 1 → 0 < blochRadius σ → blochNormSq σ < 1 →
      (quantumSpohnRate γ θ σ = 0 ↔ σ = gibbsDensityC θ) ∧
      (quantumSpohnRate γ θ σ = γ * quantumJeffreysGibbs σ θ ↔ σ 0 1 = 0)) := by
  have h_all_j : ∀ σ : Matrix (Fin 2) (Fin 2) ℂ,
      IsSelfAdjoint σ → Matrix.trace σ = 1 → blochNormSq σ < 1 →
      quantumJeffreysGibbs σ θ = blochJeffreysTerm θ σ :=
    fun _ hsa htr hb => quantumJeffreysGibbs_eq_blochJeffreysTerm hsa htr hb θ
  have h_fac2 : ∀ r : ℝ, 0 < r → r < 1 →
      let ρ_coh := blochState r 0 0
      quantumSpohnRate γ 0 ρ_coh = (γ / 2) * r * canonicalTheta r ∧
      γ * quantumJeffreysGibbs ρ_coh 0 = 2 * quantumSpohnRate γ 0 ρ_coh ∧
      0 < quantumSpohnRate γ 0 ρ_coh := by
    intro r hr0 hr1 ρ_coh
    have h0 := blochState_selfAdjoint_trace_coords r 0 0
    have h_norm_eq : blochNormSq ρ_coh = r ^ 2 := by rw [h0.2.2.2.2]; ring_nf
    have h_norm_lt : blochNormSq ρ_coh < 1 := by rw [h_norm_eq]; nlinarith [hr0, hr1]
    have h_rad : blochRadius ρ_coh = r := by
      dsimp [blochRadius]; rw [h_norm_eq, Real.sqrt_sq (le_of_lt hr0)]
    have h_coh : coherenceSq ρ_coh = r ^ 2 := by rw [h0.2.2.2.1]; ring_nf
    have h_mean0 : meanSpin 0 = 0 := by dsimp [meanSpin]; norm_num
    have h_rates := operator_spohn_rate_and_strict_coherent_dissipation
      (γ := γ) (ω := 0) (θ := 0) (σ := ρ_coh) hγ h0.1 h0.2.1
      (by rw [h_rad]; exact hr0) h_norm_lt
    have h_spohn_r : quantumSpohnRate γ 0 ρ_coh = (γ / 2) * r * canonicalTheta r := by
      rw [h_rates.2.1, h_rad, h0.2.2.1, h_mean0]
      have hr_ne : r ≠ 0 := ne_of_gt hr0
      field_simp [hr_ne]
      ring_nf
    have h_jef_r : quantumJeffreysGibbs ρ_coh 0 = r * canonicalTheta r := by
      rw [quantumJeffreysGibbs_eq_blochJeffreysTerm h0.1 h0.2.1 h_norm_lt 0]
      dsimp [blochJeffreysTerm]
      rw [h_rad, h0.2.2.1, h_mean0]
      have hr_ne : r ≠ 0 := ne_of_gt hr0
      field_simp [hr_ne]
      ring_nf
    have h_two : γ * quantumJeffreysGibbs ρ_coh 0 = 2 * quantumSpohnRate γ 0 ρ_coh := by
      rw [h_jef_r, h_spohn_r]; ring_nf
    have h_pos : 0 < quantumSpohnRate γ 0 ρ_coh := by
      rw [h_spohn_r]
      exact factor_two_canonicalTheta_pos hγ hr0 hr1
    exact ⟨h_spohn_r, h_two, h_pos⟩
  have h_iff : ∀ σ : Matrix (Fin 2) (Fin 2) ℂ,
      IsSelfAdjoint σ → Matrix.trace σ = 1 → 0 < blochRadius σ → blochNormSq σ < 1 →
      (quantumSpohnRate γ θ σ = 0 ↔ σ = gibbsDensityC θ) ∧
      (quantumSpohnRate γ θ σ = γ * quantumJeffreysGibbs σ θ ↔ σ 0 1 = 0) := by
    intro σ hsa htr hr_pos hb
    have h_lag := quantumSpohnRate_eq_blochJeffreys_minus_coherence
      (γ := γ) (ω := 0) (θ := θ) (σ := σ) hγ hsa htr hr_pos hb
    rw [← h_all_j σ hsa htr hb] at h_lag
    have hr_lt : blochRadius σ < 1 := blochRadius_lt_one hb
    have h_ct_pos : 0 < canonicalTheta (blochRadius σ) := canonicalTheta_pos_of_pos hr_pos hr_lt
    have h_coeff_pos : 0 < γ * (canonicalTheta (blochRadius σ) / (2 * blochRadius σ)) :=
      mul_pos hγ (div_pos h_ct_pos (mul_pos (by norm_num) hr_pos))
    have h_diag_iff : quantumSpohnRate γ θ σ = γ * quantumJeffreysGibbs σ θ ↔ σ 0 1 = 0 := by
      rw [h_lag]
      constructor
      · intro h_eq
        have h_prod0 : γ * (canonicalTheta (blochRadius σ) / (2 * blochRadius σ)) * coherenceSq σ = 0 := by
          linear_combination -h_eq
        have h_coh0 : coherenceSq σ = 0 :=
          (mul_eq_zero.mp h_prod0).resolve_left (ne_of_gt h_coeff_pos)
        dsimp [coherenceSq] at h_coh0
        exact Complex.normSq_eq_zero.mp (by linear_combination (1 / 4 : ℝ) * h_coh0)
      · intro h01
        have h_coh0 : coherenceSq σ = 0 := by
          dsimp [coherenceSq]; rw [h01, Complex.normSq_zero, mul_zero]
        rw [h_coh0]; ring_nf
    have h_zero_iff : quantumSpohnRate γ θ σ = 0 ↔ σ = gibbsDensityC θ := by
      have h_rates := operator_spohn_rate_and_strict_coherent_dissipation
        (γ := γ) (ω := 0) (θ := θ) (σ := σ) hγ hsa htr hr_pos hb
      rcases hermitian_unitTrace_entries hsa htr with ⟨h00, h11, h10, _⟩
      constructor
      · intro h0
        have h01 : σ 0 1 = 0 := by
          by_contra h01_ne
          have h_pos := h_rates.2.2.2 h01_ne
          rw [h0] at h_pos
          exact lt_irrefl 0 h_pos
        have hrsq : (blochZ σ) ^ 2 = (blochRadius σ) ^ 2 := by
          rw [blochRadius_sq]
          dsimp [blochNormSq, coherenceSq]
          rw [h01, Complex.normSq_zero, mul_zero, add_zero]
        rw [h0] at h_rates
        have hz_bounds := blochZ_abs_lt_one hb
        have hz_eq : blochZ σ = meanSpin θ :=
          (spohn_diag_eq_zero_iff_real hγ hr_pos hrsq hz_bounds.1 hz_bounds.2).mp h_rates.2.1.symm
        apply ext_mat2
        · rw [h00, hz_eq]; rfl
        · rw [h01]; rfl
        · rw [h10, h01, star_zero]; rfl
        · rw [h11, hz_eq]; rfl
      · intro h_eq
        subst h_eq
        have h01_g : gibbsDensityC θ 0 1 = 0 := rfl
        have hz_g : blochZ (gibbsDensityC θ) = meanSpin θ := blochZ_gibbsDensityC θ
        have hrsq_g : (blochRadius (gibbsDensityC θ)) ^ 2 = (meanSpin θ) ^ 2 := by
          rw [blochRadius_sq]
          dsimp [blochNormSq, coherenceSq]
          rw [hz_g, h01_g, Complex.normSq_zero, mul_zero, add_zero]
        rw [h_rates.2.1, hz_g, hrsq_g]
        ring_nf
    exact ⟨h_zero_iff, h_diag_iff⟩
  exact ⟨h_all_j, h_fac2, h_iff⟩

-- theorem-class: conservation
/-- **Necessary Master Synthesis ($Y_9$: Fully Welded 3D Quantum Semigroup, Cumulant & Spohn Coagulation)**:
Unites the unbroken causal deduction chain $Y_0 \prec \dots \prec Y_9$:
1. $Y_0 \prec Y_1$: `thermalLindbladianOp` equals $\mathcal{G}_1$'s `gkslGen2`, with Heisenberg carré du champ
   forcing transverse damping $\gamma/2$;
2. $Y_2$: Forward Bloch-ball positivity holds iff $t \ge 0$;
3. $Y_4 \wedge Y_5$: Operator `umegakiKernel` diagonal-pinching Pythagoras, Larmor equipotential
   orthogonality, and affine $m$-geodesic characterization;
4. $Y_6 \wedge Y_7$: Exact coherence-lag quantum Spohn–Jeffreys derivative
   $$\frac{d}{dt}D_{\mathrm{Umegaki}}(T_t(\rho) \| \rho_\theta)
     = -\gamma\,J_{\mathrm{Umegaki}}(T_t(\rho), \rho_\theta) + \frac{\gamma}{2}\,\frac{\theta(r(t))}{r(t)}\,c(T_t(\rho)) \le 0,$$
   with strict diagonal Jeffreys reduction iff $\sigma_{01} = 0$;
5. $Y_8$: Simultaneous global relaxation of both quantum coherence $C_{\mathrm{rel}}(T_t(\rho)) \to 0$,
   classical population divergence $D_\phi(z(T_t(\rho)) \| \eta_\theta) \to 0$, and full noncommutative
   Umegaki divergence $D_{\mathrm{Umegaki}}(T_t(\rho) \| \rho_\theta) \to 0$. -/
@[rep_depth thermo, capstone]
theorem master_welded_3d_quantum_semigroup_cumulant_spohn_synthesis
    {γ ω θ : ℝ} {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hγ : 0 < γ) (hsa : IsSelfAdjoint ρ) (htr : Matrix.trace ρ = 1) (hb : blochNormSq ρ < 1) :
    (thermalLindbladianOp γ ω θ ρ =
      gkslGen2 (-(Complex.I * (ω : ℂ) / 2) • pauliGamma1)
        ((Real.sqrt (ratePlus γ θ / 2) : ℂ) • wittFPlus) ρ +
      lindbladDissipator2 ((Real.sqrt (rateMinus γ θ / 2) : ℂ) • wittFMinus) ρ ∧
      thermalHeisenbergDissipator γ θ pauliSigmaX = -((γ / 2 : ℝ) : ℂ) • pauliSigmaX) ∧
    (∀ t : ℝ, (∀ ρ₀ : Matrix (Fin 2) (Fin 2) ℂ,
      IsSelfAdjoint ρ₀ → Matrix.trace ρ₀ = 1 → blochNormSq ρ₀ < 1 →
      blochNormSq (thermalSemigroupC γ ω θ t ρ₀) < 1) ↔ 0 ≤ t) ∧
    ((Matrix.trace (umegakiKernel ρ (gibbsDensityC θ))).re =
      (Matrix.trace (umegakiKernel ρ (diagPinch ρ))).re +
      (Matrix.trace (umegakiKernel (diagPinch ρ) (gibbsDensityC θ))).re ∧
      Matrix.trace ((-(Complex.I * (ω : ℂ) / 2) • ⁅pauliGamma1, ρ⁆) *
        (CFC.log ρ - CFC.log (gibbsDensityC θ))) = 0 ∧
      (IsAffineMGeodesicToGibbs γ ω θ ρ ↔ ρ 0 1 = 0 ∨ (blochZ ρ = meanSpin θ ∧ ω = 0))) ∧
    (∀ t : ℝ, 0 ≤ t → 0 < blochRadius (thermalSemigroupC γ ω θ t ρ) →
      HasDerivAt
        (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ)
        (-γ * quantumJeffreysGibbs (thermalSemigroupC γ ω θ t ρ) θ +
          (γ / 2) * (canonicalTheta (blochRadius (thermalSemigroupC γ ω θ t ρ)) /
            blochRadius (thermalSemigroupC γ ω θ t ρ)) *
              coherenceSq (thermalSemigroupC γ ω θ t ρ)) t ∧
      -quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ) ≤ 0) ∧
    (Tendsto (fun s => coherenceRelEntropy (thermalSemigroupC γ ω θ s ρ)) atTop (𝓝 0) ∧
      Tendsto (fun s => bregmanPhi (blochZ (thermalSemigroupC γ ω θ s ρ)) (meanSpin θ))
        atTop (𝓝 0) ∧
      Tendsto (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ) atTop (𝓝 0)) := by
  have hy1 := wittCAR_gkslGen2_and_carre_du_champ_damping_ratio (le_of_lt hγ) ω θ ρ
  have hy4 := pinching_idempotence_orthogonality_and_operator_pythagoras hsa htr hb θ
  have hy5 := larmor_equipotential_orthogonality_and_affine_m_geodesic_iff hγ ω θ hsa htr hb
  have hy67 := symmetrized_umegaki_jeffreys_factor_two_and_diagonal_iff hγ θ
  have hm := master_bloch_umegaki_spohn_and_gibbs_relaxation (ω := ω) (θ := θ) hγ hsa htr hb
  have h_deriv_lag : ∀ t : ℝ, 0 ≤ t → 0 < blochRadius (thermalSemigroupC γ ω θ t ρ) →
      HasDerivAt
        (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ)
        (-γ * quantumJeffreysGibbs (thermalSemigroupC γ ω θ t ρ) θ +
          (γ / 2) * (canonicalTheta (blochRadius (thermalSemigroupC γ ω θ t ρ)) /
            blochRadius (thermalSemigroupC γ ω θ t ρ)) *
              coherenceSq (thermalSemigroupC γ ω θ t ρ)) t ∧
      -quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ) ≤ 0 := by
    intro t ht hr_t
    have h_raw := master_bloch_quantum_spohn_jeffreys_coherence_lag hγ hsa htr hb t ht hr_t
    have h_pres := @thermalSemigroupC_preserves_blochBall γ ω θ t ρ hγ ht hsa htr hb
    rw [← hy67.1 (thermalSemigroupC γ ω θ t ρ) h_pres.1 h_pres.2.1 h_pres.2.2.2.1] at h_raw
    refine ⟨?_, (hm.1 t ht hr_t).2⟩
    convert h_raw using 1
    ring_nf
  have h_lim_u : Tendsto (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ) atTop (𝓝 0) :=
    hm.2.2.2
  have h_coh_ev_nn : ∀ᶠ s in atTop, 0 ≤ coherenceRelEntropy (thermalSemigroupC γ ω θ s ρ) := by
    refine (eventually_ge_atTop (0 : ℝ)).mono fun s hs => ?_
    have h_pres := @thermalSemigroupC_preserves_blochBall γ ω θ s ρ hγ hs hsa htr hb
    exact (umegakiKernel_trace_and_coherence_pythagoras h_pres.1 h_pres.2.1 h_pres.2.2.2.1 θ).2.2.1.1
  have h_breg_ev_nn :
      ∀ᶠ s in atTop, 0 ≤ bregmanPhi (blochZ (thermalSemigroupC γ ω θ s ρ)) (meanSpin θ) := by
    refine (eventually_ge_atTop (0 : ℝ)).mono fun s hs => ?_
    have h_pres := @thermalSemigroupC_preserves_blochBall γ ω θ s ρ hγ hs hsa htr hb
    have hz_b := blochZ_abs_lt_one h_pres.2.2.2.1
    have hm_b := meanSpin_mem_Ioo θ
    exact (bregman_umegaki_positivity_and_pythagorean_theorem.2.1
      (blochZ (thermalSemigroupC γ ω θ s ρ)) (meanSpin θ) hz_b.1 hz_b.2 hm_b.1 hm_b.2).1
  have h_coh_ev_le : ∀ᶠ s in atTop,
      coherenceRelEntropy (thermalSemigroupC γ ω θ s ρ) ≤
        quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ := by
    refine (eventually_ge_atTop (0 : ℝ)).mono fun s hs => ?_
    have h_pres := @thermalSemigroupC_preserves_blochBall γ ω θ s ρ hγ hs hsa htr hb
    have h_pyth := (umegakiKernel_trace_and_coherence_pythagoras
      h_pres.1 h_pres.2.1 h_pres.2.2.2.1 θ).2.1
    have hz_b := blochZ_abs_lt_one h_pres.2.2.2.1
    have hm_b := meanSpin_mem_Ioo θ
    have hb_nn := (bregman_umegaki_positivity_and_pythagorean_theorem.2.1
      (blochZ (thermalSemigroupC γ ω θ s ρ)) (meanSpin θ) hz_b.1 hz_b.2 hm_b.1 hm_b.2).1
    rw [h_pyth]
    exact le_add_of_nonneg_right hb_nn
  have h_breg_ev_le : ∀ᶠ s in atTop,
      bregmanPhi (blochZ (thermalSemigroupC γ ω θ s ρ)) (meanSpin θ) ≤
        quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ := by
    refine (eventually_ge_atTop (0 : ℝ)).mono fun s hs => ?_
    have h_pres := @thermalSemigroupC_preserves_blochBall γ ω θ s ρ hγ hs hsa htr hb
    have h_pyth := (umegakiKernel_trace_and_coherence_pythagoras
      h_pres.1 h_pres.2.1 h_pres.2.2.2.1 θ).2.1
    have hc_nn := (umegakiKernel_trace_and_coherence_pythagoras
      h_pres.1 h_pres.2.1 h_pres.2.2.2.1 θ).2.2.1.1
    rw [h_pyth]
    exact le_add_of_nonneg_left hc_nn
  have h_lim_coh :
      Tendsto (fun s => coherenceRelEntropy (thermalSemigroupC γ ω θ s ρ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim_u h_coh_ev_nn h_coh_ev_le
  have h_lim_breg :
      Tendsto (fun s => bregmanPhi (blochZ (thermalSemigroupC γ ω θ s ρ)) (meanSpin θ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim_u h_breg_ev_nn h_breg_ev_le
  exact ⟨⟨hy1.2.1, hy1.2.2.2.2.2.2.1⟩,
    fun t => (forward_monoid_positivity_iff_and_backward_aporia hγ ω θ t).2,
    ⟨hy4.2.2.2.2.2, hy5.1, hy5.2.2⟩,
    h_deriv_lag,
    ⟨h_lim_coh, h_lim_breg, h_lim_u⟩⟩

end WeldedCoagulaPoset_Y0_Y9

/-!
## Typed Archetype Registrations & Audit Checks
-/

section TypedArchetypeRegistrations

/-- Typed archetype $\mathcal{G}_8$: Bloch-ball two-sheet spectral projection and `CFC.log` evaluation. -/
def blochTwoSheetCFCLogArchetype : TypedArchetype Unit .proved where
  name := `blochTwoSheetCFCLogArchetype
  phase := 5
  claim := fun _ =>
    (∀ θ : ℝ,
      IsStrictlyPositive (gibbsDensityC θ) ∧
      CFC.log (gibbsDensityC θ) =
        (θ : ℂ) • pauliGamma1 - (cumulantPsi θ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ,
      IsSelfAdjoint ρ → Matrix.trace ρ = 1 → blochNormSq ρ < 1 →
      IsStarProjection (spectralProjector ρ) ∧
      Matrix.trace (spectralProjector ρ) = 1 ∧
      twoSheet (spectralProjector ρ) ((1 + blochRadius ρ) / 2) ((1 - blochRadius ρ) / 2) = ρ ∧
      IsStrictlyPositive ρ ∧
      CFC.log ρ =
        twoSheet (spectralProjector ρ)
          (Real.log ((1 + blochRadius ρ) / 2))
          (Real.log ((1 - blochRadius ρ) / 2)))
  evidence := fun _ =>
    ⟨gibbsDensityC_strictlyPositive_and_cfc_log,
     fun _ hsa htr hb => spectralProjector_twoSheet_and_cfc_log hsa htr hb⟩

#register_archetype blochTwoSheetCFCLogArchetype
#audit_archetype blochTwoSheetCFCLogArchetype

/-- Typed archetype $\mathcal{G}_9$: Noncommutative matrix `umegakiKernel` trace & coherence Pythagoras. -/
def umegakiCoherencePythagorasArchetype : TypedArchetype Unit .proved where
  name := `umegakiCoherencePythagorasArchetype
  phase := 6
  claim := fun _ =>
    ∀ (ρ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ),
      IsSelfAdjoint ρ → Matrix.trace ρ = 1 → blochNormSq ρ < 1 →
      Matrix.trace (umegakiKernel ρ (gibbsDensityC θ)) =
        ((negEntropyPhi (blochRadius ρ) + cumulantPsi θ - θ * blochZ ρ : ℝ) : ℂ) ∧
      quantumUmegakiGibbs ρ θ = coherenceRelEntropy ρ + bregmanPhi (blochZ ρ) (meanSpin θ) ∧
      (0 ≤ coherenceRelEntropy ρ ∧ (coherenceRelEntropy ρ = 0 ↔ ρ 0 1 = 0)) ∧
      (0 ≤ quantumUmegakiGibbs ρ θ ∧ (quantumUmegakiGibbs ρ θ = 0 ↔ ρ = gibbsDensityC θ))
  evidence := fun _ _ θ hsa htr hb =>
    umegakiKernel_trace_and_coherence_pythagoras hsa htr hb θ

#register_archetype umegakiCoherencePythagorasArchetype
#audit_archetype umegakiCoherencePythagorasArchetype

/-- Typed archetype $\mathcal{G}_{10}$: Kolmogorov forward ODE, three-channel KMS Spohn rate & Gibbs relaxation. -/
def quantumSpohnBlochRelaxationArchetype : TypedArchetype Unit .proved where
  name := `quantumSpohnBlochRelaxationArchetype
  phase := 7
  claim := fun _ =>
    ∀ (γ ω θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ),
      0 < γ → IsSelfAdjoint ρ → Matrix.trace ρ = 1 → blochNormSq ρ < 1 →
      (∀ t : ℝ, 0 ≤ t → 0 < blochRadius (thermalSemigroupC γ ω θ t ρ) →
        HasDerivAt (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ)
          (-quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ)) t ∧
        -quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ) ≤ 0) ∧
      (ρ 0 1 ≠ 0 → ∀ t : ℝ, 0 ≤ t →
        0 < blochRadius (thermalSemigroupC γ ω θ t ρ) ∧
        0 < quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ)) ∧
      (∀ i j : Fin 2,
        Tendsto (fun s => thermalSemigroupC γ ω θ s ρ i j) atTop (𝓝 (gibbsDensityC θ i j))) ∧
      Tendsto (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ) atTop (𝓝 0)
  evidence := fun _ _ _ _ _ hγ hsa htr hb =>
    master_bloch_umegaki_spohn_and_gibbs_relaxation hγ hsa htr hb

#register_archetype quantumSpohnBlochRelaxationArchetype
#audit_archetype quantumSpohnBlochRelaxationArchetype

/-- Typed archetype $Y_9$: Fully welded 3D quantum semigroup, cumulant & coherence-corrected Spohn synthesis. -/
def welded3DQuantumSpohnSynthesisArchetype : TypedArchetype Unit .proved where
  name := `welded3DQuantumSpohnSynthesisArchetype
  phase := 8
  claim := fun _ =>
    ∀ (γ ω θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ),
      0 < γ → IsSelfAdjoint ρ → Matrix.trace ρ = 1 → blochNormSq ρ < 1 →
      (thermalLindbladianOp γ ω θ ρ =
        gkslGen2 (-(Complex.I * (ω : ℂ) / 2) • pauliGamma1)
          ((Real.sqrt (ratePlus γ θ / 2) : ℂ) • wittFPlus) ρ +
        lindbladDissipator2 ((Real.sqrt (rateMinus γ θ / 2) : ℂ) • wittFMinus) ρ ∧
        thermalHeisenbergDissipator γ θ pauliSigmaX = -((γ / 2 : ℝ) : ℂ) • pauliSigmaX) ∧
      (∀ t : ℝ, (∀ ρ₀ : Matrix (Fin 2) (Fin 2) ℂ,
        IsSelfAdjoint ρ₀ → Matrix.trace ρ₀ = 1 → blochNormSq ρ₀ < 1 →
        blochNormSq (thermalSemigroupC γ ω θ t ρ₀) < 1) ↔ 0 ≤ t) ∧
      ((Matrix.trace (umegakiKernel ρ (gibbsDensityC θ))).re =
        (Matrix.trace (umegakiKernel ρ (diagPinch ρ))).re +
        (Matrix.trace (umegakiKernel (diagPinch ρ) (gibbsDensityC θ))).re ∧
        Matrix.trace ((-(Complex.I * (ω : ℂ) / 2) • ⁅pauliGamma1, ρ⁆) *
          (CFC.log ρ - CFC.log (gibbsDensityC θ))) = 0 ∧
        (IsAffineMGeodesicToGibbs γ ω θ ρ ↔ ρ 0 1 = 0 ∨ (blochZ ρ = meanSpin θ ∧ ω = 0))) ∧
      (∀ t : ℝ, 0 ≤ t → 0 < blochRadius (thermalSemigroupC γ ω θ t ρ) →
        HasDerivAt
          (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ)
          (-γ * quantumJeffreysGibbs (thermalSemigroupC γ ω θ t ρ) θ +
            (γ / 2) * (canonicalTheta (blochRadius (thermalSemigroupC γ ω θ t ρ)) /
              blochRadius (thermalSemigroupC γ ω θ t ρ)) *
                coherenceSq (thermalSemigroupC γ ω θ t ρ)) t ∧
        -quantumSpohnRate γ θ (thermalSemigroupC γ ω θ t ρ) ≤ 0) ∧
      (Tendsto (fun s => coherenceRelEntropy (thermalSemigroupC γ ω θ s ρ)) atTop (𝓝 0) ∧
        Tendsto (fun s => bregmanPhi (blochZ (thermalSemigroupC γ ω θ s ρ)) (meanSpin θ))
          atTop (𝓝 0) ∧
        Tendsto (fun s => quantumUmegakiGibbs (thermalSemigroupC γ ω θ s ρ) θ) atTop (𝓝 0))
  evidence := fun _ _ _ _ _ hγ hsa htr hb =>
    master_welded_3d_quantum_semigroup_cumulant_spohn_synthesis hγ hsa htr hb

#register_archetype welded3DQuantumSpohnSynthesisArchetype
#audit_archetype welded3DQuantumSpohnSynthesisArchetype

end TypedArchetypeRegistrations

end InfoGeometry.Modular.BlochBallUmegakiAndQuantumSpohn
