/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Lean.Util.CollectAxioms
import Lean.Elab.Command
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPolarization
import InfoGeometry.NCG.OppositePeirceRealMetric
import InfoGeometry.NCG.PeirceProjectorSpectralBounds
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKMReal

set_option autoImplicit false

/-!
# E2E Tier 2 (R1): Boundary Value Analysis & R5 Separations (Features F1–F5)

Opaque-box BVA threshold, degenerate-case, and R5 counterexample tests for R1:
* F1: `NullPolarizationData` without `PositiveHilbertCompatibility` (`negMirror`), vanishing `b`
  energy on null sheets despite `g_J` positivity, `J ≠ Γ`, `J ≠ -J`, pure-chiral split collapse.
* F2: Singular nonzero coupling (`trace > 0` yet `¬ PosDef`), diagonal Krein `Y = -Xᵀ` non-PSD,
  zero-coupling boundary, swap-adjoint asymmetry, and `OppositePeirceRealMetric` graded non-PSD.
* F3: Exact `1/4` and `3/4` BVA saturation at `45°` projectors, commuting lower bound `F² = 0`,
  non-idempotent defect term, and unilateral nilpotent witness `!![0, 0; 1, 0]`.
* F4: Equal-weight `p = q` diagonal BKM, unequal-weight `p ≠ q` non-tracial density functional,
  `Φ = 0` vanishing boundary, and `Module.End ℝ (ℕ → ℝ)` Type III / halving obstructions.
* F5: `dim E = 1` nullcone collapse vs `dim E = 2` explicit vector outside `N_±`, `g_{-J} < 0`,
  hyperbolic-plane `¬ (F²).PosSemidef`, and `clockAxis² = -id`.
-/

namespace PolarizedZ2E2E.Tier2R1

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
open MeasureTheory Set
open InfoGeometry.Krein
open InfoGeometry.Analysis
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPolarization
open InfoGeometry.NCG.OppositePeirceCoupling
open InfoGeometry.NCG.OppositePeirceRealMetric
open InfoGeometry.NCG.PeirceProjectorSpectralBounds
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKMReal

/-! ## Feature F1: Polarization & Dynamics Boundary Cases -/

theorem t2_f1_null_polarization_without_positivity_negMirror
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Nontrivial V]
    (P : NullPolarizationData V) (hpos : PositiveHilbertCompatibility P) :
    P.negMirror.Γ.comp P.negMirror.Γ = LinearMap.id ∧
    P.negMirror.J.comp P.negMirror.J = LinearMap.id ∧
    P.negMirror.Γ.comp P.negMirror.J = -(P.negMirror.J.comp P.negMirror.Γ) ∧
    ¬ PositiveHilbertCompatibility P.negMirror :=
  ⟨P.negMirror.Γ_sq, P.negMirror.J_sq, P.negMirror.Γ_J_anticomm, hpos.not_negMirror⟩

theorem t2_f1_indefinite_energy_vanishes_on_null_sheets
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : NullPolarizationData V} {pos : PositiveHilbertCompatibility P}
    (dyn : ChiralObservablesDynamics P pos)
    {u v : V} (hu : u ∈ P.nullPlusSubmodule) (hv : v ∈ P.nullMinusSubmodule) :
    P.b u (dyn.H u) = 0 ∧
    P.b v (dyn.H v) = 0 ∧
    (u ≠ 0 → 0 < P.gJ u (dyn.H u)) ∧
    (v ≠ 0 → 0 < P.gJ v (dyn.H v)) :=
  ⟨dyn.b_expectation_nullPlus_eq_zero hu,
    dyn.b_expectation_nullMinus_eq_zero hv,
    fun hne => dyn.energy_pos hne,
    fun hne => dyn.energy_pos hne⟩

theorem t2_f1_chiral_involution_J_ne_Gamma_and_J_ne_neg_J
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Nontrivial V]
    (P : NullPolarizationData V) (hpos : PositiveHilbertCompatibility P) :
    P.J ≠ P.Γ ∧
    P.J ≠ -P.J ∧
    P.complexStructure.comp P.complexStructure = -LinearMap.id :=
  ⟨P.J_ne_Γ, hpos.J_ne_neg_J, P.complexStructure_sq⟩

theorem t2_f1_chiral_energy_split_boundary_pure_chiral
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : NullPolarizationData V} {pos : PositiveHilbertCompatibility P}
    (dyn : ChiralObservablesDynamics P pos)
    {u v : V} (hu : u ∈ P.nullPlusSubmodule) (hv : v ∈ P.nullMinusSubmodule) :
    P.projMinus u = 0 ∧
    P.projPlus u = u ∧
    P.gJ u (dyn.H u) = P.gJ (P.projPlus u) (dyn.H (P.projPlus u)) ∧
    P.gJ u v = 0 := by
  have hΓ : P.Γ u = u := (P.mem_nullPlusSubmodule_iff u).mp hu
  have hm : P.projMinus u = 0 := by
    simp [NullPolarizationData.projMinus_apply, hΓ]
  have hp : P.projPlus u = u := by
    have hsum := P.projPlus_add_projMinus_apply u
    rw [hm, add_zero] at hsum
    exact hsum
  have hsplit := dyn.chiral_energy_split u
  rw [hm, map_zero, map_zero, LinearMap.zero_apply, add_zero] at hsplit
  exact ⟨hm, hp, hsplit, P.gJ_nullPlus_orthogonal_nullMinus hu hv⟩

theorem t2_f1_odd_vs_skew_generator_ker_bot
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : NullPolarizationData V} (hpos : PositiveHilbertCompatibility P)
    (m₀ : ℝ) (hm₀ : 0 < m₀) :
    let dyn0 := ChiralObservablesDynamics.ofOddGenerator hpos (0 : Module.End ℝ V)
      (by simp) (fun _ _ => by simp) m₀ hm₀
    let dynSkew0 := ChiralObservablesDynamics.ofOddSkewGenerator hpos (0 : Module.End ℝ V)
      (by simp) (fun _ _ => by simp) m₀ hm₀
    LinearMap.ker dyn0.H = ⊥ ∧
    LinearMap.ker dynSkew0.H = ⊥ ∧
    (∀ u : V, u ≠ 0 → 0 < P.gJ u (dyn0.H u)) := by
  dsimp only
  let dyn0 := ChiralObservablesDynamics.ofOddGenerator hpos (0 : Module.End ℝ V)
    (by simp) (fun _ _ => by simp) m₀ hm₀
  let dynSkew0 := ChiralObservablesDynamics.ofOddSkewGenerator hpos (0 : Module.End ℝ V)
    (by simp) (fun _ _ => by simp) m₀ hm₀
  exact ⟨dyn0.ker_eq_bot, dynSkew0.ker_eq_bot, fun _ hu => dyn0.energy_pos hu⟩

/-! ## Feature F2: Singular Couplings & Krein Adjoint Boundaries -/

theorem t2_f2_singular_nonzero_coupling_not_posDef :
    let X : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let F := blockOdd X Xᵀ
    X ≠ 0 ∧
    0 < Matrix.trace (F * F) ∧
    Matrix.trace (F * F) = 2 ∧
    (F * F).PosSemidef ∧
    ¬ (F * F).PosDef := by
  intro X F
  have htr : Matrix.trace (F * F) = 2 := by
    change Matrix.trace (blockOdd X Xᵀ * blockOdd X Xᵀ) = 2
    rw [blockOdd_sq, trace_fromBlocks_sum]
    simp [X, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  refine ⟨?_, ?_, htr, blockOdd_posAdjoint_sq_posSemidef X, ?_⟩
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [X] at h00
  · rw [htr]
    norm_num
  · rw [blockOdd_posAdjoint_sq_posDef_iff]
    intro ⟨hX, _⟩
    have hv : X *ᵥ ![0, 1] = 0 := by
      ext i
      fin_cases i <;> simp [X, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hz := hX ![0, 1] hv
    have h1 := congrFun hz 1
    simp at h1

theorem t2_f2_diagonal_krein_adjoint_neg_sq :
    let X : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 1]
    let F := blockOdd X (-Xᵀ)
    blockGamma (Fin 2) * Fᵀ * blockGamma (Fin 2) = F ∧
    (-(F * F)).PosSemidef ∧
    ¬ (F * F).PosSemidef := by
  intro X F
  have hXne : X ≠ 0 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [X] at h00
  have h := (indefinite_vs_positive_adjoint_blocks X (-Xᵀ)).2.1
  refine ⟨h.1.mpr rfl, h.2.1, h.2.2 hXne⟩

theorem t2_f2_zero_coupling_boundary :
    let F := blockOdd (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
    F * F = 0 ∧ ¬ (F * F).PosDef := by
  intro F
  have hsq : F * F = 0 := by
    change blockOdd (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ *
      blockOdd (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = 0
    rw [blockOdd_sq]
    simp
  refine ⟨hsq, ?_⟩
  rw [blockOdd_posAdjoint_sq_posDef_iff]
  intro ⟨hX, _⟩
  have hz : (0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 0] = 0 := by simp
  have h1 := congrFun (hX ![1, 0] hz) 0
  simp at h1

theorem t2_f2_swap_adjoint_vs_positive_adjoint_asymmetry :
    let Y : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let F := blockOdd (0 : Matrix (Fin 2) (Fin 2) ℝ) Y
    blockSwap (Fin 2) * Fᵀ * blockSwap (Fin 2) = F ∧
    Fᵀ ≠ F ∧
    F * F = 0 := by
  intro Y F
  have hYne : Y ≠ 0 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [Y] at h00
  have hYT : Yᵀ = Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Y]
  have hnil := unilateral_nilpotent_blocks_sq_zero hYne
  refine ⟨hnil.2.2.1 hYT, ?_, hnil.2.1⟩
  intro hT
  exact hnil.2.2.2.1 (Matrix.isHermitian_iff_isSymm.mpr hT)

theorem t2_f2_opposite_peirce_graded_square_not_psd
    {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix m m ℝ} (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix m m ℝ) (hX : component10 P A ≠ 0) :
    let F := component10 P A + component01 P Aᴴ
    reflection P * (reflection P * F)ᴴ * reflection P = reflection P * F ∧
    ¬ ((reflection P * F) * (reflection P * F)).PosSemidef :=
  ⟨graded_krein_selfadjoint hP hPs A, graded_square_not_posSemidef hP hPs A hX⟩

/-! ## Feature F3: Projector Bound Saturation, Defects & Unilateral Nilpotent -/

theorem t2_f3_quarter_bound_saturation_45_deg :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let Ω : Matrix (Fin 2) (Fin 2) ℝ := !![(1 / 2 : ℝ), 1 / 2; 1 / 2, 1 / 2]
    let F : Matrix (Fin 2) (Fin 2) ℝ := odd P Ω
    IsIdempotentElem P ∧ P.IsHermitian ∧
    IsIdempotentElem Ω ∧ Ω.IsHermitian ∧
    even P Ω = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    F * F = (1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    (1 : Matrix (Fin 2) (Fin 2) ℝ) - F * F = (3 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro P Ω F
  have hP : IsIdempotentElem P := by
    change P * P = P
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  have hPs : P.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P]
  have hΩ : IsIdempotentElem Ω := by
    change Ω * Ω = Ω
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Ω, Matrix.mul_apply, Fin.sum_univ_two]; norm_num)
  have hΩs : Ω.IsHermitian := by
    rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Ω]
  have hev : even P Ω = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    change P * Ω * P + (1 - P) * Ω * (1 - P) = (1 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [P, Ω, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)
  have hquarter := (orthogonalProjector_F_sq_le_quarter hP hPs hΩ hΩs).2.2
  rw [hev, sub_self, zero_mul] at hquarter
  have hFsq : F * F = (1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    exact (sub_eq_zero.mp hquarter).symm
  have h3q : (1 : Matrix (Fin 2) (Fin 2) ℝ) - F * F =
      (3 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hFsq]
    ext i j
    fin_cases i <;> fin_cases j <;> (simp; try norm_num)
  exact ⟨hP, hPs, hΩ, hΩs, hev, hFsq, h3q⟩

theorem t2_f3_commuting_projectors_lower_bound
    {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix m m ℝ} (hP : IsIdempotentElem P) :
    odd P P = 0 ∧
    odd P P * odd P P = 0 ∧
    (1 : Matrix m m ℝ) - odd P P * odd P P = 1 := by
  have hodd : odd P P = 0 := by
    rw [odd_apply]
    change P * P * (1 - P) + (1 - P) * P * P = 0
    rw [hP.eq]
    noncomm_ring [hP.eq]
  rw [hodd, zero_mul, sub_zero]
  exact ⟨rfl, rfl, rfl⟩

theorem t2_f3_non_idempotent_defect_boundary :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let Ω : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let T := component11 P Ω
    let G := component00 P Ω
    let F := odd P Ω
    Ω * Ω - Ω ≠ 0 ∧
    (T - T * T) + (G - G * G) = F * F - even P (Ω * Ω - Ω) := by
  intro P Ω T G F
  have hP : IsIdempotentElem P := by
    change P * P = P
    ext i j
    fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨?_, peirce_idempotencyDefect_law hP Ω⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [Ω] at h00

theorem t2_f3_unilateral_nilpotent_concrete_and_block :
    let F : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    (F ≠ 0 ∧ F * F = 0 ∧ J * Fᵀ * J = F ∧ ¬ F.IsHermitian) ∧
    (∀ (P : Matrix (Fin 2) (Fin 2) ℝ), IsIdempotentElem P → P.IsHermitian →
      ∀ (X' Y' : Matrix (Fin 2) (Fin 2) ℝ),
      X' ∈ peirce10 P → Y' ∈ peirce01 P → (X' + Y').IsHermitian → X' = 0 → Y' = 0) := by
  refine ⟨unilateral_nilpotent_concrete_witness, ?_⟩
  intro P hP hPs X' Y' hX' hY' hHerm hX0
  by_cases hY0 : Y' = 0
  · exact hY0
  · exact ((unilateral_nilpotent_F_sq_zero hP hPs hY' hY0).2.2 X' Y' hX' hY' hHerm hX0).1

theorem t2_f3_quadForm_exact_saturation_vector :
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    let Ω : Matrix (Fin 2) (Fin 2) ℝ := !![(1 / 2 : ℝ), 1 / 2; 1 / 2, 1 / 2]
    let F : Matrix (Fin 2) (Fin 2) ℝ := odd P Ω
    let v : Fin 2 → ℝ := ![1, 1]
    v ⬝ᵥ (F * F) *ᵥ v = (1 / 4 : ℝ) * (v ⬝ᵥ v) ∧
    v ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) - F * F) *ᵥ v = (3 / 4 : ℝ) * (v ⬝ᵥ v) := by
  intro P Ω F v
  have hsat := t2_f3_quarter_bound_saturation_45_deg
  dsimp only at hsat
  have h1 : F * F = (1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := hsat.2.2.2.2.2.1
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℝ) - F * F =
      (3 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := hsat.2.2.2.2.2.2
  constructor
  · rw [h1]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  · rw [h2]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

/-! ## Feature F4: BKM Weight Boundaries & Type III Infinite-Algebra Obstructions -/

theorem t2_f4_equal_weights_p_eq_q_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ : Matrix ι ι ℝ) (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p : ℝ} (hp : 0 < p) :
    twoSheetReal P p p = p • (1 : Matrix ι ι ℝ) ∧
    logDividedDifference p p = p⁻¹ ∧
    0 < logDividedDifference p p ∧
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace (Φ * twoSheetResolventReal P p p s * Φ *
        twoSheetResolventReal P p p s)) =
      p⁻¹ * Matrix.trace (Φ * Φ) := by
  have htr := real_twoSheetResolvent_quadratic_trace P hP Φ hΦ11 hΦ00 hp hp
  rw [logDividedDifference_self] at htr
  refine ⟨?_, logDividedDifference_self p, logDividedDifference_pos hp hp, htr⟩
  unfold twoSheetReal
  rw [twoSheet_equal]

theorem t2_f4_unequal_weights_non_tracial_density :
    canonicalFiniteTraceVsTypeIIISeparation.bkmContext.p ≠
      canonicalFiniteTraceVsTypeIIISeparation.bkmContext.q ∧
    Matrix.trace (canonicalFiniteTraceVsTypeIIISeparation.bkmContext.density *
        (conePlus canonicalFiniteTraceVsTypeIIISeparation.bkmContext.P
          canonicalFiniteTraceVsTypeIIISeparation.bkmContext.Φ *
        coneMinus canonicalFiniteTraceVsTypeIIISeparation.bkmContext.P
          canonicalFiniteTraceVsTypeIIISeparation.bkmContext.Φ)) ≠
      Matrix.trace (canonicalFiniteTraceVsTypeIIISeparation.bkmContext.density *
        (coneMinus canonicalFiniteTraceVsTypeIIISeparation.bkmContext.P
          canonicalFiniteTraceVsTypeIIISeparation.bkmContext.Φ *
        conePlus canonicalFiniteTraceVsTypeIIISeparation.bkmContext.P
          canonicalFiniteTraceVsTypeIIISeparation.bkmContext.Φ)) ∧
    (∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
      canonicalFiniteTraceVsTypeIIISeparation.finiteStarTrace.τ (A * B) =
        canonicalFiniteTraceVsTypeIIISeparation.finiteStarTrace.τ (B * A)) := by
  have hpq : canonicalFiniteTraceVsTypeIIISeparation.bkmContext.p ≠
      canonicalFiniteTraceVsTypeIIISeparation.bkmContext.q := by
    change (1 : ℝ) ≠ 2
    norm_num
  have hΦne : canonicalFiniteTraceVsTypeIIISeparation.bkmContext.Φ ≠ 0 := by
    intro h0
    have h01 := congrFun (congrFun h0 0) 1
    simp [canonicalFiniteTraceVsTypeIIISeparation, concreteRealTwoSheetBKMContext] at h01
  have hnt := canonicalFiniteTraceVsTypeIIISeparation.nonTracial_density_when_weights_differ hpq hΦne
  exact ⟨hpq, hnt.1, hnt.2⟩

theorem t2_f4_zero_perturbation_vanishing_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P * P = P)
    (Φ : Matrix ι ι ℝ) (hΦT : Φᵀ = Φ)
    (hΦ11 : P * Φ * P = 0) (hΦ00 : (1 - P) * Φ * (1 - P) = 0)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (0 < (∫ s in Ioi (0 : ℝ),
      Matrix.trace (Φ * twoSheetResolventReal P p q s * Φ *
        twoSheetResolventReal P p q s)) ↔ Φ ≠ 0) ∧
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace ((0 : Matrix ι ι ℝ) * twoSheetResolventReal P p q s *
        (0 : Matrix ι ι ℝ) * twoSheetResolventReal P p q s)) = 0 := by
  refine ⟨real_twoSheetResolvent_quadratic_pos_iff P hP Φ hΦT hΦ11 hΦ00 hp hq, ?_⟩
  simp

theorem t2_f4_end_nat_typeIII_obstructions :
    (¬ ∃ τ : Module.End ℝ (ℕ → ℝ) →ₗ[ℝ] ℝ,
      (∀ a b : Module.End ℝ (ℕ → ℝ), τ (a * b) = τ (b * a)) ∧ τ 1 ≠ 0) ∧
    IsEmpty (IdempotentFaithfulTrace (Module.End ℝ (ℕ → ℝ))) ∧
    IsEmpty (Module.End ℝ (ℕ → ℝ) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨no_unital_tracial_functional_on_end_nat,
    no_idempotent_faithful_trace_on_end_nat,
    no_algHom_end_nat_to_matrix (Fin 2)⟩

theorem t2_f4_finite_star_isometry_is_unitary :
    natSeqLeftShift * natSeqRightShift = 1 ∧
    natSeqRightShift * natSeqLeftShift ≠ 1 ∧
    (∀ V : Matrix (Fin 2) (Fin 2) ℝ, star V * V = 1 → V * star V = 1) :=
  ⟨natSeqLeftShift_mul_rightShift,
    natSeqRightShift_mul_leftShift_ne,
    fun V hV => no_nonunitary_starIsometry_of_faithful_starTrace (matrixStarTrace (Fin 2)) V hV⟩

/-! ## Feature F5: R5 Separations & Dimensional Boundaries -/

theorem t2_f5_dim_one_boundary_nullcone_collapse
    (u : DoubledSpace ℝ) (hu : chiralKreinForm (E := ℝ) u u = 0) :
    leftChiralProjector (E := ℝ) u = u ∨ rightChiralProjector (E := ℝ) u = u := by
  have hu_eq : to_doubled (WithLp.fst u) (WithLp.snd u) = u := DoubledSpace.ext rfl rfl
  have hform : chiralKreinForm (E := ℝ) u u = 2 * (WithLp.fst u * WithLp.snd u) := by
    calc
      chiralKreinForm (E := ℝ) u u
          = chiralKreinForm (E := ℝ) (to_doubled (WithLp.fst u) (WithLp.snd u))
              (to_doubled (WithLp.fst u) (WithLp.snd u)) := by rw [hu_eq]
      _ = inner ℝ (WithLp.fst u) (WithLp.snd u) + inner ℝ (WithLp.snd u) (WithLp.fst u) :=
            chiralKreinForm_to_doubled _ _ _ _
      _ = 2 * (WithLp.fst u * WithLp.snd u) := by
            simp only [RCLike.inner_apply, conj_trivial]
            ring
  rw [hform] at hu
  have hprod : WithLp.fst u * WithLp.snd u = 0 := (mul_eq_zero.mp hu).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hprod with hfst | hsnd
  · right
    calc
      rightChiralProjector (E := ℝ) u
          = rightChiralProjector (E := ℝ) (to_doubled (WithLp.fst u) (WithLp.snd u)) := by
            rw [hu_eq]
      _ = to_doubled 0 (WithLp.snd u) := rightChiralProjector_to_doubled _ _
      _ = to_doubled (WithLp.fst u) (WithLp.snd u) := by rw [hfst]
      _ = u := hu_eq
  · left
    calc
      leftChiralProjector (E := ℝ) u
          = leftChiralProjector (E := ℝ) (to_doubled (WithLp.fst u) (WithLp.snd u)) := by
            rw [hu_eq]
      _ = to_doubled (WithLp.fst u) 0 := leftChiralProjector_to_doubled _ _
      _ = to_doubled (WithLp.fst u) (WithLp.snd u) := by rw [hsnd]
      _ = u := hu_eq

theorem t2_f5_dim_two_explicit_null_outside_chiral :
    let e₁ : EuclideanSpace ℝ (Fin 2) := !₂[1, 0]
    let e₂ : EuclideanSpace ℝ (Fin 2) := !₂[0, 1]
    let u : DoubledSpace (EuclideanSpace ℝ (Fin 2)) := to_doubled e₁ e₂
    u ≠ 0 ∧
    chiralKreinForm u u = 0 ∧
    leftChiralProjector u ≠ u ∧
    rightChiralProjector u ≠ u := by
  intro e₁ e₂
  have he₁ : e₁ ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
    simp [e₁] at h0
  have he₂ : e₂ ≠ 0 := by
    intro h
    have h1 := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 1) h
    simp [e₂] at h1
  have horth : inner ℝ e₁ e₂ = 0 := by
    simp [e₁, e₂, PiLp.inner_apply, Fin.sum_univ_two]
  exact orthogonal_pair_nullcone_not_in_chiral he₁ he₂ horth

theorem t2_f5_neg_mirror_strictly_negative_diagonal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : NullPolarizationData V) (hpos : PositiveHilbertCompatibility P)
    {u : V} (hu : u ≠ 0) :
    P.negMirror.gJ u u < 0 := by
  rw [P.negMirror_gJ u u, neg_lt_zero]
  exact hpos.gJ_pos hu

theorem t2_f5_hyperbolic_plane_not_psd_and_noncomm :
    hyperbolicPlaneF * hyperbolicPlaneF = -(1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    ¬ (hyperbolicPlaneF * hyperbolicPlaneF).PosSemidef ∧
    hyperbolicPlaneGamma * hyperbolicPlaneF ≠ hyperbolicPlaneF * hyperbolicPlaneGamma ∧
    (∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A) :=
  ⟨hyperbolicPlane_kreinSelfAdjoint_sq_neg_one.2.2.2.2.1,
    hyperbolicPlane_kreinSelfAdjoint_sq_neg_one.2.2.2.2.2,
    hyperbolicPlane_gamma_noncomm,
    hyperbolicPlane_mat2_noncomm⟩

theorem t2_f5_hyperbolic_clockAxis_sq_neg_id
    (u : DoubledSpace (EuclideanSpace ℝ (Fin 2))) (hu : u ≠ 0) :
    IsChiralKreinSelfAdjoint (clockAxis (E := EuclideanSpace ℝ (Fin 2))) ∧
    (clockAxis (E := EuclideanSpace ℝ (Fin 2))).comp
      (clockAxis (E := EuclideanSpace ℝ (Fin 2))) =
      -(ContinuousLinearMap.id ℝ (DoubledSpace (EuclideanSpace ℝ (Fin 2)))) ∧
    inner ℝ u (clockAxis (clockAxis u)) < 0 := by
  have hb := hyperbolicPlane_clockAxis_bridge (E := EuclideanSpace ℝ (Fin 2))
  refine ⟨hb.2.2.2.2.1, hb.2.2.2.2.2.2, ?_⟩
  have hcomp := congrArg (fun f : DoubledSpace (EuclideanSpace ℝ (Fin 2)) →L[ℝ]
      DoubledSpace (EuclideanSpace ℝ (Fin 2)) => f u) hb.2.2.2.2.2.2
  change clockAxis (clockAxis u) = -u at hcomp
  rw [hcomp, inner_neg_right, neg_lt_zero]
  exact real_inner_self_pos.mpr hu

end PolarizedZ2E2E.Tier2R1

section E2EAxiomAudit
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut audited : Nat := 0
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isSome then continue
    if name.toString.startsWith "_private." then continue
    match info with
    | .thmInfo _ | .defnInfo _ =>
      if info.isUnsafe || info.isPartial then
        throwError "Unsafe or partial E2E declaration: {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed axiom {ax} in E2E declaration {name}"
      audited := audited + 1
    | .axiomInfo _ =>
      throwError "Disallowed axiom declaration in E2E file: {name}"
    | _ => pure ()
  if audited == 0 then
    throwError "E2EAxiomAudit found 0 declarations in current module"
  logInfo m!"E2E_AXIOM_AUDIT_PASS: {audited} local declarations verified"
end E2EAxiomAudit
