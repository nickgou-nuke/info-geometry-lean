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
# E2E Tier 1 (R1): Polarized Nullcone, Adjoints, Spectral Bounds & Real BKM (Features F1–F5)

Opaque-box feature verification for Requirement R1 and R5[R1] across Features F1–F5:
* F1: Null polarization `(V, b, Γ, J)` vs positive Hilbert compatibility `g_J`, Hadamard diagonal
  Krein coordinate change, and `ChiralObservablesDynamics` coercivity/energy positivity.
* F2: Indefinite Krein adjoint (`Γ Fᵀ Γ = F`, `J Fᵀ J = F`) vs positive adjoint (`Y = Xᵀ`,
  `F² ≥ 0`, `PosDef` iff trivial kernel).
* F3: Orthogonal-projector bounds `0 ≤ F² ≤ (1/4)I` and `I - F² ≥ (3/4)I` via the idempotency
  defect `(T - T²) + (G - G²) = F² - even P (Ω² - Ω)`, vs unilateral nilpotent `F² = 0`.
* F4: Real-API BKM lifting (`RealTwoSheetBKMContext`) and `FiniteTraceBKMVsTypeIIISeparation`.
* F5: Concrete R5 separations (`dim E > 1` nullcone outside `N_±`, `J ↦ -J`, hyperbolic `F² = -I`).
-/

namespace PolarizedZ2E2E.Tier1R1

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
open MeasureTheory Set
open InfoGeometry.Krein
open InfoGeometry.Analysis
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Core.PeirceCoupledCorners
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinAdjoint
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPolarization
open InfoGeometry.NCG.OppositePeirceCoupling
open InfoGeometry.NCG.OppositePeirceRealMetric
open InfoGeometry.NCG.PeirceProjectorSpectralBounds
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKMReal

/-! ## Feature F1: Null Polarization, Positive Compatibility, Hadamard & Dynamics -/

theorem t1_f1_null_submodules_compl_and_isotropic
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : NullPolarizationData V) :
    IsCompl P.nullPlusSubmodule P.nullMinusSubmodule ∧
    (∀ u v : V, u ∈ P.nullPlusSubmodule → v ∈ P.nullPlusSubmodule → P.b u v = 0) ∧
    (∀ u v : V, u ∈ P.nullMinusSubmodule → v ∈ P.nullMinusSubmodule → P.b u v = 0) ∧
    (∀ u v : V, u ∈ P.nullPlusSubmodule → v ∈ P.nullMinusSubmodule → P.gJ u v = 0) :=
  ⟨P.isCompl_nullSubmodules,
    fun _ _ hu hv => P.nullPlus_isotropic hu hv,
    fun _ _ hu hv => P.nullMinus_isotropic hu hv,
    fun _ _ hu hv => P.gJ_nullPlus_orthogonal_nullMinus hu hv⟩

theorem t1_f1_positive_compat_inner_core_and_cs
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : NullPolarizationData V} (hpos : PositiveHilbertCompatibility P)
    (u v : V) :
    (hpos.toInnerProductCore.inner u v = P.gJ u v) ∧
    (P.gJ u u = 0 ↔ u = 0) ∧
    ((P.gJ u v) ^ 2 ≤ P.gJ u u * P.gJ v v) :=
  ⟨rfl, hpos.gJ_eq_zero_iff u, hpos.cauchy_schwarz u v⟩

theorem t1_f1_hadamard_doubled_preserves_forms
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u v : DoubledSpace E) :
    let e := HadamardKreinPolarizationEquiv.doubledHadamardKreinPolarizationEquiv E
    (NullPolarizationData.doubledNullPolarization E).b (e.toLinearEquiv u) (e.toLinearEquiv v) =
      splitKreinForm u v ∧
    (NullPolarizationData.doubledNullPolarization E).gJ (e.toLinearEquiv u) (e.toLinearEquiv v) =
      (doubledDiagonalKreinData E).gDiag u v ∧
    (NullPolarizationData.doubledNullPolarization E).gJ u v = inner ℝ u v := by
  dsimp only
  refine ⟨?_, ?_, PositiveHilbertCompatibility.doubled_gJ_eq_inner u v⟩
  · exact (HadamardKreinPolarizationEquiv.doubledHadamardKreinPolarizationEquiv E).map_form u v
  · exact (HadamardKreinPolarizationEquiv.doubledHadamardKreinPolarizationEquiv E).map_gJ u v

theorem t1_f1_abstract_hadamard_positivity_transfer
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (P : NullPolarizationData V) :
    let e := HadamardKreinPolarizationEquiv.abstractHadamardEquiv P
    (PositiveHilbertCompatibility P ↔
      (∀ u : V, u ≠ 0 → 0 < P.toDiagonalKreinData.bDiag u (P.toDiagonalKreinData.symmDiag u))) ∧
    (∀ u v : V, P.gJ (e.toLinearEquiv u) (e.toLinearEquiv v) = P.toDiagonalKreinData.gDiag u v) :=
  ⟨(HadamardKreinPolarizationEquiv.abstractHadamardEquiv P).positivity_transfer,
    fun u v => (HadamardKreinPolarizationEquiv.abstractHadamardEquiv P).map_gJ u v⟩

theorem t1_f1_chiral_dynamics_energy_gap_and_split
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : NullPolarizationData V} {pos : PositiveHilbertCompatibility P}
    (dyn : ChiralObservablesDynamics P pos)
    (u : V) :
    (u ≠ 0 → 0 < P.gJ u (dyn.H u)) ∧
    LinearMap.ker dyn.H = ⊥ ∧
    P.gJ u (dyn.H u) =
      P.gJ (P.projPlus u) (dyn.H (P.projPlus u)) +
      P.gJ (P.projMinus u) (dyn.H (P.projMinus u)) ∧
    (∀ μ : ℝ, u ≠ 0 → dyn.H u = μ • u → dyn.m₀ ≤ μ) :=
  ⟨fun hu => dyn.energy_pos hu, dyn.ker_eq_bot, dyn.chiral_energy_split u,
    fun _ hu heig => dyn.eigenvalue_ge_gap hu heig⟩

theorem t1_f1_odd_generator_dynamics_sign
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : NullPolarizationData V} (hpos : PositiveHilbertCompatibility P)
    (D : Module.End ℝ V)
    (hD_odd : D.comp P.Γ = -(P.Γ.comp D))
    (hD_symm : ∀ u v : V, P.gJ (D u) v = P.gJ u (D v))
    (m₀ : ℝ) (hm₀ : 0 < m₀) :
    let dyn := ChiralObservablesDynamics.ofOddGenerator hpos D hD_odd hD_symm m₀ hm₀
    dyn.m₀ = m₀ ^ 2 ∧
    (∀ u : V, u ≠ 0 → 0 < P.gJ u (dyn.H u)) ∧
    (dyn.H.comp P.J = P.J.comp dyn.H →
      (∀ {u : V}, u ≠ 0 → P.J u = u → 0 < P.b u (dyn.H u)) ∧
      (∀ {u : V}, u ≠ 0 → P.J u = -u → P.b u (dyn.H u) < 0)) := by
  dsimp only
  let dyn := ChiralObservablesDynamics.ofOddGenerator hpos D hD_odd hD_symm m₀ hm₀
  exact ⟨rfl, fun _ hu => dyn.energy_pos hu, fun hJ => dyn.b_expectation_sign_of_J_comm hJ⟩

theorem t1_f1_concrete_ground_witness_dynamics :
    let P := concreteDoubledNullPolarizationReal
    let dyn := concreteChiralObservablesDynamicsReal
    let uPlus : DoubledSpace ℝ := to_doubled 1 1
    let uMinus : DoubledSpace ℝ := to_doubled 1 (-1)
    let uNull : DoubledSpace ℝ := to_doubled 1 0
    (etaChiral (E := ℝ)).toLinearMap ≠ 0 ∧
    P.J = (etaChiral (E := ℝ)).toLinearMap ∧
    0 < dyn.m₀ ∧
    dyn.m₀ = 1 ∧
    0 < P.gJ uPlus (dyn.H uPlus) ∧
    0 < P.gJ uMinus (dyn.H uMinus) ∧
    0 < P.b uPlus (dyn.H uPlus) ∧
    P.b uMinus (dyn.H uMinus) < 0 ∧
    P.b uNull (dyn.H uNull) = 0 := by
  intro P dyn uPlus uMinus uNull
  have hDne : (etaChiral (E := ℝ)).toLinearMap ≠ 0 := by
    intro h0
    have happ := congrArg
      (fun T : Module.End ℝ (DoubledSpace ℝ) => T (to_doubled (1 : ℝ) 0)) h0
    have hsnd := congrArg WithLp.snd happ
    change WithLp.snd (etaChiral (E := ℝ) (to_doubled (1 : ℝ) 0)) =
      WithLp.snd (0 : DoubledSpace ℝ) at hsnd
    rw [etaChiral_to_doubled] at hsnd
    simp at hsnd
  have huPlus_ne : uPlus ≠ 0 := by
    intro h0
    have hfst := congrArg WithLp.fst h0
    simp [uPlus] at hfst
  have huMinus_ne : uMinus ≠ 0 := by
    intro h0
    have hfst := congrArg WithLp.fst h0
    simp [uMinus] at hfst
  have hHJ : dyn.H.comp P.J = P.J.comp dyn.H := by
    apply LinearMap.ext
    intro u
    change P.J (P.J (P.J u)) + ((1 : ℝ) ^ 2) • P.J u =
      P.J (P.J (P.J u) + ((1 : ℝ) ^ 2) • u)
    rw [map_add, map_smul]
  have hJplus : P.J uPlus = uPlus := by
    change etaChiral (E := ℝ) (to_doubled (1 : ℝ) 1) = to_doubled (1 : ℝ) 1
    rw [etaChiral_to_doubled]
  have hJminus : P.J uMinus = -uMinus := by
    change etaChiral (E := ℝ) (to_doubled (1 : ℝ) (-1)) = -to_doubled (1 : ℝ) (-1)
    rw [etaChiral_to_doubled]
    apply DoubledSpace.ext <;> simp
  have hNull : uNull ∈ P.nullPlusSubmodule := by
    rw [P.mem_nullPlusSubmodule_iff]
    change gamma5 (E := ℝ) (to_doubled (1 : ℝ) 0) = to_doubled (1 : ℝ) 0
    simp
  have hsign := dyn.b_expectation_sign_of_J_comm hHJ
  have hm0 : dyn.m₀ = 1 := by
    change (1 : ℝ) ^ 2 = 1
    norm_num
  refine ⟨hDne, rfl, dyn.m₀_pos, hm0,
    dyn.energy_pos huPlus_ne, dyn.energy_pos huMinus_ne,
    hsign.1 huPlus_ne hJplus, hsign.2 huMinus_ne hJminus,
    dyn.b_expectation_nullPlus_eq_zero hNull⟩

/-! ## Feature F2: Indefinite Krein Adjoint vs Positive Adjoint -/

theorem t1_f2_blockOdd_positive_adjoint_psd_and_pd_iff
    {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℝ) :
    ((blockOdd X Y).IsHermitian ↔ Y = Xᵀ) ∧
    (blockOdd X Xᵀ * blockOdd X Xᵀ).PosSemidef ∧
    ((blockOdd X Xᵀ * blockOdd X Xᵀ).PosDef ↔
      (∀ v : n → ℝ, X *ᵥ v = 0 → v = 0) ∧ (∀ v : n → ℝ, Xᵀ *ᵥ v = 0 → v = 0)) :=
  ⟨blockOdd_isHermitian_iff X Y,
    blockOdd_posAdjoint_sq_posSemidef X,
    blockOdd_posAdjoint_sq_posDef_iff X⟩

theorem t1_f2_concrete_invertible_blockOdd_posDef :
    let X : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]
    (blockOdd X Xᵀ * blockOdd X Xᵀ).PosDef := by
  intro X
  rw [blockOdd_posAdjoint_sq_posDef_iff]
  constructor
  · intro v hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp only [X, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.zero_apply] at h0 h1
    ext i
    fin_cases i
    · have hv1 : v 1 = 0 := by linarith
      have hv0 : v 0 = 0 := by linarith
      exact hv0
    · have hv1 : v 1 = 0 := by linarith
      exact hv1
  · intro v hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp only [X, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.zero_apply] at h0 h1
    ext i
    fin_cases i
    · have hv0 : v 0 = 0 := by linarith
      exact hv0
    · have hv0 : v 0 = 0 := by linarith
      have hv1 : v 1 = 0 := by linarith
      exact hv1

theorem t1_f2_peirce_positive_vs_krein_adjoint_general
    {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix m m ℝ} (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix m m ℝ) :
    let F := component10 P A + component01 P Aᴴ
    F.IsHermitian ∧
    (F * F).PosSemidef ∧
    (reflection P * (reflection P * F)ᵀ * reflection P = reflection P * F) ∧
    (-((reflection P * F) * (reflection P * F))).PosSemidef := by
  have h := (peirce_indefinite_vs_positive_adjoint hP hPs).1 A
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem t1_f2_opposite_peirce_trace_and_kernel
    {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (A : Matrix n n ℝ) :
    (0 < Matrix.trace ((component10 P A + component01 P Aᴴ) *
      (component10 P A + component01 P Aᴴ)) ↔ component10 P A ≠ 0) ∧
    LinearMap.ker (Matrix.toLin' ((component10 P A + component01 P Aᴴ) *
      (component10 P A + component01 P Aᴴ))) =
      LinearMap.ker (Matrix.toLin' (component10 P A)) ⊓
        LinearMap.ker (Matrix.toLin' ((component10 P A)ᴴ)) :=
  ⟨trace_square_pos_iff hP hPs A, square_ker hP hPs A⟩

theorem t1_f2_doubled_chiral_krein_adjoint_formula
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : ChiralEnd (E := E)) (u v : DoubledSpace E) :
    chiralKreinForm (A u) v = chiralKreinForm u (chiralKreinAdjoint A v) ∧
    (IsChiralKreinSelfAdjoint A ↔ IsChiralKreinHermitian A) :=
  ⟨chiralKreinForm_kreinAdjoint A u v, isChiralKreinSelfAdjoint_iff_form A⟩

theorem t1_f2_block_adjoint_three_regimes_equivalence
    (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    ((blockOdd X Y)ᵀ = blockOdd X Y ↔ Y = Xᵀ) ∧
    (blockGamma (Fin 2) * (blockOdd X Y)ᵀ * blockGamma (Fin 2) = blockOdd X Y ↔ Y = -Xᵀ) ∧
    (blockSwap (Fin 2) * (blockOdd X Y)ᵀ * blockSwap (Fin 2) = blockOdd X Y ↔ Xᵀ = X ∧ Yᵀ = Y) := by
  have h := indefinite_vs_positive_adjoint_blocks X Y
  exact ⟨h.1.1, h.2.1.1, h.2.2.1⟩

/-! ## Feature F3: Orthogonal-Projector 1/4 & 3/4 Bounds vs Unilateral Nilpotent -/

theorem t1_f3_idempotency_defect_identity
    {A : Type*} [Ring A] [Algebra ℝ A]
    {P : A} (hP : IsIdempotentElem P) (Ω : A) :
    (component11 P Ω - component11 P Ω * component11 P Ω) +
      (component00 P Ω - component00 P Ω * component00 P Ω) =
      odd P Ω * odd P Ω - even P (Ω * Ω - Ω) ∧
    (IsIdempotentElem Ω →
      (1 / 4 : ℝ) • (1 : A) - odd P Ω * odd P Ω =
        (even P Ω - (1 / 2 : ℝ) • (1 : A)) * (even P Ω - (1 / 2 : ℝ) • (1 : A))) :=
  ⟨peirce_idempotencyDefect_law hP Ω, fun hΩ => peirce_projector_quarter_sq_identity hP hΩ⟩

theorem t1_f3_orthogonal_projector_quarter_bound
    {m : Type*} [Fintype m] [DecidableEq m]
    {P Ω : Matrix m m ℝ}
    (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (hΩ : IsIdempotentElem Ω) (hΩs : Ω.IsHermitian) :
    let F : Matrix m m ℝ := odd P Ω
    (F * F).PosSemidef ∧
    ((1 / 4 : ℝ) • (1 : Matrix m m ℝ) - F * F).PosSemidef ∧
    ((1 / 4 : ℝ) • (1 : Matrix m m ℝ) - F * F =
      (even P Ω - (1 / 2 : ℝ) • (1 : Matrix m m ℝ)) *
        (even P Ω - (1 / 2 : ℝ) • (1 : Matrix m m ℝ))) :=
  orthogonalProjector_F_sq_le_quarter hP hPs hΩ hΩs

theorem t1_f3_orthogonal_projector_three_quarters_bound
    {m : Type*} [Fintype m] [DecidableEq m]
    {P Ω : Matrix m m ℝ}
    (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (hΩ : IsIdempotentElem Ω) (hΩs : Ω.IsHermitian) :
    let F : Matrix m m ℝ := odd P Ω
    (((1 : Matrix m m ℝ) - F * F) - (3 / 4 : ℝ) • (1 : Matrix m m ℝ)).PosSemidef ∧
    ((1 : Matrix m m ℝ) - F * F).PosDef :=
  orthogonalProjector_one_sub_F_sq_ge_three_quarters hP hPs hΩ hΩs

theorem t1_f3_orthogonal_projector_quadForm_and_block_bounds
    {n : Type*} [Fintype n] [DecidableEq n]
    {T X Y G : Matrix n n ℝ}
    (hΩ : IsIdempotentElem (Matrix.fromBlocks T X Y G))
    (hΩs : (Matrix.fromBlocks T X Y G).IsHermitian)
    (v : n ⊕ n → ℝ) :
    (blockOdd X Y * blockOdd X Y).PosSemidef ∧
    ((1 : Matrix (n ⊕ n) (n ⊕ n) ℝ) - blockOdd X Y * blockOdd X Y).PosDef ∧
    0 ≤ v ⬝ᵥ (odd (blockCut n) (Matrix.fromBlocks T X Y G) *
      odd (blockCut n) (Matrix.fromBlocks T X Y G)) *ᵥ v ∧
    v ⬝ᵥ (odd (blockCut n) (Matrix.fromBlocks T X Y G) *
      odd (blockCut n) (Matrix.fromBlocks T X Y G)) *ᵥ v ≤ (1 / 4 : ℝ) * (v ⬝ᵥ v) := by
  have hb := orthogonalProjector_block_bounds hΩ hΩs
  have hq := orthogonalProjector_quadForm_bounds
    (blockCut_isIdempotent (n := n)) (blockCut_isHermitian (n := n)) hΩ hΩs v
  exact ⟨hb.1, hb.2.2.2, hq.1, hq.2.1⟩

theorem t1_f3_unilateral_nilpotent_regimes
    {n : Type*} [Fintype n] [DecidableEq n]
    {Y : Matrix n n ℝ} (hYne : Y ≠ 0) :
    let F : Matrix (n ⊕ n) (n ⊕ n) ℝ := blockOdd 0 Y
    F ≠ 0 ∧ F * F = 0 ∧ ¬ F.IsHermitian ∧
    (Yᵀ = Y → blockSwap n * Fᵀ * blockSwap n = F) := by
  have h := unilateral_nilpotent_blocks_sq_zero hYne
  exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1⟩

/-! ## Feature F4: Real-API BKM Bridge & Type III Separation -/

theorem t1_f4_real_bkm_context_constructors_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P * P = P) (hPT : Pᵀ = P)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (A : Matrix ι ι ℝ) (Φ : Matrix ι ι ℝ) (hΦT : Φᵀ = Φ) (hOdd : P * Φ + Φ * P = Φ) :
    let ctx1 := RealTwoSheetBKMContext.ofCoupledCorner P hP hPT p q hp hq A
    let ctx2 := RealTwoSheetBKMContext.ofOddAnticomm P hP hPT p q hp hq Φ hΦT hOdd
    ctx1.density.PosDef ∧
    ctx2.density.PosDef ∧
    ctx1.Φ = component10 P A + component01 P Aᵀ ∧
    ctx2.Φ = Φ ∧
    P * ctx2.Φ * P = 0 ∧
    (1 - P) * ctx2.Φ * (1 - P) = 0 ∧
    0 ≤ ctx1.bkmPairing ctx1.Φ ctx1.Φ ∧
    0 ≤ ctx2.bkmPairing ctx2.Φ ctx2.Φ ∧
    (Φ ≠ 0 → 0 < ctx2.bkmPairing ctx2.Φ ctx2.Φ) := by
  intro ctx1 ctx2
  refine ⟨ctx1.twoSheetReal_posDef, ctx2.twoSheetReal_posDef, rfl, rfl,
    ctx2.P_mul_Φ_mul_P, ctx2.one_sub_P_mul_Φ_mul_one_sub_P, ?_, ?_,
    fun hΦ => ctx2.bkmPairing_self_pos hΦ⟩
  · rw [ctx1.bkmPairing_self_eq_quadratic]
    exact ctx1.quadratic_nonneg
  · rw [ctx2.bkmPairing_self_eq_quadratic]
    exact ctx2.quadratic_nonneg

theorem t1_f4_real_bkm_trace_left_and_sandwich
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ctx : RealTwoSheetBKMContext ι) (X : Matrix ι ι ℝ) :
    (∫ s in Ioi (0 : ℝ),
      Matrix.trace (X * ctx.resolvent s * ctx.Φ * ctx.resolvent s)) =
      logDividedDifference ctx.p ctx.q * Matrix.trace (X * ctx.Φ) ∧
    (∫ s in Ioi (0 : ℝ),
      ctx.resolvent s * ctx.Φ * ctx.resolvent s) =
      logDividedDifference ctx.p ctx.q • ctx.Φ :=
  ⟨ctx.trace_left X,
    integral_twoSheetResolventReal_sandwich ctx.P ctx.P_idempotent ctx.Φ
      ctx.P_mul_Φ_mul_P ctx.one_sub_P_mul_Φ_mul_one_sub_P ctx.p_pos ctx.q_pos⟩

theorem t1_f4_real_bkm_quadratic_pos_and_coupledCorner_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P * P = P) (hPT : Pᵀ = P)
    (A : Matrix ι ι ℝ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (0 < (∫ s in Ioi (0 : ℝ),
      Matrix.trace ((component10 P A + component01 P Aᵀ) *
        twoSheetResolventReal P p q s *
        (component10 P A + component01 P Aᵀ) *
        twoSheetResolventReal P p q s)) ↔
      component10 P A ≠ 0) ∧
    (component10 P A ≠ 0 →
      0 < (RealTwoSheetBKMContext.ofCoupledCorner P hP hPT p q hp hq A).bkmPairing
        (RealTwoSheetBKMContext.ofCoupledCorner P hP hPT p q hp hq A).Φ
        (RealTwoSheetBKMContext.ofCoupledCorner P hP hPT p q hp hq A).Φ) := by
  have hiff := real_twoSheetResolvent_coupledCorner_pos_iff P hP hPT A hp hq
  refine ⟨hiff, fun hne => ?_⟩
  let ctx := RealTwoSheetBKMContext.ofCoupledCorner P hP hPT p q hp hq A
  rw [ctx.bkmPairing_self_eq_quadratic]
  exact hiff.mpr hne

theorem t1_f4_concrete_real_bkm_context_eval :
    0 < concreteRealTwoSheetBKMContext.bkmPairing
      concreteRealTwoSheetBKMContext.Φ concreteRealTwoSheetBKMContext.Φ ∧
    concreteRealTwoSheetBKMContext.bkmPairing
      concreteRealTwoSheetBKMContext.Φ concreteRealTwoSheetBKMContext.Φ =
      logDividedDifference 1 2 * 2 := by
  have hΦne : concreteRealTwoSheetBKMContext.Φ ≠ 0 := by
    intro h0
    have h01 := congrFun (congrFun h0 0) 1
    simp [concreteRealTwoSheetBKMContext] at h01
  have htr : Matrix.trace (concreteRealTwoSheetBKMContext.Φ * concreteRealTwoSheetBKMContext.Φ) = 2 := by
    have hsq : concreteRealTwoSheetBKMContext.Φ * concreteRealTwoSheetBKMContext.Φ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [concreteRealTwoSheetBKMContext, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hsq, Matrix.trace_one]
    norm_num
  refine ⟨concreteRealTwoSheetBKMContext.bkmPairing_self_pos hΦne, ?_⟩
  rw [concreteRealTwoSheetBKMContext.bkmPairing_self_eq_quadratic,
    concreteRealTwoSheetBKMContext.quadratic_trace, htr]
  rfl

theorem t1_f4_finite_trace_vs_typeIII_separation :
    (∀ A C : Matrix (Fin 2) (Fin 2) ℝ, A * C = 1 → C * A = 1) ∧
    (¬ ∃ V : Matrix (Fin 2) (Fin 2) ℝ, star V * V = 1 ∧ V * star V ≠ 1) ∧
    (¬ ∃ P u₁ v₁ u₂ v₂ : Matrix (Fin 2) (Fin 2) ℝ,
      u₁ * v₁ = 1 ∧ v₁ * u₁ = P ∧ u₂ * v₂ = 1 ∧ v₂ * u₂ = 1 - P) ∧
    (¬ ∃ τ : Module.End ℝ (ℕ → ℝ) →ₗ[ℝ] ℝ,
      (∀ a b : Module.End ℝ (ℕ → ℝ), τ (a * b) = τ (b * a)) ∧ τ 1 ≠ 0) ∧
    IsEmpty (Module.End ℝ (ℕ → ℝ) →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨fun A C hAC => canonicalFiniteTraceVsTypeIIISeparation.finiteMatrix_dedekindFinite A C hAC,
    canonicalFiniteTraceVsTypeIIISeparation.finite_no_nonunitary_starIsometry,
    canonicalFiniteTraceVsTypeIIISeparation.finite_no_typeIII_halving,
    canonicalFiniteTraceVsTypeIIISeparation.boundary_no_unital_tracial_functional,
    canonicalFiniteTraceVsTypeIIISeparation.no_algHom_boundary_to_finite⟩

/-! ## Feature F5: R5 Separations (dim E > 1 Nullcone, J ↦ -J, Hyperbolic Plane) -/

theorem t1_f5_dim_gt_one_fin2_nullcone_outside_chiral :
    ∃ u : DoubledSpace (EuclideanSpace ℝ (Fin 2)),
      u ≠ 0 ∧
      chiralKreinForm u u = 0 ∧
      leftChiralProjector u ≠ u ∧
      rightChiralProjector u ≠ u := by
  have hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  exact dim_gt_one_nullcone_not_in_chiral hdim

theorem t1_f5_nullconeNullPolarization_outside_chiral
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (b : LinearMap.BilinForm ℝ H)
    (hsym : ∀ u v : H, b u v = b v u)
    (hnd : IsNondegeneratePairing b)
    {e₁ e₂ : H} (he₁ : e₁ ≠ 0) (he₂ : e₂ ≠ 0) (horth : b e₁ e₂ = 0) :
    let P := NullPolarizationData.nullconeNullPolarization b hsym hnd
    let u : H × H := (e₁, e₂)
    u ≠ 0 ∧ P.b u u = 0 ∧ P.projPlus u ≠ u ∧ P.projMinus u ≠ u := by
  intro P u
  let x₁ : H × H := (e₁, (0 : H))
  let x₂ : H × H := (e₂, (0 : H))
  have hx₁_ne : x₁ ≠ 0 := by
    intro h0
    exact he₁ (congrArg Prod.fst h0)
  have hx₂_ne : x₂ ≠ 0 := by
    intro h0
    exact he₂ (congrArg Prod.fst h0)
  have hx₁_mem : x₁ ∈ P.nullPlusSubmodule := by
    rw [P.mem_nullPlusSubmodule_iff]
    change (e₁, -(0 : H)) = (e₁, (0 : H))
    simp
  have hx₂_mem : x₂ ∈ P.nullPlusSubmodule := by
    rw [P.mem_nullPlusSubmodule_iff]
    change (e₂, -(0 : H)) = (e₂, (0 : H))
    simp
  have hx_orth : P.b x₁ (P.J x₂) = 0 := by
    change b e₁ e₂ + b (0 : H) (0 : H) = 0
    simp [horth]
  have hu_eq : x₁ + P.J x₂ = u := by
    change (e₁, (0 : H)) + ((0 : H), e₂) = (e₁, e₂)
    ext <;> simp
  have hres := P.exists_null_outside_chiral_of_orthogonal hx₁_ne hx₂_ne hx₁_mem hx₂_mem hx_orth
  dsimp only at hres
  rwa [hu_eq] at hres

theorem t1_f5_sign_flip_neg_mirror_abstract_and_doubled
    {V : Type*} [AddCommGroup V] [Module ℝ V] [Nontrivial V]
    (P : NullPolarizationData V) (hpos : PositiveHilbertCompatibility P) :
    (P.negMirror.Γ = P.Γ ∧ P.negMirror.J = -P.J) ∧
    (∀ u v : V, P.negMirror.gJ u v = -P.gJ u v) ∧
    ¬ PositiveHilbertCompatibility P.negMirror ∧
    (∃ u : DoubledSpace ℝ, u ≠ 0 ∧
      chiralKreinForm u (-(etaChiral (E := ℝ)) u) < 0) :=
  ⟨(sign_flip_neg_mirror P hpos).1,
    (sign_flip_neg_mirror P hpos).2.1,
    (sign_flip_neg_mirror P hpos).2.2,
    (realDoubled_sign_flip_neg_mirror (E := ℝ)).2.2.2.2⟩

theorem t1_f5_hyperbolic_plane_krein_selfadjoint_sq_neg_one :
    hyperbolicPlaneGamma * hyperbolicPlaneGamma = 1 ∧
    hyperbolicPlaneGamma * hyperbolicPlaneF + hyperbolicPlaneF * hyperbolicPlaneGamma = 0 ∧
    hyperbolicPlaneGamma * hyperbolicPlaneFᵀ * hyperbolicPlaneGamma = hyperbolicPlaneF ∧
    hyperbolicPlaneJ * hyperbolicPlaneFᵀ * hyperbolicPlaneJ = hyperbolicPlaneF ∧
    hyperbolicPlaneF * hyperbolicPlaneF = -(1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    ¬ (hyperbolicPlaneF * hyperbolicPlaneF).PosSemidef :=
  hyperbolicPlane_kreinSelfAdjoint_sq_neg_one

theorem t1_f5_hyperbolic_plane_clockAxis_bridge
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : DoubledSpace ℝ) :
    doubledRealEquiv (-(clockAxis u)) = hyperbolicPlaneF *ᵥ doubledRealEquiv u ∧
    doubledRealEquiv (gamma5 u) = hyperbolicPlaneGamma *ᵥ doubledRealEquiv u ∧
    doubledRealEquiv (etaChiral u) = hyperbolicPlaneJ *ᵥ doubledRealEquiv u ∧
    IsChiralKreinSelfAdjoint (clockAxis (E := E)) ∧
    (clockAxis (E := E)).comp (clockAxis (E := E)) =
      -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  have hb := hyperbolicPlane_clockAxis_bridge (E := E)
  exact ⟨hb.2.1 u, hb.2.2.1 u, hb.2.2.2.1 u, hb.2.2.2.2.1, hb.2.2.2.2.2.2⟩

end PolarizedZ2E2E.Tier1R1

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
