/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPolarization
import InfoGeometry.NCG.OppositePeirceRealMetric
import InfoGeometry.NCG.PeirceProjectorSpectralBounds
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKMReal
import InfoGeometry.Canonical.CurvedZ2GradedDGA
import InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
import InfoGeometry.OperatorAlgebra.ProjectorCurvatureSplitting
import InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
import InfoGeometry.Core.OperatorCliffordDouble
import InfoGeometry.Clifford.Cl30RealMatrixSignature
import InfoGeometry.Algebra.RegularActionAssociator
import InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation
import InfoGeometry.Algebra.Zorn.SplitOctonionPeirceG2Unification
import InfoGeometry.Clifford.Cl11TensorTowerLimit
import InfoGeometry.Canonical.BostConnesKMS
import InfoGeometry.Canonical.BostConnesColimitKMSBridge
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false

/-!
# Tier 4 E2E Tests: Real-World Application Scenarios (Scenarios 1–8)

End-to-end application workflows chaining `M1`–`M5` public APIs across all
eight application scenarios specified in `TEST_INFRA.md § 4`.
-/

namespace PolarizedZ2E2E.Tier4

open Matrix MeasureTheory Set
open InfoGeometry.Krein
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.Core.PeirceGrading
open InfoGeometry.Analysis
open InfoGeometry.Algebra (DerivationLieLane)
open InfoGeometry.Algebra.GradedNullconeAlgebra
open InfoGeometry.Algebra.DerivationLieLane
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.DerivationMatrixGeometry
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinPolarization
open InfoGeometry.NCG.OppositePeirceCoupling
open InfoGeometry.NCG.OppositePeirceTrace
open InfoGeometry.NCG.OppositePeirceRealMetric
open InfoGeometry.NCG.PeirceProjectorSpectralBounds
open InfoGeometry.OperatorAlgebra.PeirceSpine.TwoSheetBKMReal
open InfoGeometry.Canonical.CurvedZ2GradedDGA
open InfoGeometry.OperatorAlgebra.MaurerCartanFrameTransport
open InfoGeometry.OperatorAlgebra.ProjectorCurvatureSplitting
open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ThreeDHurwitz
open InfoGeometry.Clifford.Cl11SplitTowerMatrixEquiv
open InfoGeometry.Core.OperatorCliffordDouble
open InfoGeometry.Clifford.Cl30RealMatrixSignature
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation
open InfoGeometry.Algebra.Zorn.SplitOctonionPeirceG2Unification
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.BostConnesKMS
open InfoGeometry.Canonical.BostConnesColimitKMSBridge

/-- Scenario 1 (`F1, F2, F5`): Polarized doubled Krein quantization on
`EuclideanSpace ℝ (Fin 2)` (`dim E = 2 > 1`), Hadamard diagonal-Krein coordinate change,
nullcone witness outside both chiral subspaces, `ChiralObservablesDynamics` energy and
mass-gap positivity, and `J ↦ -J` sign inversion. -/
theorem t4_scenario1_polarized_doubled_krein_quantization :
    let E := EuclideanSpace ℝ (Fin 2)
    let P := NullPolarizationData.doubledNullPolarization E
    let D := doubledDiagonalKreinData E
    let eqv := HadamardKreinPolarizationEquiv.doubledHadamardKreinPolarizationEquiv E
    let hpos := PositiveHilbertCompatibility.doubledPositiveHilbertCompatibility E
    let dyn := ChiralObservablesDynamics.ofOddGenerator hpos P.J
      (by
        apply LinearMap.ext
        intro u
        exact (NullPolarizationData.doubledNullPolarization E).J_Γ_apply u)
      (fun u v => by
        rw [NullPolarizationData.gJ_apply, NullPolarizationData.gJ_apply,
          NullPolarizationData.J_apply_J]
        exact P.b_J_invariant u v)
      (1 : ℝ) one_pos
    (∀ u v : DoubledSpace E, P.b (eqv.toLinearEquiv u) (eqv.toLinearEquiv v) = D.bDiag u v) ∧
      (∃ u : DoubledSpace E,
        u ≠ 0 ∧ chiralKreinForm (E := E) u u = 0 ∧
          leftChiralProjector (E := E) u ≠ u ∧ rightChiralProjector (E := E) u ≠ u) ∧
      (∀ v : DoubledSpace E, v ≠ 0 → 0 < P.gJ v (dyn.H v)) ∧
      (∀ (μ : ℝ) (v : DoubledSpace E), v ≠ 0 → dyn.H v = μ • v → dyn.m₀ ≤ μ) ∧
      ((∀ u v : DoubledSpace E, P.negMirror.gJ u v = -P.gJ u v) ∧
        ¬ PositiveHilbertCompatibility P.negMirror) := by
  let E := EuclideanSpace ℝ (Fin 2)
  let P := NullPolarizationData.doubledNullPolarization E
  let D := doubledDiagonalKreinData E
  let eqv := HadamardKreinPolarizationEquiv.doubledHadamardKreinPolarizationEquiv E
  let hpos := PositiveHilbertCompatibility.doubledPositiveHilbertCompatibility E
  let dyn := ChiralObservablesDynamics.ofOddGenerator hpos P.J
    (by
      apply LinearMap.ext
      intro u
      exact (NullPolarizationData.doubledNullPolarization E).J_Γ_apply u)
    (fun u v => by
      rw [NullPolarizationData.gJ_apply, NullPolarizationData.gJ_apply,
        NullPolarizationData.J_apply_J]
      exact P.b_J_invariant u v)
    (1 : ℝ) one_pos
  have hdim : 1 < Module.finrank ℝ E := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hflip := sign_flip_neg_mirror P hpos
  exact ⟨eqv.map_form, dim_gt_one_nullcone_not_in_chiral hdim,
    fun _ hv => dyn.energy_pos hv,
    fun _ _ hv heig => dyn.eigenvalue_ge_gap hv heig,
    ⟨hflip.2.1, hflip.2.2⟩⟩

/-- Scenario 2 (`F2, F3, F4`): Orthogonal-projector Peirce spectral gap (`0 ≤ F² ≤ (1/4) I`
and `I - F² ≥ (3/4) I`) chained into `RealTwoSheetBKMContext.ofOddAnticomm`, proving strict
positivity of the real two-sheet BKM resolvent integral alongside Dedekind-finite separation
from Type III algebras. -/
theorem t4_scenario2_orthogonal_projector_spectral_gap_real_bkm
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {B_inf : Type*} [Ring B_inf] [Algebra ℝ B_inf]
    (P Ω : Matrix ι ι ℝ)
    (hP : IsIdempotentElem P) (hPT : Pᵀ = P)
    (hΩ : IsIdempotentElem Ω) (hΩT : Ωᵀ = Ω)
    (hFne : odd P Ω ≠ 0) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (sep : FiniteTraceBKMVsTypeIIISeparation ι B_inf) :
    let F := odd P Ω
    let hPs : P.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hPT
    let hΩs : Ω.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hΩT
    let hFT : Fᵀ = F := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (odd_isHermitian hPs hΩs).eq
    let hFOdd : P * F + F * P = F := (mem_odd_iff hP).mp ⟨Ω, rfl⟩
    let ctx := RealTwoSheetBKMContext.ofOddAnticomm P hP.eq hPT p q hp hq F hFT hFOdd
    F.IsHermitian ∧
      (F * F).PosSemidef ∧
      ((1 / 4 : ℝ) • (1 : Matrix ι ι ℝ) - F * F).PosSemidef ∧
      (((1 : Matrix ι ι ℝ) - F * F) - (3 / 4 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef ∧
      ((1 : Matrix ι ι ℝ) - F * F).PosDef ∧
      ctx.density.PosDef ∧
      0 < (∫ s in Ioi (0 : ℝ),
        Matrix.trace (F * twoSheetResolventReal P p q s * F * twoSheetResolventReal P p q s)) ∧
      IsEmpty (B_inf →ₐ[ℝ] Matrix ι ι ℝ) := by
  have hPs : P.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hPT
  have hΩs : Ω.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hΩT
  have hFT : (odd P Ω)ᵀ = odd P Ω := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using (odd_isHermitian hPs hΩs).eq
  have hFOdd : P * odd P Ω + odd P Ω * P = odd P Ω := (mem_odd_iff hP).mp ⟨Ω, rfl⟩
  let ctx := RealTwoSheetBKMContext.ofOddAnticomm P hP.eq hPT p q hp hq (odd P Ω) hFT hFOdd
  have hquarter := orthogonalProjector_F_sq_le_quarter hP hPs hΩ hΩs
  have h3q := orthogonalProjector_one_sub_F_sq_ge_three_quarters hP hPs hΩ hΩs
  have hbkm := real_twoSheetResolvent_quadratic_pos P hP.eq (odd P Ω) hFT
    ctx.P_mul_Φ_mul_P ctx.one_sub_P_mul_Φ_mul_one_sub_P hFne hp hq
  exact ⟨odd_isHermitian hPs hΩs, hquarter.1, hquarter.2.1, h3q.1, h3q.2,
    ctx.twoSheetReal_posDef, hbkm, sep.no_algHom_boundary_to_finite⟩

/-- Scenario 3 (`F6, F7, F8`): Curved `ℤ/2`-graded gauge fluctuation complex
`nonCentralMat4DGA` verifying graded Leibniz, `∂_F²(A) = [F², A] ≠ 0`, Bianchi identity
`∂_F(F²) = 0`, and sharp separation from ungraded commutator derivations `D_G`
(`G² = 0 ∧ D_G² ≠ 0` vs `∂_G² = 0`). -/
theorem t4_scenario3_curved_z2_graded_gauge_fluctuation_complex
    (H2 : Matrix (Fin 2) (Fin 2) ℝ) :
    let D := nonCentralMat4DGA
    (∀ x y : Matrix (Fin 4) (Fin 4) ℝ,
        D.diff (x * y) = D.diff x * y + D.parity x * D.diff y) ∧
      IsNonCentralRegime D.curvature ∧
      D.diff ^ 2 ≠ 0 ∧
      (∀ x : Matrix (Fin 4) (Fin 4) ℝ, D.diff (D.diff x) = D.curvature * x - x * D.curvature) ∧
      D.diff D.curvature = 0 ∧
      flatMat2DGA.diff ≠ commutatorDeriv (R := ℝ) H2 ∧
      (atomNeg2 * atomNeg2 = 0 ∧ (commutatorDeriv (R := ℝ) atomNeg2) ^ 2 ≠ 0 ∧
        flatMat2DGA.diff ^ 2 = 0) := by
  exact ⟨nonCentralMat4DGA.diff_mul, nonCentralMat4DGA_isNonCentral,
    nonCentralMat4DGA_diff_sq_ne_zero,
    fun x => nonCentralMat4DGA.diff_sq_apply x,
    nonCentralMat4DGA_bianchi,
    flatMat2DGA_diff_ne_commutatorDeriv H2,
    ⟨nilpotent_commutatorDeriv_sq_ne_zero.1,
      nilpotent_commutatorDeriv_sq_ne_zero.2.2.2.1,
      flatMat2DGA_diff_sq⟩⟩

/-- Scenario 4 (`F9, F10, F12`): Flat Maurer–Cartan frame splitting `θ = ϖ + e` into
even Cartan connection `ϖ` and odd soldering `e`, deriving `R_ϖ = -e ∧ e` and
`de + [ϖ, e] = 0`, verifying isotropy covariance, and attaching `SolderingOneForm`
equivariance and bijectivity. -/
theorem t4_scenario4_flat_maurer_cartan_frame_soldering
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (K : DerivationLieLane R A) {P : A} (hP : P * P = P)
    (hKP : ∀ z : K.L, K.operatorAction z P = 0)
    (g : Aˣ) {H : Subgroup Aˣ} (S : SolderingOneForm K P H)
    {h : Aˣ} (hh : h ∈ peirceIsotropySubgroup A P) (hH : H) (x y : K.L) :
    let θ := gaugeForm K g
    let ϖ := peirceEvenOneForm K P θ
    let e := peirceOddOneForm K P θ
    gaugeForm K (g * h) x = frameTransport h (θ x) + gaugeForm K h x ∧
      connectionCurvature K (gaugeForm K (g * h)) = 0 ∧
      θ = ϖ + e ∧
      connectionCurvature K ϖ x y = -(e x * e y - e y * e x) ∧
      exteriorDerivativeOne K e x y + (ϖ x * e y - e y * ϖ x) -
        (ϖ y * e x - e x * ϖ y) = 0 ∧
      peirceOddOneForm K P (gaugeForm K (g * h)) x = frameTransport h (e x) ∧
      S.toOneForm (S.baseRightAct hH x) = frameTransport (hH.1 : Aˣ) (S.toOneForm x) ∧
      Function.Bijective S.frameEquiv := by
  have hsep := gaugeForm_product_general_separation K g h x
  have hcart := gaugeForm_graded_split_cartan_equations K hP hKP g x y
  have hiso := peirceSplit_gaugeForm_isotropy_transform K hP hKP g hh x
  exact ⟨hsep.1, hsep.2.2.2.1, hcart.1, hcart.2.1, hcart.2.2, hiso.2,
    S.equivariant hH x, S.frameEquiv.bijective⟩

/-- Scenario 5 (`F3, F11`): Adiabatic Berry / Grassmann projector curvature
`P [D₁ P, D₂ P] P = Y₁ X₂ - Y₂ X₁ = star X₁ * X₂ - star X₂ * X₁`, linking self-adjoint
projector derivatives `Dᵢ P` to the positive-adjoint `F² ≥ 0` regime and witnessing
nonzero Berry curvature in `M₃(ℝ)`. -/
theorem t4_scenario5_adiabatic_berry_projector_curvature_spectral
    {m : Type*} [Fintype m] [DecidableEq m]
    {P : Matrix m m ℝ} (hP : IsIdempotentElem P) (hPs : P.IsHermitian)
    (D₁ D₂ : Matrix m m ℝ → Matrix m m ℝ)
    (hD₁ : ∀ a b, D₁ (a * b) = D₁ a * b + a * D₁ b)
    (hD₂ : ∀ a b, D₂ (a * b) = D₂ a * b + a * D₂ b)
    (hD₁star : ∀ a, D₁ (star a) = star (D₁ a))
    (hD₂star : ∀ a, D₂ (star a) = star (D₂ a)) :
    let X₁ := coneMinus P (D₁ P)
    let X₂ := coneMinus P (D₂ P)
    let Y₁ := conePlus P (D₁ P)
    let Y₂ := conePlus P (D₂ P)
    D₁ P = X₁ + Y₁ ∧
      P * (D₁ P * D₂ P - D₂ P * D₁ P) * P = Y₁ * X₂ - Y₂ * X₁ ∧
      P * (D₁ P * D₂ P - D₂ P * D₁ P) * P = star X₁ * X₂ - star X₂ * X₁ ∧
      (D₁ P * D₁ P).PosSemidef ∧
      (D₂ P * D₂ P).PosSemidef ∧
      mat3P * ((matrixDerivationsLane ℝ (Fin 3)).operatorAction
          (matrixInnerLieHom ℝ (Fin 3) mat3S1) mat3P *
        (matrixDerivationsLane ℝ (Fin 3)).operatorAction
          (matrixInnerLieHom ℝ (Fin 3) mat3S2) mat3P -
        (matrixDerivationsLane ℝ (Fin 3)).operatorAction
          (matrixInnerLieHom ℝ (Fin 3) mat3S2) mat3P *
        (matrixDerivationsLane ℝ (Fin 3)).operatorAction
          (matrixInnerLieHom ℝ (Fin 3) mat3S1) mat3P) * mat3P ≠ 0 := by
  have hsplit := projector_deriv_peirce_split hP.eq D₁ hD₁
  have hcurv := projected_two_direction_curvature hP.eq D₁ D₂ hD₁ hD₂
  have hstar := projected_two_direction_curvature_star hP.eq hPs.eq D₁ D₂ hD₁ hD₂ hD₁star hD₂star
  have hD₁_herm : (D₁ P).IsHermitian := by
    change star (D₁ P) = D₁ P
    rw [← hD₁star P]
    exact congrArg D₁ hPs.eq
  have hD₂_herm : (D₂ P).IsHermitian := by
    change star (D₂ P) = D₂ P
    rw [← hD₂star P]
    exact congrArg D₂ hPs.eq
  have hpsd1 : (D₁ P * D₁ P).PosSemidef := by
    nth_rw 2 [← hD₁_herm.eq]
    exact Matrix.posSemidef_self_mul_conjTranspose (D₁ P)
  have hpsd2 : (D₂ P * D₂ P).PosSemidef := by
    nth_rw 2 [← hD₂_herm.eq]
    exact Matrix.posSemidef_self_mul_conjTranspose (D₂ P)
  exact ⟨hsplit, hcurv, hstar, hpsd1, hpsd2, mat3_projected_curvature_star_ne_zero.2⟩

/-- Scenario 6 (`F13, F14`): Real Clifford signature discrimination lifting real algebras
through `cliffordTensorEquivMatrix` and `blockMatrixAlgEquiv`, constructing
`Cl(3,0) ≃ₐ[ℝ] M₂(ℂ)` vs `Cl(2,2) ≃ₐ[ℝ] M₄(ℝ)`, and certifying non-isomorphism via
dimension, center rank, and central `z² = -1` invariants. -/
theorem t4_scenario6_real_clifford_signature_discrimination
    (k : ℕ) {A : Type*} [Ring A] [Algebra ℝ A] (a : A)
    (M : Type*) [AddCommMonoid M] [Module ℝ M] :
    cliffordTensorEquivMatrix k A ((1 : Clsplit k) ⊗ₜ[ℝ] a) = Matrix.scalar (Fin (2 ^ k)) a ∧
      Nonempty (Matrix (Fin 2) (Fin 2) (Module.End ℝ M) ≃ₐ[ℝ] Module.End ℝ (M × M)) ∧
      Nonempty (Cl3 1 1 1 ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) ∧
      Nonempty (Clsplit 2 ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) ∧
      Module.finrank ℝ (Subalgebra.center ℝ (Cl3 1 1 1)) = 2 ∧
      Module.finrank ℝ (Subalgebra.center ℝ (Clsplit 2)) = 1 ∧
      (∃ z ∈ Subalgebra.center ℝ (Cl3 1 1 1), z ^ 2 = -1) ∧
      (∀ z ∈ Subalgebra.center ℝ (Clsplit 2), z ^ 2 ≠ -1) ∧
      ¬ Nonempty (Cl3 1 1 1 ≃ₐ[ℝ] Clsplit 2) ∧
      ¬ Nonempty (Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) := by
  exact ⟨cliffordTensorEquivMatrix_one_tmul k A a,
    ⟨blockMatrixAlgEquiv⟩, ⟨cl30EquivMat2C⟩, ⟨cl22EquivMat4R⟩,
    cl30_center_finrank, cl22_center_finrank,
    cl30_exists_central_sq_neg_one, cl22_no_central_sq_neg_one,
    cl30_not_algEquiv_cl22, mat2C_not_algEquiv_mat4R⟩

/-- Scenario 7 (`F13, F15`): Split-octonion Peirce `2×2` Zorn decomposition,
`M₈(ℝ) ≃ₐ[ℝ] End_ℝ(ZornCarrier)`, associator defect `[L_x, R_y] z = -zornAssociator x z y`,
`G_{2(2)}` automorphism conjugation & 14-dimensional derivation algebra, and R5
non-multiplicativity obstructions. -/
theorem t4_scenario7_split_octonion_zorn_associator_g2_symmetry
    (φ : InfoGeometry.Canonical.RealSplitOctonionAut) (x y z : ZornCarrier) :
    z = peirce11 peirceP z + conePlus peirceP z + coneMinus peirceP z + peirce00 peirceP z ∧
      mat8EquivEndZorn (leftMulMat8 x) = leftMulEnd x ∧
      lrComm x y z = -zornAssociator x z y ∧
      lrComm x y z = zornAssociator x y z ∧
      autMat8 φ * leftMulMat8 x * (autMat8 φ)⁻¹ = leftMulMat8 (φ.1 x) ∧
      autMat8 φ * lrCommMat8 x y * (autMat8 φ)⁻¹ = lrCommMat8 (φ.1 x) (φ.1 y) ∧
      Module.finrank ℝ canonicalZornDerivations = 14 ∧
      (∃ u v : ZornCarrier, leftMulEnd (u * v) ≠ leftMulEnd u ∘ₗ leftMulEnd v) ∧
      (∃ u v : ZornCarrier, leftMulMat8 (u * v) ≠ leftMulMat8 u * leftMulMat8 v) ∧
      ¬ (∃ f : InfoGeometry.Algebra.FiniteSpin.Mat2C → ZornCarrier,
          Function.Surjective f ∧ ∀ A B, f (A * B) = f A * f B) := by
  refine ⟨zorn_peirce_decomposition z, ?_,
    lrComm_apply_eq_neg_associator x y z,
    lrComm_apply_eq_associator x y z,
    autMat8_conj_leftMulMat8 φ x,
    autMat8_conj_lrCommMat8 φ x y,
    g2_derivation_finrank_and_standard_span.1,
    leftMulEnd_not_multiplicative,
    leftMulMat8_not_multiplicative,
    no_surjective_multiplicative_mat2C_to_zornCarrier⟩
  change mat8EquivEndZorn (endToMat8 (leftMulEnd x)) = leftMulEnd x
  exact endToMat8.symm_apply_apply (leftMulEnd x)

/-- Scenario 8 (`F13, F16`): Finite-stage Clifford matrix equivalence via
`cliffordTensorEquivMatrix`, inductive colimit `Cl11TensorTowerLimit.Limit`,
`CliffordTowerKMSBridgeSystem` bridging to `KMSProjectionState` normalized at
`Re ζ(β)` with total Boltzmann mass `1`, and nontrivial modular-shift separation
from `traceKMSBridgeModel`. -/
theorem t4_scenario8_inductive_limit_clifford_tower_to_bost_connes_kms
    (k n : ℕ) (X : Stage n)
    (Sys : CliffordTowerKMSBridgeSystem)
    (C : BostConnesCuntzSystem Sys.completion.Carrier)
    {β : ℝ} (hβ : 1 < β)
    (h_scale : ∀ m : ℕ+, Sys.modular.σ_imag (S C m) = ((m : ℝ) ^ (-β)) • S C m)
    (h_scale_star : ∀ m : ℕ+, Sys.modular.σ_imag (star (S C m)) = ((m : ℝ) ^ β) • star (S C m)) :
    let Φ := bostConnesKMSProjectionState Sys C hβ h_scale h_scale_star
    cliffordTensorEquivMatrix k ℝ ((1 : Clsplit k) ⊗ₜ[ℝ] (1 : ℝ)) = 1 ∧
      ofStage (n + 1) (stageBond n X) = ofStage n X ∧
      (∃ a b : Limit, a * b ≠ b * a) ∧
      Φ.ζβ = (riemannZeta (β : ℂ)).re ∧
      (∀ m : ℕ+, Φ.φ (S C m * star (S C m)) = normalizedBostConnesWeight β m) ∧
      (∑' m : ℕ+, Φ.φ (S C m * star (S C m))) = 1 ∧
      (∀ m : ℕ+, 0 < Φ.φ (S C m * star (S C m))) ∧
      Sys.limitState (ofStage (n + 1) (stageBond n X)) = Sys.limitState (ofStage n X) ∧
      Sys.modular.σ_imag ≠ AlgHom.id ℝ Sys.completion.Carrier := by
  have h1 : cliffordTensorEquivMatrix k ℝ ((1 : Clsplit k) ⊗ₜ[ℝ] (1 : ℝ)) = 1 := by
    rw [cliffordTensorEquivMatrix_one_tmul]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, hij]
  have hbridge := bostConnes_colimit_kms_partition_bridge Sys C hβ h_scale h_scale_star
  exact ⟨h1, ofStage_apply_bond n X, limit_noncommutative,
    hbridge.1, hbridge.2.1, hbridge.2.2.1, hbridge.2.2.2.1,
    hbridge.2.2.2.2.2 n X,
    bostConnes_kms_requires_nontrivial_modular_shift Sys C hβ h_scale⟩

end PolarizedZ2E2E.Tier4

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
