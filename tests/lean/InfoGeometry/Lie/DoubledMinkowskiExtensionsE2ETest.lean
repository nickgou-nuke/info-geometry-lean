/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
import InfoGeometry.Lie.DoubledMinkowskiGradedDifferentialBridge
import InfoGeometry.Lie.DoubledMinkowskiLatticeContinuumLimit
import InfoGeometry.Lie.DoubledMinkowskiManifoldYangMillsPDE
import InfoGeometry.Meta.Trust

/-!
# End-to-End Verification Suite for Doubled-Minkowski Chiral Yang–Mills Extensions

Opaque-box Tier 1–5 test suite covering:
1. R1: Nonzero graded differential compatibility (`DoubledMinkowskiGradedDifferentialBridge`),
2. R2: Analytic `a → 0` lattice continuum limits (`DoubledMinkowskiLatticeContinuumLimit`),
3. R3: Smooth 4-manifold gauge bundle & Yang–Mills PDE (`DoubledMinkowskiManifoldYangMillsPDE`),
4. Baseline `DoubledMinkowskiCircularChiralYangMillsBridge` integration and kernel
   `InfoGeometry.Meta.Trust.collectHardEvidenceBatch` axiom/hole boundary audit,
5. Tier-5 adversarial hardening probes across M1, M2, M3, and cross-module bridges.
-/

set_option autoImplicit false

noncomputable section

open Lean Elab Command Bundle InfoGeometry.Meta InfoGeometry.Lie
open InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
  (frame coordinateEquiv coordinateEquiv_apply_frame leftMultiplication)
open InfoGeometry.Lie.SplitOctonionEllCrossChannel (uPlus uMinus)
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
open InfoGeometry.Lie.SplitOctonionDoubleChiralSolderingBridge (pauliSolder2x2)
open InfoGeometry.Quantum.PauliSoldering (solder σ0 σ1 σ2 σ3)
open InfoGeometry.Algebra.Zorn.SplitQuaternionCore (lUnit)
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Canonical.ExteriorContractionOperatorBridge
open InfoGeometry.Canonical.MatrixTracedChernWeilBridge
open InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge (curvatureFromConnection)
open InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge
open InfoGeometry.Canonical.SelfDualConnectionCurvatureYangMillsBridge
open InfoGeometry.Canonical.YangMillsSelfDualInstantonBridge
  (matrixHodgeStar isSelfDualCurvature)
open InfoGeometry.Core.IdempotentGraphGrassmannian (idempotencyDefect)
open InfoGeometry.Canonical.RealDoubledChiralKreinFrame hiding FourSpace KreinFrame4
open InfoGeometry.OperatorAlgebra.RealDoubledChiralKrein
  (chiralKreinForm leftChiralProjector rightChiralProjector)
open InfoGeometry.OperatorAlgebra.TetraktysZornYangMillsBridge (firstSheetProjection)
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine
open scoped Manifold Bundle Matrix.Norms.Operator Matrix Topology BigOperators

namespace InfoGeometry.Lie.DoubledMinkowskiExtensionsE2ETest

/-! ## Noncommutativity Regression Witnesses (Matrix Carriers) -/

/-- Closed noncommutativity witness for `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem mat2c_noncomm_regression :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  weylUpperMat_mat2C_noncomm_witness

/-- Closed noncommutativity witness for `Matrix (Fin 4) (Fin 4) ℂ`. -/
theorem mat4c_noncomm_regression :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A :=
  circularConnectionMat4_mat4C_noncomm_witness

/-- Closed noncommutativity witness for `Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ))`. -/
theorem mat4_ext_noncomm_regression :
    ∃ A B : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)), A * B ≠ B * A :=
  chiralProj4_mat4R_noncomm_witness

/-! ## Tier 1: Happy-Path Concrete & Symbolic Contract Tests (F1–F10, 50 Cases) -/

/-! ### F1: R1 Structural Equivalence & Square-Zero No-Go -/

/-- T1-F1-01: Concrete numeric off-block Peirce grading derivation over `ExteriorAlgebra`. -/
theorem t1_f1_01_offblock_peirce_deriv_concrete :
    let U : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) := !![1, 2; 3, 4]
    let L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) := !![5, 6; 7, 8]
    peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) (chiralOffBlock4 U L) =
      chiralOffBlock4 U (-L) :=
  chiralExteriorProj4_peirceGradingDeriv_offBlock _ _

/-- T1-F1-02: Symbolic off-block Peirce grading derivation for arbitrary `U, L`. -/
theorem t1_f1_02_offblock_peirce_deriv_symbolic
    (U L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ))) :
    peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) (chiralOffBlock4 U L) =
      chiralOffBlock4 U (-L) :=
  chiralExteriorProj4_peirceGradingDeriv_offBlock U L

/-- T1-F1-03: Forward direction of `circularGaugeConnection4_eigencondition_iff` for graded diff. -/
theorem t1_f1_03_compat_iff_forward_graded :
    let ω := circularGradedOmega (coordinateEquiv uPlus)
    ∀ i : Fin 8, circularGradedDiff (ω i) = if i.val < 4 then ω i else -ω i :=
  (circularGaugeConnection4_eigencondition_iff circularGradedDiff
    (circularGradedOmega (coordinateEquiv uPlus))).mp (circularGradedDiff_eigencondition _)

/-- T1-F1-04: Backward direction of `circularGaugeConnection4_eigencondition_iff` for even diff. -/
theorem t1_f1_04_compat_iff_backward_even :
    let ω := circularEvenOmega (coordinateEquiv (rootPlus 0))
    let A := circularGaugeConnection4 ω
    matrixExteriorDerivative circularEvenDiff A =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) A := by
  have h := circularEvenDiff_eigencondition (coordinateEquiv (rootPlus 0))
  exact (circularGaugeConnection4_eigencondition_iff circularEvenDiff
    (circularEvenOmega (coordinateEquiv (rootPlus 0)))).mpr
    ((circularGaugeConnection4_eigencondition_iff circularEvenDiff
      (circularEvenOmega (coordinateEquiv (rootPlus 0)))).mp h)

/-- T1-F1-05: `genPhi` invariance on `circularGaugeConnection4 (circularGradedOmega _)`. -/
theorem t1_f1_05_genphi_invariant_on_graded_conn :
    let A := circularGaugeConnection4 (circularGradedOmega (coordinateEquiv uPlus))
    genPhi (chiralExteriorProj4 (Fin 4 → ℂ)) A A = A := by
  intro A
  exact (circularGaugeConnection4_yang_mills_bridge 0 circularGradedDiff
    (circularGradedOmega (coordinateEquiv uPlus)) A).1

/-! ### F2: R1 Nonzero Odd Graded Derivation (`d ≠ 0`, `A ≠ 0`) -/

/-- T1-F2-01: `circularGradedDiff` is strictly nonzero. -/
theorem t1_f2_01_graded_diff_nonzero : circularGradedDiff ≠ 0 :=
  circularGradedDiff_ne_zero

/-- T1-F2-02: `circularGradedDiff` obeys the odd graded Leibniz rule on degree-1 forms. -/
theorem t1_f2_02_graded_diff_leibniz_one_form (y : ExteriorAlgebra ℂ (Fin 4 → ℂ)) :
    let x : ExteriorAlgebra ℂ (Fin 4 → ℂ) := ExteriorAlgebra.ι ℂ (Pi.single 0 1)
    circularGradedDiff (x * y) = circularGradedDiff x * y - x * circularGradedDiff y := by
  intro x
  have hx : IsHomogeneousExteriorDegree 1 x :=
    Submodule.subset_span ⟨fun _ => Pi.single 0 1, by simp [x]⟩
  have hL := circularGradedDiff_isGradedDerivation 1 x y hx
  simpa [sub_eq_add_neg] using hL

/-- T1-F2-03: Compatibility on `uPlus` coordinate. -/
theorem t1_f2_03_graded_diff_compat_uplus :
    let A := circularGaugeConnection4 (circularGradedOmega (coordinateEquiv uPlus))
    matrixExteriorDerivative circularGradedDiff A =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) A :=
  circularGradedDiff_eigencondition (coordinateEquiv uPlus)

/-- T1-F2-04: Instantiation of `circularGaugeConnection4_yang_mills_bridge` with odd diff. -/
theorem t1_f2_04_graded_diff_ym_bridge_instantiation :
    let x := coordinateEquiv (uPlus + uMinus)
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularGradedOmega x)
    curvatureFromConnection circularGradedDiff A = genJ P A A + genV P A A ∧
      evenGrade P (curvatureFromConnection circularGradedDiff A) = genV P A A := by
  have h := circularGradedDiff_yang_mills_bridge (coordinateEquiv (uPlus + uMinus))
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- T1-F2-05: Existence of nondegenerate nonzero curvature witness under `circularGradedDiff`. -/
theorem t1_f2_05_graded_diff_nondegenerate_witness :
    ∃ x : Coordinate,
      let A := circularGaugeConnection4 (circularGradedOmega x)
      A ≠ 0 ∧
      curvatureFromConnection circularGradedDiff A ≠ 0 ∧
      matrixExteriorDerivative circularGradedDiff A =
        peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) A := by
  rcases circularGradedDiff_nondegenerate_witness with ⟨x, hA, hCurv, hCompat, _, _⟩
  exact ⟨x, hA, hCurv, hCompat⟩

/-! ### F3: R1 Complementary Homogeneous 1-Form Derivation -/

/-- T1-F3-01: `circularEvenDiff` is strictly nonzero. -/
theorem t1_f3_01_even_diff_nonzero : circularEvenDiff ≠ 0 :=
  circularEvenDiff_ne_zero

/-- T1-F3-02: `circularEvenOmega` produces a matrix of homogeneous degree-1 forms. -/
theorem t1_f3_02_even_omega_homogeneous_one :
    MatrixIsHomogeneous 1
      (circularGaugeConnection4 (circularEvenOmega (coordinateEquiv (uPlus + rootMinus 1)))) :=
  circularEvenOmega_homogeneous (coordinateEquiv (uPlus + rootMinus 1))

/-- T1-F3-03: Even derivation compatibility on mixed `uPlus + uMinus` coordinate. -/
theorem t1_f3_03_even_diff_compat_mixed :
    let A := circularGaugeConnection4 (circularEvenOmega (coordinateEquiv (uPlus + uMinus)))
    matrixExteriorDerivative circularEvenDiff A =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) A :=
  circularEvenDiff_eigencondition (coordinateEquiv (uPlus + uMinus))

/-- T1-F3-04: Covariant vanishing of `genV P A A` under `circularEvenDiff`. -/
theorem t1_f3_04_even_diff_covariant_vanishing :
    let x := coordinateEquiv (uPlus + rootMinus 0)
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularEvenOmega x)
    covariantDerivative A circularEvenDiff (genV P A A) = 0 :=
  circularEvenDiff_covariant_vanishing (coordinateEquiv (uPlus + rootMinus 0))

/-- T1-F3-05: Even derivation Leibniz check on degree-1 generators. -/
theorem t1_f3_05_even_diff_leibniz_generators :
    let x : ExteriorAlgebra ℂ (Fin 4 → ℂ) := ExteriorAlgebra.ι ℂ (Pi.single 0 1)
    let y : ExteriorAlgebra ℂ (Fin 4 → ℂ) := ExteriorAlgebra.ι ℂ (Pi.single 2 1)
    circularEvenDiff (x * y) = circularEvenDiff x * y + x * circularEvenDiff y :=
  InfoGeometry.CliffordExteriorLift.exteriorLift_even_derivation circularEvenMap _ _

/-! ### F4: R2 Normed Two-Sheet Carrier & Link Transporters -/

/-- T1-F4-01: `Mat4C` Hilbert–Schmidt norm trace matches baseline formula on `uPlus`. -/
theorem t1_f4_01_mat4c_hilbert_schmidt_identity :
    let x := coordinateEquiv uPlus
    ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace =
      ((4 * (wittNorm x ^ 2 + normSq3 (chiralBoostVec x) +
        normSq3 (chiralVorticityVec x)) : ℝ) : ℂ) :=
  circularCurvatureMat4_hilbertSchmidt_action (coordinateEquiv uPlus)

/-- T1-F4-02: Link transporter at `a = 1` is a unit in `Mat4C`. -/
theorem t1_f4_02_link_transport_unit :
    IsUnit (circularLinkTransport (fun _ _ => coordinateEquiv uPlus) 0 0 1) := by
  simpa [circularLinkTransport] using Matrix.isUnit_exp _

/-- T1-F4-03: Link transporter obeys the 1-parameter multiplicative group rule. -/
theorem t1_f4_03_link_transport_additive_group (a b : ℝ) :
    let x : FourSpace → Fin 4 → Coordinate := fun _ _ => coordinateEquiv (rootPlus 0)
    circularLinkTransport x 0 0 (a + b) =
      circularLinkTransport x 0 0 a * circularLinkTransport x 0 0 b := by
  intro x
  simp only [circularLinkTransport]
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _
    (((Commute.refl (circularConnectionMat4 (x 0 0))).smul_left a).smul_right b)

/-- T1-F4-04: Link transporter inverse pair `U(a) * U(-a) = 1`. -/
theorem t1_f4_04_link_transport_inverse_pair :
    let x : FourSpace → Fin 4 → Coordinate := fun _ _ => coordinateEquiv (uPlus + uMinus)
    circularLinkTransport x 0 0 (0.25 : ℝ) * circularLinkTransport x 0 0 (-0.25 : ℝ) = 1 := by
  intro x
  simp only [circularLinkTransport]
  rw [← Matrix.exp_add_of_commute _ _
    (((Commute.refl (circularConnectionMat4 (x 0 0))).smul_left (0.25 : ℝ)).smul_right
      (-0.25 : ℝ)), ← add_smul]
  norm_num

/-- T1-F4-05: Link transporter is continuous in lattice spacing `a : ℝ`. -/
theorem t1_f4_05_link_transport_continuous_spacing
    (x : FourSpace → Fin 4 → Coordinate) (y : FourSpace) (μ : Fin 4) :
    Continuous (fun a : ℝ => circularLinkTransport x y μ a) :=
  circularLinkTransport_continuous x y μ

/-! ### F5: R2 Lattice Covariant Difference `a → 0` Convergence -/

/-- T1-F5-01: Constant `Φ` covariant difference converges to `[A_μ, Φ]`. -/
theorem t1_f5_01_lattice_cov_diff_const_phi (y : FourSpace) (μ : Fin 4) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ _ => circularConnectionMat4 (coordinateEquiv uPlus)
    let Φ : FourSpace → Mat4C := fun _ => circularConnectionMat4 (coordinateEquiv (rootMinus 1))
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y μ a) (𝓝[≠] 0)
      (nhds (continuumCovariantDeriv A Φ y μ)) :=
  tendsto_latticeCovariantDiff _ _ y μ (differentiableAt_const _)

/-- T1-F5-02: Zero connection `A = 0` and linear scalar `Φ` converge to directional derivative. -/
theorem t1_f5_02_lattice_cov_diff_zero_conn_linear_phi (y : FourSpace) :
    let Φ : FourSpace → Mat4C := fun z => (z 0 : ℂ) • (1 : Mat4C)
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff 0 Φ y 0 a) (𝓝[≠] 0)
      (nhds (continuumCovariantDeriv 0 Φ y 0)) := by
  intro Φ
  have hDiff : DifferentiableAt ℝ Φ y := by fun_prop
  exact tendsto_latticeCovariantDiff 0 Φ y 0 hDiff

/-- T1-F5-03: Linear `Φ` combined with non-Abelian circular `A` converges at `μ = 1`. -/
theorem t1_f5_03_lattice_cov_diff_linear_phi_nonabelian_conn
    (c : Fin 4 → Coordinate) (y : FourSpace) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ μ => circularConnectionMat4 (c μ)
    let Φ : FourSpace → Mat4C := fun z =>
      (z 1 : ℂ) • circularConnectionMat4 (coordinateEquiv uMinus)
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y 1 a) (𝓝[≠] 0)
      (nhds (continuumCovariantDeriv A Φ y 1)) := by
  intro A Φ
  have hDiff : DifferentiableAt ℝ Φ y := by fun_prop
  exact tendsto_latticeCovariantDiff A Φ y 1 hDiff

/-- T1-F5-04: General differentiable `Φ` convergence for arbitrary `A`, `y`, `μ`. -/
theorem t1_f5_04_lattice_cov_diff_general_differentiable
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ : Fin 4) (hΦ : DifferentiableAt ℝ Φ y) :
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y μ a) (𝓝[≠] 0)
      (nhds (continuumCovariantDeriv A Φ y μ)) :=
  tendsto_latticeCovariantDiff A Φ y μ hΦ

/-- T1-F5-05: Directional convergence along `μ = 3` for `Φ z = z₃ • chiralProjMat4`. -/
theorem t1_f5_05_lattice_cov_diff_direction_three
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) :
    let Φ : FourSpace → Mat4C := fun z => (z 3 : ℂ) • chiralProjMat4
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y 3 a) (𝓝[≠] 0)
      (nhds (continuumCovariantDeriv A Φ y 3)) := by
  intro Φ
  have hDiff : DifferentiableAt ℝ Φ y := by fun_prop
  exact tendsto_latticeCovariantDiff A Φ y 3 hDiff

/-! ### F6: R2 Wilson Plaquette Curvature & Action `a → 0` Convergence -/

/-- T1-F6-01: Constant non-Abelian plaquette curvature converges at `a → 0`. -/
theorem t1_f6_01_wilson_plaquette_const_nonabelian (y : FourSpace) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ μ =>
      if μ = 0 then circularConnectionMat4 (coordinateEquiv (rootPlus 0))
      else circularConnectionMat4 (coordinateEquiv (rootMinus 1))
    Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A y 0 1 a - 1)) (𝓝[≠] 0)
      (nhds (continuumCurvature A y 0 1)) :=
  tendsto_wilsonPlaquette_curvature _ y 0 1 contDiff_const

/-- T1-F6-02: Coordinate-linear non-Abelian `A` plaquette curvature converges at `a → 0`. -/
theorem t1_f6_02_wilson_plaquette_linear_conn (y : FourSpace) :
    let A : FourSpace → Fin 4 → Mat4C := fun z μ =>
      (z μ : ℂ) • circularConnectionMat4 (coordinateEquiv uPlus)
    Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A y 0 1 a - 1)) (𝓝[≠] 0)
      (nhds (continuumCurvature A y 0 1)) := by
  intro A
  have hA : ContDiff ℝ 2 A := by
    refine contDiff_pi.mpr fun μ => ?_
    have hCoord : ContDiff ℝ 2 (fun z : FourSpace => (z μ : ℂ)) :=
      (Complex.ofRealCLM.comp (EuclideanSpace.proj μ)).contDiff
    exact hCoord.smul contDiff_const
  exact tendsto_wilsonPlaquette_curvature A y 0 1 hA

/-- T1-F6-03: Wilson plaquette Hilbert–Schmidt action converges in `(0, 2)` plane. -/
theorem t1_f6_03_wilson_plaquette_action_tendsto
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (hA : ContDiff ℝ 2 A) :
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A y 0 2 a) (𝓝[≠] 0)
      (nhds (continuumPlaquetteAction A y 0 2)) :=
  tendsto_wilsonPlaquetteAction A y 0 2 hA

/-- T1-F6-04: Continuum plaquette Hilbert–Schmidt action is non-negative. -/
theorem t1_f6_04_continuum_plaquette_action_nonneg
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) :
    0 ≤ continuumPlaquetteAction A y μ ν :=
  continuumPlaquetteAction_nonneg A y μ ν

/-- T1-F6-05: Explicit non-Abelian circular field witness (nonzero F, > 0 action). -/
theorem t1_f6_05_circular_lattice_nonabelian_witness :
    ∃ (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4),
      continuumCurvature A y μ ν ≠ 0 ∧ 0 < continuumPlaquetteAction A y μ ν :=
  let ⟨A, y, μ, ν, _, hCurv, hAct⟩ := circularLattice_nonabelian_continuum_smooth_witness
  ⟨A, y, μ, ν, hCurv, hAct⟩

/-! ### F7: R2 Continuous Colimit Cone Transport Compatibility -/

/-- T1-F7-01: Continuous colimit transport on constant `Mat4C` tower. -/
theorem t1_f7_01_colimit_continuum_const_tower
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4)
    (hA : ContDiff ℝ 2 A) :
    let cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone
        (fun _ => Mat4C) Mat4C :=
      { stepHom := fun _ => CanonicalTwoSheetedInductiveColimit.StarRingHom.id Mat4C
        toColimit := fun _ => CanonicalTwoSheetedInductiveColimit.StarRingHom.id Mat4C
        compat := fun _ _ => rfl }
    Filter.Tendsto
      (fun a : ℝ => (cone.toColimit 0).toRingHom ((a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1)))
      (𝓝[≠] 0)
      (nhds ((cone.toColimit 0).toRingHom (continuumCurvature A y μ ν))) := by
  intro cone
  exact (circularColimit_continuum_transport cone 0
    (CanonicalTwoSheetedInductiveColimit.StarRingHom.id Mat4C) continuous_id
    (fun _ _ => 0) A (fun _ => 1) y μ ν hA (differentiableAt_const _)).2.1

/-- T1-F7-02: Colimit continuum transport into arbitrary normed topological star-ring `B_inf`. -/
theorem t1_f7_02_colimit_continuum_arbitrary_normed_star
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf] [TopologicalSpace B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (hCont : Continuous (fun M : Mat4C => (cone.toColimit k).toRingHom (ι.toRingHom M)))
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4)
    (hA : ContDiff ℝ 2 A) :
    Filter.Tendsto
      (fun a : ℝ => (cone.toColimit k).toRingHom
        (ι.toRingHom ((a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1))))
      (𝓝[≠] 0)
      (nhds ((cone.toColimit k).toRingHom (ι.toRingHom (continuumCurvature A y μ ν)))) :=
  (circularColimit_continuum_transport cone k ι hCont (fun _ _ => 0) A (fun _ => 1)
    y μ ν hA (differentiableAt_const _)).2.1

/-- T1-F7-03: Cocycle step coherence across stage `k` and `k + 1` at the continuum limit. -/
theorem t1_f7_03_colimit_cocycle_step_coherence
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) :
    (cone.toColimit (k + 1)).toRingHom
        ((cone.stepHom k).toRingHom (ι.toRingHom (continuumCurvature A y μ ν))) =
      (cone.toColimit k).toRingHom (ι.toRingHom (continuumCurvature A y μ ν)) :=
  cone.compat k (ι.toRingHom (continuumCurvature A y μ ν))

/-- T1-F7-04: Combined baseline `chiralProjMat4` star-colimit transport and continuum limit. -/
theorem t1_f7_04_colimit_chiral_proj_and_conn_transport
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (x : Coordinate) :
    let ψ : Mat4C →+* B_inf := (cone.toColimit k).toRingHom.comp ι.toRingHom
    ψ chiralProjMat4 * ψ chiralProjMat4 = ψ chiralProjMat4 ∧
      star (ψ chiralProjMat4) = ψ chiralProjMat4 := by
  have h := circularConnection_starColimit_transport cone k ι x
  exact ⟨h.1, h.2.1⟩

/-- T1-F7-05: Continuous real functional preserves `a → 0` convergence of plaquette action. -/
theorem t1_f7_05_colimit_action_trace_continuity
    (f : ℝ → ℝ) (hf : Continuous f)
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4)
    (hA : ContDiff ℝ 2 A) :
    Filter.Tendsto (fun a : ℝ => f (wilsonPlaquetteAction A y μ ν a)) (𝓝[≠] 0)
      (nhds (f (continuumPlaquetteAction A y μ ν))) :=
  (hf.continuousAt.tendsto).comp (tendsto_wilsonPlaquetteAction A y μ ν hA)

/-! ### F8: R3 Smooth 4-Manifold & Rank-4 Chiral Gauge Vector Bundle -/

/-- T1-F8-01: Native Mathlib `IsManifold (𝓡 4) ⊤ FourSpace` instance synthesis. -/
theorem t1_f8_01_fourspace_manifold_instance :
    IsManifold (𝓡 4) ⊤ FourSpace :=
  inferInstance

/-- T1-F8-02: Native Mathlib `ContMDiffVectorBundle` on `Bundle.Trivial FourSpace (Fin 4 → ℂ)`. -/
theorem t1_f8_02_trivial_bundle_smooth_instance :
    ContMDiffVectorBundle ⊤ (Fin 4 → ℂ) (Bundle.Trivial FourSpace (Fin 4 → ℂ)) (𝓡 4) :=
  inferInstance

/-- T1-F8-03: Lifted `chiralBundleProjector` is idempotent on every fiber. -/
theorem t1_f8_03_chiral_bundle_projector_smooth (m : FourSpace) :
    (chiralBundleProjector FourSpace m).comp (chiralBundleProjector FourSpace m) =
      chiralBundleProjector FourSpace m :=
  chiralBundleProjector_idempotent FourSpace m

/-- T1-F8-04: `fiberKreinPairing` pulls back `chiralKreinForm` via `chiralFiberToKreinFrame`. -/
theorem t1_f8_04_krein_frame_bundle_pairing (u v : ChiralFiber) :
    fiberKreinPairing u v =
      chiralKreinForm (E := FourSpace)
        (chiralFiberToKreinFrame u) (chiralFiberToKreinFrame v) :=
  rfl

/-- T1-F8-05: `circularBundleConnection` adds the `Mat4C` 1-form action on bundle sections. -/
theorem t1_f8_05_circular_bundle_connection_apply
    (A : Mat4CForm 1) (σ : FourSpace → ChiralFiber) (x v : FourSpace) :
    circularBundleConnection A σ x v =
      fderiv ℝ σ x v + (A x (fun _ => v)).mulVec (σ x) :=
  circularBundleConnection_apply A σ x v

/-! ### F9: R3 Matrix-Valued Differential Forms, Curvature & Differential Bianchi -/

private lemma local_ofSubsingletonLIE_apply (f : FourSpace →L[ℝ] Mat4C) (v : Fin 1 → FourSpace) :
    ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace) (F := Mat4C)
      (0 : Fin 1) f v = f (v 0) :=
  rfl

private lemma local_frameBasis_apply (γ δ : Fin 4) :
    frameBasis γ δ = if δ = γ then 1 else 0 := by
  rw [frameBasis, EuclideanSpace.basisFun_apply]
  simp [EuclideanSpace.single, eq_comm]

private lemma local_ymCurvature_zero : ymCurvature (0 : Mat4CForm 1) = 0 := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, ymCurvature_apply_two (0 : Mat4CForm 1) (differentiable_const _) x (v 0) (v 1)]
  simp

private lemma local_covExtDeriv_zero (A : Mat4CForm 1) (k : ℕ) :
    covExtDeriv A (0 : Mat4CForm k) = 0 := by
  have hneg : covExtDeriv A (-(0 : Mat4CForm k)) = -covExtDeriv A (0 : Mat4CForm k) :=
    covExtDeriv_neg A 0
  rw [neg_zero] at hneg
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  ext i j
  let z : ℂ := covExtDeriv A (0 : Mat4CForm k) x v i j
  have hij : z = -z :=
    congrFun (congrFun (congrArg (fun f : Mat4CForm (k + 1) => f x v) hneg) i) j
  have h2 : (2 : ℂ) * z = 0 := by
    rw [two_mul]
    nth_rw 2 [hij]
    exact add_neg_cancel z
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

private lemma local_isSelfDualForm4_zero : IsSelfDualForm4 (0 : Mat4CForm 1) := by
  rw [IsSelfDualForm4, local_ymCurvature_zero]
  funext x
  exact map_zero hodgeStar4EuclMap

/-- T1-F9-01: `ymCurvature` vanishes on the zero 1-form as a `Mat4CForm 2`. -/
theorem t1_f9_01_ym_curvature_form_typing (x : FourSpace) :
    (ymCurvature (0 : Mat4CForm 1) : Mat4CForm 2) x = 0 := by
  rw [local_ymCurvature_zero]
  rfl

/-- T1-F9-02: `covExtDeriv` maps the zero 2-form under `A = 0` to `0` as a `Mat4CForm 3`. -/
theorem t1_f9_02_cov_ext_deriv_typing (x : FourSpace) :
    (covExtDeriv (0 : Mat4CForm 1) (0 : Mat4CForm 2) : Mat4CForm 3) x = 0 := by
  rw [local_covExtDeriv_zero]
  rfl

/-- T1-F9-03: Differential Bianchi identity `D_A F_A = 0` for any `C²` 1-form `A`. -/
theorem t1_f9_03_bianchi_identity_smooth_form (A : Mat4CForm 1) (hA : ContDiff ℝ 2 A) :
    covExtDeriv A (ymCurvature A) = 0 :=
  bianchi_identity_ymCurvature hA

/-- T1-F9-04: Curvature evaluation on constant non-Abelian circular 1-form basis vectors. -/
theorem t1_f9_04_ym_curvature_basis_eval (M0 M1 : Mat4C) :
    let A : Mat4CForm 1 := fun _ =>
      ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
        (F := Mat4C) (0 : Fin 1)
        (LinearMap.toContinuousLinearMap
          { toFun := fun v => (v 0 : ℂ) • M0 + (v 1 : ℂ) • M1
            map_add' := fun u v => by
              simp only [PiLp.add_apply, Complex.ofReal_add, add_smul]
              abel
            map_smul' := fun c v => by
              simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
                smul_add, ← smul_assoc, Complex.real_smul] })
    ymCurvature A 0 ![frameBasis 0, frameBasis 1] = M0 * M1 - M1 * M0 := by
  intro A
  rw [ymCurvature_apply_two A (differentiable_const _) 0 (frameBasis 0) (frameBasis 1)]
  have hc0 : fderiv ℝ (fun y => A y (fun _ => frameBasis 1)) 0 = 0 := by
    change fderiv ℝ (fun _ => A 0 (fun _ => frameBasis 1)) 0 = 0
    simp
  have hc1 : fderiv ℝ (fun y => A y (fun _ => frameBasis 0)) 0 = 0 := by
    change fderiv ℝ (fun _ => A 0 (fun _ => frameBasis 0)) 0 = 0
    simp
  have ha0 : A 0 (fun _ => frameBasis 0) = M0 := by
    change ((frameBasis 0 0 : ℝ) : ℂ) • M0 + ((frameBasis 0 1 : ℝ) : ℂ) • M1 = M0
    simp [local_frameBasis_apply]
  have ha1 : A 0 (fun _ => frameBasis 1) = M1 := by
    change ((frameBasis 1 0 : ℝ) : ℂ) • M0 + ((frameBasis 1 1 : ℝ) : ℂ) • M1 = M1
    simp [local_frameBasis_apply]
  rw [hc0, hc1, ha0, ha1]
  simp

/-- T1-F9-05: Additivity of `covExtDeriv A` on matrix-valued differential forms. -/
theorem t1_f9_05_cov_ext_deriv_add_linear (A : Mat4CForm 1) (k : ℕ)
    (ω₁ ω₂ : Mat4CForm k) (h1 : Differentiable ℝ ω₁) (h2 : Differentiable ℝ ω₂) :
    covExtDeriv A (ω₁ + ω₂) = covExtDeriv A ω₁ + covExtDeriv A ω₂ := by
  funext x
  let ed : Mat4CForm k → Mat4CForm (k + 1) :=
    @extDeriv ℝ FourSpace (Matrix (Fin 4) (Fin 4) ℂ) _ _ _
      Matrix.normedAddCommGroup Matrix.normedSpace k
  have hL : ed (ω₁ + ω₂) x = ed ω₁ x + ed ω₂ x :=
    @extDeriv_add ℝ FourSpace (Matrix (Fin 4) (Fin 4) ℂ) _ _ _
      Matrix.normedAddCommGroup Matrix.normedSpace k ω₁ ω₂ x (h1 x) (h2 x)
  have h0 : covExtDeriv A (ω₁ + ω₂) x = ed (ω₁ + ω₂) x + wedgeComm A (ω₁ + ω₂) x := rfl
  have h1' : covExtDeriv A ω₁ x = ed ω₁ x + wedgeComm A ω₁ x := rfl
  have h2' : covExtDeriv A ω₂ x = ed ω₂ x + wedgeComm A ω₂ x := rfl
  change covExtDeriv A (ω₁ + ω₂) x = covExtDeriv A ω₁ x + covExtDeriv A ω₂ x
  rw [h0, h1', h2', hL]
  dsimp [wedgeComm]
  rw [map_add]
  abel

/-! ### F10: R3 Explicit 4D Hodge Star, Yang–Mills PDE & Circular Solution -/

/-- T1-F10-01: Euclidean 4D Hodge star is an involution (`⋆² = +id`). -/
theorem t1_f10_01_hodge_star_eucl_involutive
    (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap (hodgeStar4EuclMap η) = η :=
  hodgeStar4EuclMap_involutive η

/-- T1-F10-02: Minkowski 4D Hodge star squares to `-id` (`⋆² = -id`). -/
theorem t1_f10_02_hodge_star_minkowski_sq_neg
    (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4MinkowskiMap (hodgeStar4MinkowskiMap η) = -η :=
  hodgeStar4MinkowskiMap_sq_neg η

/-- T1-F10-03: Self-dual `C²` 1-forms solve the Yang–Mills PDE (`D_A (⋆ F_A) = 0`). -/
theorem t1_f10_03_self_dual_solves_ym_pde (A : Mat4CForm 1)
    (hA : ContDiff ℝ 2 A) (hSD : IsSelfDualForm4 A) :
    YangMillsPDE A :=
  selfDual_solves_yangMillsPDE hA hSD

/-- T1-F10-04: `circularGaugeForm` is `C²` smooth on `FourSpace`. -/
theorem t1_f10_04_circular_gauge_form_smooth :
    ContDiff ℝ 2 circularGaugeForm :=
  circularGaugeForm_contDiff.of_le le_top

/-- T1-F10-05: `circularGaugeForm` is a non-Abelian Yang–Mills PDE solution (`F_A ≠ 0`). -/
theorem t1_f10_05_circular_gauge_form_nonabelian_ym :
    ymCurvature circularGaugeForm ≠ 0 ∧ YangMillsPDE circularGaugeForm :=
  ⟨circularGaugeForm_ymCurvature_ne_zero, circularGaugeForm_solves_yangMillsPDE⟩

/-! ## Tier 2: Boundary / Corner Cases (BVA, F1–F10, 50 Cases) -/

/-! ### F1 BVA: `x = 0`, `d = 0`, `d ≠ 0` yet `d² = 0` no-go, sheet projections, sign flip -/

/-- T2-F1-01: Zero 1-forms `ω = 0` satisfy compatibility trivially for any `d`. -/
theorem t2_f1_01_zero_connection_compat (d : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (0 : Fin 8 → ExteriorAlgebra ℂ (Fin 4 → ℂ))
    matrixExteriorDerivative d A = peirceGradingDeriv P A := by
  intro P A
  have hA : A = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, circularGaugeConnection4, chiralOffBlock4, weylUpperExt, weylLowerExt]
  rw [hA]
  ext i j
  simp [matrixExteriorDerivative, peirceGradingDeriv, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]

/-- T2-F1-02: Trivial `d = 0` triggers square-zero no-go, forcing `A = 0`. -/
theorem t2_f1_02_zero_diff_forces_zero_conn
    (ω : Fin 8 → ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (hCompat : matrixExteriorDerivative (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
      (circularGaugeConnection4 ω) =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) (circularGaugeConnection4 ω)) :
    circularGaugeConnection4 ω = 0 :=
  circularGaugeConnection4_sq_zero_eigencondition_forces_zero 0 ω (LinearMap.zero_comp _) hCompat

/-- T2-F1-03: Nonzero `contractionOp` with `d² = 0` STILL forces `A = 0` under compatibility. -/
theorem t2_f1_03_nonzero_contraction_sq_zero_forces_zero
    (ω : Fin 8 → ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (lam : (Fin 4 → ℂ) →ₗ[ℂ] ℂ)
    (hCompat : matrixExteriorDerivative (contractionOp lam) (circularGaugeConnection4 ω) =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) (circularGaugeConnection4 ω)) :
    circularGaugeConnection4 ω = 0 := by
  have hSq : (contractionOp lam).comp (contractionOp lam) = 0 :=
    LinearMap.ext (contraction_op_sq_zero lam)
  exact circularGaugeConnection4_sq_zero_eigencondition_forces_zero (contractionOp lam) ω hSq hCompat

/-- T2-F1-04: Pure upper sheet (`L = 0`) has `+1` eigenvalue, pure lower (`U = 0`) has `-1`. -/
theorem t2_f1_04_upper_vs_lower_sheet_eigenvalue
    (U L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ))) :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    peirceGradingDeriv P (chiralOffBlock4 U 0) = chiralOffBlock4 U 0 ∧
      peirceGradingDeriv P (chiralOffBlock4 0 L) = -(chiralOffBlock4 0 L) := by
  refine ⟨?_, ?_⟩
  · simpa using chiralExteriorProj4_peirceGradingDeriv_offBlock U (0 : Matrix (Fin 2) (Fin 2) _)
  · rw [chiralExteriorProj4_peirceGradingDeriv_offBlock (0 : Matrix (Fin 2) (Fin 2) _) L]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

/-- T2-F1-05: Negation boundary respects `peirceGradingDeriv P (-A) = -peirceGradingDeriv P A`. -/
theorem t2_f1_05_peirce_grading_negation
    (U L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ))) :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    peirceGradingDeriv P (-(chiralOffBlock4 U L)) =
      -(peirceGradingDeriv P (chiralOffBlock4 U L)) := by
  simp [peirceGradingDeriv, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  abel

/-! ### F2 BVA: `x = 0`, `uPlus` (`L = 0`), `uMinus` (`U = 0`), `d² ≠ 0`, mixed non-degeneracy -/

/-- T2-F2-01: Zero coord `x = 0` yields `A = 0` & zero curvature under `circularGradedDiff`. -/
theorem t2_f2_01_graded_zero_coord_boundary :
    let A := circularGaugeConnection4 (circularGradedOmega (0 : Coordinate))
    A = 0 ∧ curvatureFromConnection circularGradedDiff A = 0 := by
  have hω : ∀ i : Fin 8, circularGradedOmega (0 : Coordinate) i = 0 := by
    intro i
    fin_cases i <;> simp [circularGradedOmega]
  have hA : circularGaugeConnection4 (circularGradedOmega (0 : Coordinate)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, weylLowerExt, hω]
  refine ⟨hA, ?_⟩
  rw [hA]
  ext i j
  simp [curvatureFromConnection, matrixExteriorDerivative]

/-- T2-F2-02: Pure upper-sheet `uPlus` yields `A ≠ 0` while `genV P A A = 0`. -/
theorem t2_f2_02_graded_pure_uplus_vanishing_gen_v :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularGradedOmega (coordinateEquiv uPlus))
    A ≠ 0 ∧ genV P A A = 0 := by
  have hc : coordinateEquiv uPlus = Pi.single 0 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 0
  have hω : ∀ i : Fin 8, circularGradedOmega (coordinateEquiv uPlus) i =
      if i = 0 then uPlusForm else 0 := by
    intro i
    fin_cases i <;> simp [circularGradedOmega, hc]
  have hL : weylLowerExt (circularGradedOmega (coordinateEquiv uPlus) 4)
      (circularGradedOmega (coordinateEquiv uPlus) 5)
      (circularGradedOmega (coordinateEquiv uPlus) 6)
      (circularGradedOmega (coordinateEquiv uPlus) 7) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylLowerExt, hω]
  have hA_ne : circularGaugeConnection4 (circularGradedOmega (coordinateEquiv uPlus)) ≠ 0 := by
    intro hz
    have h02 := congrFun (congrFun hz 0) 2
    have h02' : uPlusForm = 0 := by
      simpa [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 0, hω 3] using h02
    have hc01 := congrArg
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1) h02'
    have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      0 1 0 1 0).1
    have hev1 := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      0 1 1 0 0).2.1
    rw [map_zero] at hc01
    change InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1 +
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) = 0
      at hc01
    rw [map_add, hev, hev1] at hc01
    norm_num at hc01
  refine ⟨hA_ne, ?_⟩
  unfold circularGaugeConnection4 chiralExteriorProj4
  rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4, hL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

/-- T2-F2-03: Pure lower-sheet `uMinus` yields `d A = -A` under `circularGradedDiff`. -/
theorem t2_f2_03_graded_pure_uminus_neg_eigenspace :
    let A := circularGaugeConnection4 (circularGradedOmega (coordinateEquiv uMinus))
    A ≠ 0 ∧ matrixExteriorDerivative circularGradedDiff A = -A := by
  have hc : coordinateEquiv uMinus = Pi.single 4 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 4
  have hω : ∀ i : Fin 8, circularGradedOmega (coordinateEquiv uMinus) i =
      if i = 4 then uMinusForm else 0 := by
    intro i
    fin_cases i <;> simp [circularGradedOmega, hc]
  have hU : weylUpperExt (circularGradedOmega (coordinateEquiv uMinus) 0)
      (circularGradedOmega (coordinateEquiv uMinus) 1)
      (circularGradedOmega (coordinateEquiv uMinus) 2)
      (circularGradedOmega (coordinateEquiv uMinus) 3) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylUpperExt, hω]
  have hA_ne : circularGaugeConnection4 (circularGradedOmega (coordinateEquiv uMinus)) ≠ 0 := by
    intro hz
    have h20 := congrFun (congrFun hz 2) 0
    have h20' : uMinusForm = 0 := by
      simpa [circularGaugeConnection4, chiralOffBlock4, weylLowerExt, hω 4, hω 7] using h20
    have hc23 := congrArg
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 2 3) h20'
    have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      2 3 2 3 0).1
    have hev3 := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      2 3 3 0 0).2.1
    rw [map_zero] at hc23
    change InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 2 3
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 2 *
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 3 -
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 3) = 0
      at hc23
    rw [map_sub, hev, hev3] at hc23
    norm_num at hc23
  refine ⟨hA_ne, ?_⟩
  rw [circularGradedDiff_eigencondition]
  unfold circularGaugeConnection4
  rw [chiralExteriorProj4_peirceGradingDeriv_offBlock, hU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

/-- T2-F2-04: `circularGradedDiff` is NOT square-zero (`d² ≠ 0`), escaping F1 no-go. -/
theorem t2_f2_04_graded_diff_not_square_zero :
    circularGradedDiff.comp circularGradedDiff ≠ 0 := by
  intro h
  have hup := circularGradedDiff_uPlusForm
  have h2 : circularGradedDiff (circularGradedDiff uPlusForm) = 0 := by
    have hz := congrArg (fun f : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) => f uPlusForm) h
    simpa [LinearMap.comp_apply, LinearMap.zero_apply] using hz
  rw [hup, hup] at h2
  have hc := congrArg
    (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1) h2
  have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
    0 1 0 1 0).1
  have hev1 := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
    0 1 1 0 0).2.1
  rw [map_zero] at hc
  change InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
    (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
      InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1 +
      InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) = 0 at hc
  rw [map_add, hev, hev1] at hc
  norm_num at hc

/-- T2-F2-05: Nondegenerate mixed witness has nonzero `A`, `genV`, and curvature. -/
theorem t2_f2_05_graded_diff_nondegenerate_components :
    ∃ x : Coordinate,
      let P := chiralExteriorProj4 (Fin 4 → ℂ)
      let A := circularGaugeConnection4 (circularGradedOmega x)
      A ≠ 0 ∧ genV P A A ≠ 0 ∧ curvatureFromConnection circularGradedDiff A ≠ 0 := by
  rcases circularGradedDiff_nondegenerate_witness with ⟨x, hA, hCurv, _, _, hV⟩
  exact ⟨x, hA, hV, hCurv⟩

/-! ### F3 BVA: `x = 0`, degree-1 homogeneity, `uPlus`, mixed `genV ≠ 0`, involution `d² = id` -/

/-- T2-F3-01: At `x = 0`, `circularEvenOmega 0` gives zero `A` and zero `covariantDerivative`. -/
theorem t2_f3_01_even_zero_coord_boundary :
    let A := circularGaugeConnection4 (circularEvenOmega (0 : Coordinate))
    A = 0 ∧ covariantDerivative A circularEvenDiff 0 = 0 := by
  have hω : ∀ i : Fin 8, circularEvenOmega (0 : Coordinate) i = 0 := by
    intro i
    fin_cases i <;> simp [circularEvenOmega]
  have hA : circularGaugeConnection4 (circularEvenOmega (0 : Coordinate)) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, weylLowerExt, hω]
  refine ⟨hA, ?_⟩
  ext i j
  simp [covariantDerivative, matrixExteriorDerivative, matrixCommutator]

/-- T2-F3-02: Mixed coordinate `uPlus + uMinus` preserves `MatrixIsHomogeneous 1`. -/
theorem t2_f3_02_even_mixed_homogeneous_one :
    MatrixIsHomogeneous 1
      (circularGaugeConnection4 (circularEvenOmega (coordinateEquiv (uPlus + uMinus)))) :=
  circularEvenOmega_homogeneous (coordinateEquiv (uPlus + uMinus))

/-- T2-F3-03: Pure upper-sheet `uPlus` has `genV P A A = 0` and covariant vanishing. -/
theorem t2_f3_03_even_uplus_gen_v_zero :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularEvenOmega (coordinateEquiv uPlus))
    genV P A A = 0 ∧ covariantDerivative A circularEvenDiff (genV P A A) = 0 := by
  have hc : coordinateEquiv uPlus = Pi.single 0 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 0
  have hω : ∀ i : Fin 8, circularEvenOmega (coordinateEquiv uPlus) i =
      if i = 0 then ExteriorAlgebra.ι ℂ (Pi.single 0 1) else 0 := by
    intro i
    fin_cases i <;> simp [circularEvenOmega, hc]
  have hL : weylLowerExt (circularEvenOmega (coordinateEquiv uPlus) 4)
      (circularEvenOmega (coordinateEquiv uPlus) 5)
      (circularEvenOmega (coordinateEquiv uPlus) 6)
      (circularEvenOmega (coordinateEquiv uPlus) 7) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [weylLowerExt, hω]
  refine ⟨?_, circularEvenDiff_covariant_vanishing _⟩
  unfold circularGaugeConnection4 chiralExteriorProj4
  rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4, hL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chiralOffBlock4]

/-- T2-F3-04: Mixed witness has `genV P A A ≠ 0` yet `D_A (genV P A A) = 0`. -/
theorem t2_f3_04_even_mixed_nonzero_gen_v_covariant_vanishing :
    ∃ x : Coordinate,
      let P := chiralExteriorProj4 (Fin 4 → ℂ)
      let A := circularGaugeConnection4 (circularEvenOmega x)
      genV P A A ≠ 0 ∧ covariantDerivative A circularEvenDiff (genV P A A) = 0 := by
  rcases circularEvenDiff_nondegenerate_witness with ⟨x, _, hV, _, _⟩
  exact ⟨x, hV, circularEvenDiff_covariant_vanishing x⟩

/-- T2-F3-05: `circularEvenDiff` squares to `+id` on degree-1 generators (`d² ≠ 0`). -/
theorem t2_f3_05_even_diff_involution_on_generators (v : Fin 4 → ℂ) :
    circularEvenDiff (circularEvenDiff (ExteriorAlgebra.ι ℂ v)) = ExteriorAlgebra.ι ℂ v := by
  unfold circularEvenDiff
  rw [InfoGeometry.CliffordExteriorLift.exteriorLift_ι,
    InfoGeometry.CliffordExteriorLift.exteriorLift_ι]
  congr 1
  ext i
  fin_cases i <;> simp [circularEvenMap]

/-! ### F4 BVA: `a = 0`, `x = 0`, `a < 0`, commuting vs non-Abelian, nontrivial `U ≠ 1` -/

/-- T2-F4-01: At degenerate lattice spacing `a = 0`, `circularLinkTransport` equals `1`. -/
theorem t2_f4_01_link_transport_at_zero_spacing
    (x : FourSpace → Fin 4 → Coordinate) (y : FourSpace) (μ : Fin 4) :
    circularLinkTransport x y μ 0 = 1 := by
  simp [circularLinkTransport]

/-- T2-F4-02: Zero gauge field `x = 0` gives trivial link transporter `1` for all `a`. -/
theorem t2_f4_02_link_transport_zero_field (y : FourSpace) (μ : Fin 4) (a : ℝ) :
    circularLinkTransport (fun _ _ => 0) y μ a = 1 := by
  have h0 : circularConnectionMat4 (0 : Coordinate) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [circularConnectionMat4, chiralOffBlock4, weylUpperMat, weylLowerMat,
        pauliSolder2x2, solder]
  simp [circularLinkTransport, h0]

/-- T2-F4-03: Negative spacing `a = -0.5` is the exact matrix inverse of `a = 0.5`. -/
theorem t2_f4_03_link_transport_negative_spacing
    (x : FourSpace → Fin 4 → Coordinate) (y : FourSpace) (μ : Fin 4) :
    circularLinkTransport x y μ (-0.5 : ℝ) * circularLinkTransport x y μ (0.5 : ℝ) = 1 := by
  simp only [circularLinkTransport]
  rw [← Matrix.exp_add_of_commute _ _
    (((Commute.refl (circularConnectionMat4 (x y μ))).smul_left (-0.5 : ℝ)).smul_right
      (0.5 : ℝ)), ← add_smul]
  norm_num

/-- T2-F4-04: Non-Abelian `rootPlus 0`, `rootMinus 1` blocks fail to commute in `Mat4C`. -/
theorem t2_f4_04_nonabelian_blocks_noncommute :
    let x := coordinateEquiv (rootPlus 0 + rootMinus 1)
    weylUpperMat x * weylLowerMat x ≠ weylLowerMat x * weylUpperMat x :=
  weylChannel_noncomm_sheet_blocks_witness

/-- T2-F4-05: Nonzero circular connection `circularConnectionMat4 (coordinateEquiv uPlus) ≠ 0`. -/
theorem t2_f4_05_circular_connection_nonzero :
    circularConnectionMat4 (coordinateEquiv uPlus) ≠ 0 := by
  intro h
  have h02 := congrFun (congrFun h 0) 2
  have hc : coordinateEquiv uPlus = Pi.single 0 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 0
  simp [circularConnectionMat4, chiralOffBlock4, weylUpperMat, pauliSolder2x2,
    solder, σ0, σ1, σ2, σ3, hc] at h02

/-! ### F5 BVA: `a = 0` vs `𝓝[≠] 0`, `A = 0`, Abelian `[A, Φ] = 0`, non-Abelian, two-sided `0±` -/

/-- T2-F5-01: At `a = 0`, `latticeCovariantDiff` collapses to `0` (`𝓝[≠] 0` is essential). -/
theorem t2_f5_01_lattice_cov_diff_degenerate_zero
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C) (y : FourSpace) (μ : Fin 4) :
    latticeCovariantDiff A Φ y μ 0 = 0 :=
  latticeCovariantDiff_at_zero A Φ y μ

/-- T2-F5-02: Zero field `A = 0` and constant `Φ` yield `0` at every `a` and `0` in limit. -/
theorem t2_f5_02_lattice_cov_diff_zero_const (M0 : Mat4C) (y : FourSpace) (μ : Fin 4) :
    continuumCovariantDeriv 0 (fun _ => M0) y μ = 0 ∧
      Filter.Tendsto (fun a : ℝ => latticeCovariantDiff 0 (fun _ => M0) y μ a)
        (𝓝[≠] 0) (nhds 0) :=
  ⟨continuumCovariantDeriv_zero_const M0 y μ,
    by simpa [continuumCovariantDeriv_zero_const] using
      tendsto_latticeCovariantDiff 0 (fun _ => M0) y μ (differentiableAt_const M0)⟩

/-- T2-F5-03: Abelian scalar-multiple `A, Φ` annihilate commutator `[A, Φ] = 0`. -/
theorem t2_f5_03_lattice_cov_diff_abelian_commutes (c d : ℂ) (y : FourSpace) (μ : Fin 4) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ _ => c • (1 : Mat4C)
    let Φ : FourSpace → Mat4C := fun _ => d • (1 : Mat4C)
    continuumCovariantDeriv A Φ y μ = 0 :=
  continuumCovariantDeriv_abelian_const c d y μ

/-- T2-F5-04: Non-Abelian `A` with constant `Φ` yields strictly nonzero `[A, Φ]` limit. -/
theorem t2_f5_04_lattice_cov_diff_nonabelian_nonzero (y : FourSpace) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ _ =>
      circularConnectionMat4 (coordinateEquiv uPlus)
    let Φ : FourSpace → Mat4C := fun _ => chiralProjMat4
    continuumCovariantDeriv A Φ y 0 ≠ 0 :=
  continuumCovariantDeriv_nonabelian_const_nonzero y

/-- T2-F5-05: Both one-sided limits `a → 0⁺` and `a → 0⁻` agree with `continuumCovariantDeriv`. -/
theorem t2_f5_05_lattice_cov_diff_two_sided
    (A : FourSpace → Fin 4 → Mat4C) (Φ : FourSpace → Mat4C)
    (y : FourSpace) (μ : Fin 4) (hΦ : DifferentiableAt ℝ Φ y) :
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y μ a) (𝓝[>] 0)
        (nhds (continuumCovariantDeriv A Φ y μ)) ∧
      Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y μ a) (𝓝[<] 0)
        (nhds (continuumCovariantDeriv A Φ y μ)) :=
  ⟨(tendsto_latticeCovariantDiff A Φ y μ hΦ).mono_left (nhdsGT_le_nhdsNE 0),
    (tendsto_latticeCovariantDiff A Φ y μ hΦ).mono_left (nhdsLT_le_nhdsNE 0)⟩

/-! ### F6 BVA: `a = 0` plaquette, `μ = ν`, constant Abelian, antisymmetry, `> 0` witness -/

/-- T2-F6-01: At `a = 0`, `wilsonPlaquette = 1` and `wilsonPlaquetteAction = 0`. -/
theorem t2_f6_01_wilson_plaquette_at_zero_spacing
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) :
    wilsonPlaquette A y μ ν 0 = 1 ∧ wilsonPlaquetteAction A y μ ν 0 = 0 :=
  wilsonPlaquette_at_zero A y μ ν

/-- T2-F6-02: Degenerate plane `μ = ν` gives trivial plaquette `1` and zero curvature/action. -/
theorem t2_f6_02_wilson_plaquette_same_direction
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ : Fin 4) (a : ℝ) :
    wilsonPlaquette A y μ μ a = 1 ∧ continuumCurvature A y μ μ = 0 :=
  wilsonPlaquette_diag_trivial A y μ a

/-- T2-F6-03: Constant Abelian gauge field gives zero continuum curvature and action. -/
theorem t2_f6_03_wilson_plaquette_constant_abelian
    (c : Fin 4 → ℂ) (y : FourSpace) (μ ν : Fin 4) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ ρ => c ρ • (1 : Mat4C)
    continuumCurvature A y μ ν = 0 ∧ continuumPlaquetteAction A y μ ν = 0 := by
  intro A
  have hF : continuumCurvature A y μ ν = 0 := continuumCurvature_abelian_const_zero c y μ ν
  refine ⟨hF, ?_⟩
  simp [continuumPlaquetteAction, hF]

/-- T2-F6-04: Continuum curvature is antisymmetric under `(μ, ν) ↔ (ν, μ)`. -/
theorem t2_f6_04_continuum_curvature_antisymm
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) :
    continuumCurvature A y ν μ = -continuumCurvature A y μ ν :=
  continuumCurvature_antisymm A y μ ν

/-- T2-F6-05: Strict non-degeneracy (`continuumCurvature ≠ 0`, `continuumPlaquetteAction > 0`). -/
theorem t2_f6_05_continuum_nonabelian_strict_positivity :
    ∃ (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4),
      continuumCurvature A y μ ν ≠ 0 ∧ 0 < continuumPlaquetteAction A y μ ν :=
  let ⟨A, y, μ, ν, _, hCurv, hAct⟩ := circularLattice_nonabelian_continuum_smooth_witness
  ⟨A, y, μ, ν, hCurv, hAct⟩

/-! ### F7 BVA: zero field, `a = 0` vs `𝓝[≠] 0`, non-Abelian cone, multi-step `k = 0..5`, star -/

/-- T2-F7-01: Zero gauge field converges to `0` in `B_inf` under colimit cone. -/
theorem t2_f7_01_colimit_zero_field
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf] [TopologicalSpace B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (hCont : Continuous (fun M : Mat4C => (cone.toColimit k).toRingHom (ι.toRingHom M)))
    (y : FourSpace) (μ ν : Fin 4) :
    Filter.Tendsto
      (fun a : ℝ => (cone.toColimit k).toRingHom
        (ι.toRingHom ((a ^ 2)⁻¹ • (wilsonPlaquette 0 y μ ν a - 1))))
      (𝓝[≠] 0) (nhds (0 : B_inf)) := by
  have h := (circularColimit_continuum_transport cone k ι hCont (fun _ _ => 0) 0 (fun _ => 0)
    y μ ν contDiff_const (differentiableAt_const _)).2.1
  simpa [continuumCurvature_zero] using h

/-- T2-F7-02: At `a = 0`, plaquette image under `cone.toColimit` is `1` while `𝓝[≠] 0` converges. -/
theorem t2_f7_02_colimit_a_zero_vs_punctured
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4) :
    (cone.toColimit k).toRingHom (ι.toRingHom (wilsonPlaquette A y μ ν 0)) = 1 := by
  rw [(wilsonPlaquette_at_zero A y μ ν).1, map_one, map_one]

/-- T2-F7-03: Non-Abelian commutator curvature satisfies step-homomorphism cocycle compatibility. -/
theorem t2_f7_03_colimit_nonabelian_step_compat
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (M : Mat4C) :
    (cone.toColimit (k + 1)).toRingHom ((cone.stepHom k).toRingHom (ι.toRingHom M)) =
      (cone.toColimit k).toRingHom (ι.toRingHom M) :=
  cone.compat k (ι.toRingHom M)

/-- T2-F7-04: Iterated transition from stage `0` to stage `5` matches stage `0` limit. -/
theorem t2_f7_04_colimit_stage_zero_to_five
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower 0))
    (M : Mat4C) :
    (cone.toColimit (0 + 5)).toRingHom
        ((CanonicalTwoSheetedInductiveColimit.stepHomIter cone 0 5).toRingHom (ι.toRingHom M)) =
      (cone.toColimit 0).toRingHom (ι.toRingHom M) := by
  have h1 := cone.compat 0 (ι.toRingHom M)
  have h2 := cone.compat 1 ((cone.stepHom 0).toRingHom (ι.toRingHom M))
  have h3 := cone.compat 2 ((cone.stepHom 1).toRingHom
    ((cone.stepHom 0).toRingHom (ι.toRingHom M)))
  have h4 := cone.compat 3 ((cone.stepHom 2).toRingHom
    ((cone.stepHom 1).toRingHom ((cone.stepHom 0).toRingHom (ι.toRingHom M))))
  have h5 := cone.compat 4 ((cone.stepHom 3).toRingHom
    ((cone.stepHom 2).toRingHom ((cone.stepHom 1).toRingHom
      ((cone.stepHom 0).toRingHom (ι.toRingHom M)))))
  simp only [CanonicalTwoSheetedInductiveColimit.stepHomIter,
    CanonicalTwoSheetedInductiveColimit.StarRingHom.comp,
    CanonicalTwoSheetedInductiveColimit.StarRingHom.id]
  exact h5.trans (h4.trans (h3.trans (h2.trans h1)))

/-- T2-F7-05: Star involution commutes with colimit cone morphisms at the continuum limit. -/
theorem t2_f7_05_colimit_star_commutes
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (F : Mat4C) :
    (cone.toColimit k).toRingHom (ι.toRingHom (star F)) =
      star ((cone.toColimit k).toRingHom (ι.toRingHom F)) := by
  rw [ι.map_star', (cone.toColimit k).map_star']

/-! ### F8 BVA: zero connection, projector nontriviality, Krein null vectors, base shift, bundle -/

/-- T2-F8-01: Adding the zero `Mat4C` 1-form via `circularBundleConnection` gives `fderiv`. -/
theorem t2_f8_01_circular_bundle_connection_zero
    (σ : FourSpace → ChiralFiber) (x v : FourSpace) :
    circularBundleConnection (0 : Mat4CForm 1) σ x v = fderiv ℝ σ x v := by
  rw [circularBundleConnection_apply]
  simp

/-- T2-F8-02: `chiralProjCLM` projected by `chiralFiberToKreinFrame` is isotropic under Krein. -/
theorem t2_f8_02_bundle_projector_nontrivial (u v : ChiralFiber) :
    fiberKreinPairing (chiralProjCLM u) (chiralProjCLM v) = 0 :=
  fiberKreinPairing_chiralProj_isotropic u v

/-- T2-F8-03: Krein bundle pairing vanishes on nonzero lightlike vectors (indefinite signature). -/
theorem t2_f8_03_krein_null_lightcone_indefinite :
    let x := coordinateEquiv (uPlus + uMinus + rootPlus 0 + rootMinus 0)
    x ≠ 0 ∧ fiberKreinPairing (chiralFiberToKreinFrame.symm (circularCoordToKreinFrame x))
      (chiralFiberToKreinFrame.symm (circularCoordToKreinFrame x)) = 0 := by
  have hc0 : coordinateEquiv uPlus = Pi.single 0 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 0
  have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 1
  have hc4 : coordinateEquiv uMinus = Pi.single 4 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 4
  have hc5 : coordinateEquiv (rootMinus 0) = Pi.single 5 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 5
  have hx : coordinateEquiv (uPlus + uMinus + rootPlus 0 + rootMinus 0) =
      Pi.single 0 1 + Pi.single 4 1 + Pi.single 1 1 + Pi.single 5 1 := by
    rw [LinearEquiv.map_add, LinearEquiv.map_add, LinearEquiv.map_add, hc0, hc4, hc1, hc5]
  constructor
  · intro h
    have h0 : ((Pi.single 0 1 + Pi.single 4 1 + Pi.single 1 1 + Pi.single 5 1 : Coordinate) 0) =
        0 := by
      rw [← hx]
      exact congrFun h 0
    simp at h0
  · simp only [fiberKreinPairing, LinearEquiv.apply_symm_apply,
      chiralKreinForm_diag_eq_two_wittNorm]
    rw [hx]
    simp [wittNorm]

/-- T2-F8-04: `chiralBundleProjector` is idempotent and invariant under basepoint shift. -/
theorem t2_f8_04_bundle_projector_basepoint_invariant (m₀ m₁ : FourSpace) :
    (chiralBundleProjector FourSpace m₀).comp (chiralBundleProjector FourSpace m₁) =
      chiralBundleProjector FourSpace m₀ :=
  chiralBundleProjector_idempotent FourSpace m₀

/-- T2-F8-05: Arbitrary smooth 4-manifold `(M, E)` chiral bundle projector & gauge connection. -/
theorem t2_f8_05_abstract_manifold_bundle_compat
    {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold (𝓡 4) ⊤ M]
    {E : M → Type*} [TopologicalSpace (TotalSpace ChiralFiber E)]
    [∀ m, AddCommGroup (E m)] [∀ m, Module ℝ (E m)]
    [∀ m, TopologicalSpace (E m)]
    [∀ m, IsTopologicalAddGroup (E m)] [∀ m, ContinuousSMul ℝ (E m)]
    [FiberBundle ChiralFiber E] [VectorBundle ℝ ChiralFiber E]
    [ContMDiffVectorBundle ⊤ ChiralFiber E (𝓡 4)]
    (e : Trivialization ChiralFiber (π ChiralFiber E)) [MemTrivializationAtlas e]
    (cov : CovariantDerivative (𝓡 4) ChiralFiber E)
    (A : ∀ x : M, E x →L[ℝ] TangentSpace (𝓡 4) x →L[ℝ] E x)
    (σ : ∀ x : M, E x) {x : M} (hx : x ∈ e.baseSet) :
    (chiralLocalBundleProjector e x).comp (chiralLocalBundleProjector e x) =
        chiralLocalBundleProjector e x ∧
      gaugeConnection cov A σ x = cov σ x + A x (σ x) :=
  ⟨chiralLocalBundleProjector_idempotent e hx, gaugeConnection_apply cov A σ x⟩

/-! ### F9 BVA: `A = 0`, constant Abelian, constant non-Abelian, exact `df`, varying `C²` -/

/-- T2-F9-01: Zero 1-form `A = 0` has `ymCurvature 0 = 0` and `covExtDeriv 0 0 = 0`. -/
theorem t2_f9_01_zero_one_form_curvature :
    ymCurvature (0 : Mat4CForm 1) = 0 ∧ covExtDeriv (0 : Mat4CForm 1) (0 : Mat4CForm 2) = 0 :=
  ⟨local_ymCurvature_zero, local_covExtDeriv_zero 0 2⟩

/-- T2-F9-02: Constant Abelian 1-form `A x v = (v 0 : ℂ) • 1` has `ymCurvature A = 0`. -/
theorem t2_f9_02_const_abelian_one_form_flat :
    let A : Mat4CForm 1 := fun _ =>
      ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
        (F := Mat4C) (0 : Fin 1)
        (LinearMap.toContinuousLinearMap
          { toFun := fun v => (v 0 : ℂ) • (1 : Mat4C)
            map_add' := fun u v => by
              simp only [PiLp.add_apply, Complex.ofReal_add, add_smul]
            map_smul' := fun c v => by
              simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
                ← smul_assoc, Complex.real_smul] })
    ymCurvature A = 0 := by
  intro A
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv, ymCurvature_apply_two A (differentiable_const _) x (v 0) (v 1)]
  have hc0 : fderiv ℝ (fun y => A y (fun _ => v 1)) x = 0 := by
    change fderiv ℝ (fun _ => A x (fun _ => v 1)) x = 0
    simp
  have hc1 : fderiv ℝ (fun y => A y (fun _ => v 0)) x = 0 := by
    change fderiv ℝ (fun _ => A x (fun _ => v 0)) x = 0
    simp
  have hev : ∀ u : FourSpace, A x (fun _ => u) = (u 0 : ℂ) • (1 : Mat4C) := fun u => rfl
  rw [hc0, hc1, hev (v 0), hev (v 1)]
  simp only [zero_apply, sub_self, zero_add, Algebra.mul_smul_comm, mul_one, smul_smul]
  rw [mul_comm ((v 0 0 : ℂ)) ((v 1 0 : ℂ)), sub_self]
  rfl

/-- T2-F9-03: Constant non-Abelian 1-form has `ContDiff ℝ 2 A`, `ymCurvature A ≠ 0`, `D_A F = 0`. -/
theorem t2_f9_03_const_nonabelian_curvature_bianchi :
    ∃ A : Mat4CForm 1,
      ContDiff ℝ 2 A ∧ ymCurvature A ≠ 0 ∧ covExtDeriv A (ymCurvature A) = 0 :=
  ⟨circularGaugeForm, circularGaugeForm_contDiff.of_le le_top,
    circularGaugeForm_ymCurvature_ne_zero,
    bianchi_identity_ymCurvature (circularGaugeForm_contDiff.of_le le_top)⟩

/-- T2-F9-04: Purely exact Abelian 1-form `A = df • 1` has zero curvature and satisfies Bianchi. -/
theorem t2_f9_04_exact_abelian_curvature_zero (f : FourSpace → ℝ) (hf : ContDiff ℝ 3 f) :
    let A : Mat4CForm 1 := fun y =>
      ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
        (F := Mat4C) (0 : Fin 1) ((fderiv ℝ f y).smulRight (1 : Mat4C))
    ymCurvature A = 0 ∧ covExtDeriv A (ymCurvature A) = 0 := by
  intro A
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have hL : Differentiable ℝ (fun y => (fderiv ℝ f y).smulRight (1 : Mat4C)) :=
    ((ContinuousLinearMap.smulRightL ℝ FourSpace Mat4C).flip (1 : Mat4C)).differentiable.comp hf1
  have hA : Differentiable ℝ A :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace) (F := Mat4C)
      (0 : Fin 1)).toContinuousLinearMap.differentiable.comp hL
  have hF : ymCurvature A = 0 := by
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, ymCurvature_apply_two A hA x (v 0) (v 1)]
    have heval : ∀ z (y : FourSpace), A y (fun _ => z) = (fderiv ℝ f y z) • (1 : Mat4C) := by
      intro z y
      exact local_ofSubsingletonLIE_apply _ _
    have hfderiv : ∀ z, fderiv ℝ (fun y => A y (fun _ => z)) x =
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (1 : Mat4C)).comp
          ((ContinuousLinearMap.apply ℝ ℝ z).comp (fderiv ℝ (fderiv ℝ f) x)) := by
      intro z
      have hfun : (fun y => A y (fun _ => z)) =
          fun y => (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (1 : Mat4C))
            ((ContinuousLinearMap.apply ℝ ℝ z) (fderiv ℝ f y)) := by
        funext y
        rw [heval]
        simp
      rw [hfun]
      exact ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (1 : Mat4C)).comp
        (ContinuousLinearMap.apply ℝ ℝ z)).hasFDerivAt.comp x (hf1 x).hasFDerivAt |>.fderiv
    rw [hfderiv (v 1), hfderiv (v 0)]
    have hsymm : fderiv ℝ (fderiv ℝ f) x (v 0) (v 1) = fderiv ℝ (fderiv ℝ f) x (v 1) (v 0) :=
      (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (v 0) (v 1)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, heval, hsymm, sub_self,
      zero_add, Algebra.mul_smul_comm, mul_one, smul_smul]
    rw [mul_comm (fderiv ℝ f x (v 0)) (fderiv ℝ f x (v 1)), sub_self]
    rfl
  exact ⟨hF, by rw [hF]; exact local_covExtDeriv_zero A 2⟩

/-- T2-F9-05: Constant `C²` non-Abelian `circularGaugeForm` satisfies Bianchi (`D_A F_A = 0`). -/
theorem t2_f9_05_varying_nonabelian_bianchi :
    covExtDeriv circularGaugeForm (ymCurvature circularGaugeForm) = 0 :=
  bianchi_identity_ymCurvature (circularGaugeForm_contDiff.of_le le_top)

/-! ### F10 BVA: Euclidean vs Minkowski `⋆²`, zero 2-form, ASD vs SD, trivial vs non-Abelian, `η` -/

/-- T2-F10-01: Euclidean `⋆² = +id` vs Minkowski `⋆² = -id` on the same 2-form. -/
theorem t2_f10_01_eucl_vs_minkowski_hodge_sq
    (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap (hodgeStar4EuclMap η) = η ∧
      hodgeStar4MinkowskiMap (hodgeStar4MinkowskiMap η) = -η :=
  ⟨hodgeStar4EuclMap_involutive η, hodgeStar4MinkowskiMap_sq_neg η⟩

/-- T2-F10-02: Zero 2-form is fixed by both Hodge stars and `A = 0` solves `YangMillsPDE`. -/
theorem t2_f10_02_zero_form_hodge_and_pde :
    hodgeStar4Eucl 0 = 0 ∧ hodgeStar4Minkowski 0 = 0 ∧ YangMillsPDE (0 : Mat4CForm 1) :=
  ⟨by funext x; exact map_zero hodgeStar4EuclMap,
    by funext x; exact map_zero hodgeStar4MinkowskiMap,
    selfDual_solves_yangMillsPDE contDiff_const local_isSelfDualForm4_zero⟩

/-- T2-F10-03: Symmetric and antisymmetric projections `η ± ⋆η` are `+1` / `-1` eigenspaces. -/
theorem t2_f10_03_self_dual_vs_anti_self_dual
    (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    hodgeStar4EuclMap (η + hodgeStar4EuclMap η) = η + hodgeStar4EuclMap η ∧
      hodgeStar4EuclMap (η - hodgeStar4EuclMap η) = -(η - hodgeStar4EuclMap η) := by
  refine ⟨?_, ?_⟩
  · rw [map_add, hodgeStar4EuclMap_involutive, add_comm]
  · rw [map_sub, hodgeStar4EuclMap_involutive]
    abel

/-- T2-F10-04: Zero solution has `ymCurvature = 0` whereas `circularGaugeForm` has `≠ 0`. -/
theorem t2_f10_04_abelian_vs_nonabelian_ym_pde :
    (ymCurvature (0 : Mat4CForm 1) = 0 ∧ YangMillsPDE (0 : Mat4CForm 1)) ∧
      (ymCurvature circularGaugeForm ≠ 0 ∧ YangMillsPDE circularGaugeForm) :=
  ⟨⟨local_ymCurvature_zero,
      selfDual_solves_yangMillsPDE contDiff_const local_isSelfDualForm4_zero⟩,
    ⟨circularGaugeForm_ymCurvature_ne_zero, circularGaugeForm_solves_yangMillsPDE⟩⟩

/-- T2-F10-05: Minkowski metric `minkowskiEta4` is involutive and invertible (`det = -1 ≠ 0`). -/
theorem t2_f10_05_minkowski_metric_invertible :
    minkowskiEta4 * minkowskiEta4 = 1 ∧ minkowskiEta4.det = -1 ∧ minkowskiEta4.det ≠ 0 := by
  refine ⟨minkowskiEta4_mul_self, minkowskiEta4_det, ?_⟩
  rw [minkowskiEta4_det]
  norm_num

/-! ## Tier 3: Pairwise Cross-Feature Combinations (12 Cases) -/

/-- T3-01 (R1 + Baseline): Graded diff satisfies bridge + compat + `A ≠ 0` on `uPlus + uMinus`. -/
theorem t3_01_r1_graded_plus_baseline_bridge :
    let x := coordinateEquiv (uPlus + uMinus)
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularGradedOmega x)
    A ≠ 0 ∧
      matrixExteriorDerivative circularGradedDiff A = peirceGradingDeriv P A ∧
      curvatureFromConnection circularGradedDiff A = genJ P A A + genV P A A := by
  have hBridge := circularGradedDiff_yang_mills_bridge (coordinateEquiv (uPlus + uMinus))
  have hCompat := circularGradedDiff_eigencondition (coordinateEquiv (uPlus + uMinus))
  have hA_ne : circularGaugeConnection4
      (circularGradedOmega (coordinateEquiv (uPlus + uMinus))) ≠ 0 := by
    intro hz
    have h0 : coordinateEquiv uPlus = Pi.single 0 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 0
    have h4 : coordinateEquiv uMinus = Pi.single 4 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 4
    have hx : coordinateEquiv (uPlus + uMinus) = Pi.single 0 1 + Pi.single 4 1 := by
      rw [LinearEquiv.map_add, h0, h4]
    have hω0 : circularGradedOmega (coordinateEquiv (uPlus + uMinus)) 0 = uPlusForm := by
      rw [hx]
      simp [circularGradedOmega]
    have hω3 : circularGradedOmega (coordinateEquiv (uPlus + uMinus)) 3 = 0 := by
      rw [hx]
      simp [circularGradedOmega]
    have h02 := congrFun (congrFun hz 0) 2
    have h02' : uPlusForm = 0 := by
      simp only [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply] at h02
      rw [hω0, hω3, add_zero] at h02
      exact h02
    have hc := congrArg
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1) h02'
    have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      0 1 0 1 0).1
    have hev1 := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      0 1 1 0 0).2.1
    rw [map_zero] at hc
    change InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1 +
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) = 0 at hc
    rw [map_add, hev, hev1] at hc
    norm_num at hc
  exact ⟨hA_ne, hCompat, hBridge.2.2.1⟩

/-- T3-02 (R1 + Baseline): Even diff satisfies `MatrixIsHomogeneous 1`, compat, `D_A V = 0`. -/
theorem t3_02_r1_even_plus_baseline_bridge (x : Coordinate) :
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularEvenOmega x)
    MatrixIsHomogeneous 1 A ∧
      matrixExteriorDerivative circularEvenDiff A = peirceGradingDeriv P A ∧
      covariantDerivative A circularEvenDiff (genV P A A) = 0 :=
  ⟨circularEvenOmega_homogeneous x, circularEvenDiff_eigencondition x,
    circularEvenDiff_covariant_vanishing x⟩

/-- T3-03 (R1 + R1): Contrasts nonzero graded/even derivations vs `d² = 0` no-go. -/
theorem t3_03_r1_graded_vs_even_vs_contraction
    (ω : Fin 8 → ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (lam : (Fin 4 → ℂ) →ₗ[ℂ] ℂ)
    (hCompat : matrixExteriorDerivative (contractionOp lam) (circularGaugeConnection4 ω) =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) (circularGaugeConnection4 ω)) :
    circularGradedDiff ≠ 0 ∧ circularEvenDiff ≠ 0 ∧ circularGaugeConnection4 ω = 0 :=
  ⟨circularGradedDiff_ne_zero, circularEvenDiff_ne_zero,
    t2_f1_03_nonzero_contraction_sq_zero_forces_zero ω lam hCompat⟩

/-- T3-04 (R1 + R2): Scalar `circularGaugeConnection4_evalScalar` matches `circularConnectionMat4`
feeding `circularLinkTransport`. -/
theorem t3_04_r1_eval_scalar_plus_r2_link_transport (x : Coordinate) :
    circularGaugeConnection4 (fun i => algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) (x i : ℂ)) =
      (circularConnectionMat4 x).map (algebraMap ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ))) ∧
    circularLinkTransport (fun _ _ => x) 0 0 0 = 1 :=
  ⟨circularGaugeConnection4_evalScalar x, t2_f4_01_link_transport_at_zero_spacing _ 0 0⟩

/-- T3-05 (R1 + R2): Couples baseline vorticity action gap with `continuumPlaquetteAction > 0`. -/
theorem t3_05_r1_hs_vorticity_gap_plus_r2_plaquette_action :
    let x := coordinateEquiv (rootPlus 0 + rootMinus 1)
    ((circularCurvatureMat4 x)ᴴ * circularCurvatureMat4 x).trace -
        (circularCurvatureMat4 x * circularCurvatureMat4 x).trace =
      ((8 * normSq3 (chiralVorticityVec x) : ℝ) : ℂ) ∧
    ∃ (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4),
      0 < continuumPlaquetteAction A y μ ν :=
  ⟨circularCurvatureMat4_vorticity_action_gap _,
    let ⟨A, y, μ, ν, _, _, hPos⟩ := circularLattice_nonabelian_continuum_smooth_witness
    ⟨A, y, μ, ν, hPos⟩⟩

/-- T3-06 (R1 + R2): Constant field `A` and `Φ := A²` satisfy `[A, Φ] = 0`, matching `D_A V = 0`. -/
theorem t3_06_r1_even_cov_vanishing_plus_r2_lattice_cov_diff (x : Coordinate)
    (y : FourSpace) (μ : Fin 4) :
    let A : FourSpace → Fin 4 → Mat4C := fun _ _ => circularConnectionMat4 x
    let Φ : FourSpace → Mat4C := fun _ => circularCurvatureMat4 x
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y μ a) (𝓝[≠] 0) (nhds 0) ∧
      covariantDerivative (circularGaugeConnection4 (circularEvenOmega x))
        circularEvenDiff (genV (chiralExteriorProj4 (Fin 4 → ℂ))
          (circularGaugeConnection4 (circularEvenOmega x))
          (circularGaugeConnection4 (circularEvenOmega x))) = 0 := by
  refine ⟨?_, circularEvenDiff_covariant_vanishing x⟩
  have hLim := continuumCovariantDeriv_connection_sq_zero x y μ
  simpa [hLim] using
    tendsto_latticeCovariantDiff (fun _ _ => circularConnectionMat4 x)
      (fun _ => circularCurvatureMat4 x) y μ (differentiableAt_const _)

/-- T3-07 (R2 + R2): Link transporters feed plaquette `a → 0` limit and colimit cone transport. -/
theorem t3_07_r2_link_plaquette_plus_colimit_cone
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf] [TopologicalSpace B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (hCont : Continuous (fun M : Mat4C => (cone.toColimit k).toRingHom (ι.toRingHom M)))
    (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4)
    (hA : ContDiff ℝ 2 A) :
    Filter.Tendsto
      (fun a : ℝ => (cone.toColimit k).toRingHom
        (ι.toRingHom ((a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1))))
      (𝓝[≠] 0)
      (nhds ((cone.toColimit k).toRingHom (ι.toRingHom (continuumCurvature A y μ ν)))) ∧
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A y μ ν a) (𝓝[≠] 0)
      (nhds (continuumPlaquetteAction A y μ ν)) :=
  ⟨(circularColimit_continuum_transport cone k ι hCont (fun _ _ => 0) A (fun _ => 1)
      y μ ν hA (differentiableAt_const _)).2.1,
    tendsto_wilsonPlaquetteAction A y μ ν hA⟩

/-- T3-08 (R2 + R3): `chiralBundleProjector` (R3) is idempotent and acts by `chiralProjMat4`. -/
theorem t3_08_r2_mat4c_connection_plus_r3_bundle_projector (y : FourSpace) (v : ChiralFiber) :
    ((chiralBundleProjector FourSpace y).comp (chiralBundleProjector FourSpace y)) v =
      chiralProjMat4.mulVec v := by
  rw [chiralBundleProjector_idempotent]
  rfl

/-- T3-09 (R2 + R3): `ymCurvature` on `frameBasis` vectors matches `continuumCurvature`. -/
theorem t3_09_r2_continuum_curvature_plus_r3_ym_curvature
    (A : Mat4CForm 1) (y : FourSpace) (μ ν : Fin 4) (hA : ContDiff ℝ 2 A) :
    ymCurvature A y ![frameBasis μ, frameBasis ν] =
      continuumCurvature (fun z ρ => A z ![frameBasis ρ]) y μ ν := by
  rw [ymCurvature_apply_two A (hA.differentiable (by norm_num)) y (frameBasis μ) (frameBasis ν)]
  dsimp [continuumCurvature]
  have h0 : (fun _ : Fin 1 => frameBasis μ) = ![frameBasis μ] := by
    funext i; fin_cases i; rfl
  have h1 : (fun _ : Fin 1 => frameBasis ν) = ![frameBasis ν] := by
    funext i; fin_cases i; rfl
  rw [h0, h1]

/-- T3-10 (R2 + R3): Non-Abelian circular fields are nontrivial in both discrete `a → 0` and PDE. -/
theorem t3_10_r2_nonabelian_witness_plus_r3_ym_solution :
    (∃ (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4),
      continuumCurvature A y μ ν ≠ 0 ∧ 0 < continuumPlaquetteAction A y μ ν) ∧
    (ymCurvature circularGaugeForm ≠ 0 ∧ YangMillsPDE circularGaugeForm) :=
  ⟨let ⟨A, y, μ, ν, _, hF, hAct⟩ := circularLattice_nonabelian_continuum_smooth_witness
   ⟨A, y, μ, ν, hF, hAct⟩,
   ⟨circularGaugeForm_ymCurvature_ne_zero, circularGaugeForm_solves_yangMillsPDE⟩⟩

/-- T3-11 (R1 + R3): R1 fixed-cut `d² = 0 → A = 0` vs R3 `d² = 0` with `ymCurvature A ≠ 0`. -/
theorem t3_11_r1_nogo_vs_r3_manifold_ext_deriv_bianchi
    (ω₀ : Fin 8 → ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (hZero : matrixExteriorDerivative (0 : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)))
      (circularGaugeConnection4 ω₀) =
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) (circularGaugeConnection4 ω₀)) :
    circularGaugeConnection4 ω₀ = 0 ∧
      ymCurvature circularGaugeForm ≠ 0 ∧
      covExtDeriv circularGaugeForm (ymCurvature circularGaugeForm) = 0 :=
  ⟨t2_f1_02_zero_diff_forces_zero_conn ω₀ hZero,
    circularGaugeForm_ymCurvature_ne_zero,
    bianchi_identity_ymCurvature (circularGaugeForm_contDiff.of_le le_top)⟩

/-- T3-12 (R1 + R3): Connects R1 `circularGradedDiff` curvature with R3 `circularGaugeForm` PDE. -/
theorem t3_12_r1_self_dual_vs_r3_circular_ym_bridge :
    (∃ x : Coordinate,
      let A := circularGaugeConnection4 (circularGradedOmega x)
      A ≠ 0 ∧ curvatureFromConnection circularGradedDiff A ≠ 0 ∧
      matrixExteriorDerivative circularGradedDiff A =
        peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) A) ∧
    (ymCurvature circularGaugeForm ≠ 0 ∧ YangMillsPDE circularGaugeForm) :=
  ⟨t1_f2_05_graded_diff_nondegenerate_witness,
    ⟨circularGaugeForm_ymCurvature_ne_zero, circularGaugeForm_solves_yangMillsPDE⟩⟩

/-! ## Tier 4: Real-World End-to-End Scenarios & Trust Batch Audit (6 Scenarios) -/

/-- T4-01: End-to-End R1 circular split-octonion chiral gauge pipeline (Krein + odd/even diffs). -/
theorem t4_01_circular_chiral_gauge_r1_pipeline :
    let x := coordinateEquiv (uPlus + uMinus)
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A_odd := circularGaugeConnection4 (circularGradedOmega x)
    let A_even := circularGaugeConnection4 (circularEvenOmega x)
    chiralKreinForm (E := FourSpace) (circularCoordToKreinFrame x) (circularCoordToKreinFrame x) =
        2 * wittNorm x ∧
      minkowskiEta4 * minkowskiEta4 = 1 ∧
      circularGradedDiff ≠ 0 ∧
      circularEvenDiff ≠ 0 ∧
      A_odd ≠ 0 ∧
      matrixExteriorDerivative circularGradedDiff A_odd = peirceGradingDeriv P A_odd ∧
      MatrixIsHomogeneous 1 A_even ∧
      matrixExteriorDerivative circularEvenDiff A_even = peirceGradingDeriv P A_even ∧
      covariantDerivative A_even circularEvenDiff (genV P A_even A_even) = 0 := by
  refine ⟨chiralKreinForm_diag_eq_two_wittNorm _, minkowskiEta4_mul_self,
    circularGradedDiff_ne_zero, circularEvenDiff_ne_zero,
    t3_01_r1_graded_plus_baseline_bridge.1, circularGradedDiff_eigencondition _,
    circularEvenOmega_homogeneous _, circularEvenDiff_eigencondition _,
    circularEvenDiff_covariant_vanishing _⟩

/-- T4-02: End-to-End R2 lattice gauge regularization to continuum action & colimit cone. -/
theorem t4_02_lattice_to_continuum_colimit_r2_pipeline
    {A_tower : ℕ → Type*} [∀ k, Ring (A_tower k)] [∀ k, StarRing (A_tower k)]
    {B_inf : Type*} [Ring B_inf] [StarRing B_inf] [TopologicalSpace B_inf]
    (cone : CanonicalTwoSheetedInductiveColimit.InductiveStarColimitCone A_tower B_inf)
    (k : ℕ)
    (ι : CanonicalTwoSheetedInductiveColimit.StarRingHom Mat4C (A_tower k))
    (hCont : Continuous (fun M : Mat4C => (cone.toColimit k).toRingHom (ι.toRingHom M))) :
    circularLinkTransport (fun _ _ => coordinateEquiv (rootPlus 0)) 0 0 0 = 1 ∧
      (∃ (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4),
        ContDiff ℝ 2 A ∧
        continuumCurvature A y μ ν ≠ 0 ∧
        0 < continuumPlaquetteAction A y μ ν ∧
        Filter.Tendsto
          (fun a : ℝ => (cone.toColimit k).toRingHom
            (ι.toRingHom ((a ^ 2)⁻¹ • (wilsonPlaquette A y μ ν a - 1))))
          (𝓝[≠] 0)
          (nhds ((cone.toColimit k).toRingHom (ι.toRingHom (continuumCurvature A y μ ν))))) := by
  refine ⟨t2_f4_01_link_transport_at_zero_spacing _ 0 0, ?_⟩
  rcases circularLattice_nonabelian_continuum_smooth_witness with ⟨A, y, μ, ν, hA, hCurv, hAct⟩
  exact ⟨A, y, μ, ν, hA, hCurv, hAct,
    (circularColimit_continuum_transport cone k ι hCont (fun _ _ => 0) A (fun _ => 1)
      y μ ν hA (differentiableAt_const _)).2.1⟩

/-- T4-03: End-to-End R3 smooth 4-manifold bundle, Bianchi identity, Hodge stars & YM PDE. -/
theorem t4_03_smooth_manifold_bundle_ym_pde_r3_pipeline
    (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    IsManifold (𝓡 4) ⊤ FourSpace ∧
      ContMDiffVectorBundle ⊤ (Fin 4 → ℂ) (Bundle.Trivial FourSpace (Fin 4 → ℂ)) (𝓡 4) ∧
      hodgeStar4EuclMap (hodgeStar4EuclMap η) = η ∧
      hodgeStar4MinkowskiMap (hodgeStar4MinkowskiMap η) = -η ∧
      covExtDeriv circularGaugeForm (ymCurvature circularGaugeForm) = 0 ∧
      ymCurvature circularGaugeForm ≠ 0 ∧
      YangMillsPDE circularGaugeForm :=
  ⟨inferInstance, inferInstance, hodgeStar4EuclMap_involutive η, hodgeStar4MinkowskiMap_sq_neg η,
    bianchi_identity_ymCurvature (circularGaugeForm_contDiff.of_le le_top),
    circularGaugeForm_ymCurvature_ne_zero,
    circularGaugeForm_solves_yangMillsPDE⟩

/-- T4-04: Unified R1 + R2 + R3 non-Abelian circular split-octonion Yang–Mills consistency. -/
theorem t4_04_unified_r1_r2_r3_nonabelian_consistency :
    (weylUpperMat (coordinateEquiv (rootPlus 0 + rootMinus 1)) *
        weylLowerMat (coordinateEquiv (rootPlus 0 + rootMinus 1)) ≠
      weylLowerMat (coordinateEquiv (rootPlus 0 + rootMinus 1)) *
        weylUpperMat (coordinateEquiv (rootPlus 0 + rootMinus 1))) ∧
    (∃ x : Coordinate,
      let A := circularGaugeConnection4 (circularGradedOmega x)
      A ≠ 0 ∧ curvatureFromConnection circularGradedDiff A ≠ 0 ∧
      matrixExteriorDerivative circularGradedDiff A =
        peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) A) ∧
    (∃ (A : FourSpace → Fin 4 → Mat4C) (y : FourSpace) (μ ν : Fin 4),
      continuumCurvature A y μ ν ≠ 0 ∧ 0 < continuumPlaquetteAction A y μ ν) ∧
    (ymCurvature circularGaugeForm ≠ 0 ∧
      covExtDeriv circularGaugeForm (ymCurvature circularGaugeForm) = 0 ∧
      YangMillsPDE circularGaugeForm) :=
  ⟨weylChannel_noncomm_sheet_blocks_witness,
    t1_f2_05_graded_diff_nondegenerate_witness,
    (let ⟨A, y, μ, ν, _, hCurv, hAct⟩ := circularLattice_nonabelian_continuum_smooth_witness
     ⟨A, y, μ, ν, hCurv, hAct⟩),
    ⟨circularGaugeForm_ymCurvature_ne_zero,
      bianchi_identity_ymCurvature (circularGaugeForm_contDiff.of_le le_top),
      circularGaugeForm_solves_yangMillsPDE⟩⟩

/-- T4-05: Krein indefinite signature & Lorentzian (`⋆² = -id`) vs Euclidean (`⋆² = +id`) Hodge. -/
theorem t4_05_krein_indefinite_vs_lorentzian_hodge_consistency
    (η : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C) :
    let x := coordinateEquiv (uPlus + uMinus + rootPlus 0 + rootMinus 0)
    (x ≠ 0 ∧ fiberKreinPairing (chiralFiberToKreinFrame.symm (circularCoordToKreinFrame x))
      (chiralFiberToKreinFrame.symm (circularCoordToKreinFrame x)) = 0) ∧
      minkowskiEta4 * minkowskiEta4 = 1 ∧
      minkowskiEta4.det = -1 ∧
      hodgeStar4EuclMap (hodgeStar4EuclMap η) = η ∧
      hodgeStar4MinkowskiMap (hodgeStar4MinkowskiMap η) = -η :=
  ⟨t2_f8_03_krein_null_lightcone_indefinite, minkowskiEta4_mul_self, minkowskiEta4_det,
    hodgeStar4EuclMap_involutive η, hodgeStar4MinkowskiMap_sq_neg η⟩

/-! ## Tier 5: Adversarial Coverage Hardening (M1, M2 & Cross-Module Bridges) -/

/-- T5-M1-01: Exterior matrix noncommutativity witnesses and asymmetric block `compat_iff`. -/
theorem t5_m1_01_exterior_noncomm_and_offblock_compat :
    (∃ A B : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)), A * B ≠ B * A) ∧
    (∃ A B : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ (Fin 4 → ℂ)), A * B ≠ B * A) ∧
    (let U : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) := !![uPlusForm, 0; 0, 0]
     let L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) := !![0, uMinusForm; 0, 0]
     let P := chiralExteriorProj4 (Fin 4 → ℂ)
     U ≠ L ∧
     matrixExteriorDerivative circularGradedDiff (chiralOffBlock4 U L) =
       peirceGradingDeriv P (chiralOffBlock4 U L) ∧
     (chiralOffBlock4 U L = chiralOffBlock4 U 0 → L = 0)) := by
  refine ⟨mat2_exterior_noncomm_witness, mat4_exterior_noncomm_witness, ?_⟩
  intro U L P
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [U, L, Matrix.of_apply, Matrix.cons_val_zero] at h00
    have hc := congrArg
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1) h00
    have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      0 1 0 1 0).1
    have hev1 := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      0 1 1 0 0).2.1
    rw [map_zero] at hc
    change InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1 +
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) = 0
      at hc
    rw [map_add, hev, hev1] at hc
    norm_num at hc
  · rw [chiralOffBlock4_eigencondition_iff]
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [U, circularGradedDiff_uPlusForm, LinearMap.map_zero]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [L, circularGradedDiff_uMinusForm, LinearMap.map_zero]
  · intro hEq
    exact ((chiralOffBlock4_eq_iff U L U 0).mp hEq).2

/-- T5-M1-02: Graded diff generator action, `uMinusForm` eigenform, `k=0` & `k=2` Leibniz rule. -/
theorem t5_m1_02_graded_diff_generators_even_degree_and_uminus
    (y : ExteriorAlgebra ℂ (Fin 4 → ℂ)) :
    circularGradedDiff (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ))) =
      circularGradedTargetMap (Pi.single 0 (1 : ℂ)) ∧
    circularGradedDiff uMinusForm = -uMinusForm ∧
    circularGradedDiff (1 : ExteriorAlgebra ℂ (Fin 4 → ℂ)) = 0 ∧
    (let x2 := ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
        ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))
     circularGradedDiff (x2 * y) = circularGradedDiff x2 * y + x2 * circularGradedDiff y) ∧
    circularGradedDiff (uPlusForm * uMinusForm) ≠ 0 := by
  refine ⟨circularGradedDiff_ι _, circularGradedDiff_uMinusForm, ?_, ?_, ?_⟩
  · have hdeg0 : IsHomogeneousExteriorDegree 0 (1 : ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
      Submodule.subset_span ⟨fun i => Fin.elim0 i, by simp⟩
    have hL := circularGradedDiff_isGradedDerivation 0 1 1 hdeg0
    simp only [one_mul, mul_one, pow_zero, one_smul] at hL
    have h0 : (0 : ExteriorAlgebra ℂ (Fin 4 → ℂ)) = circularGradedDiff 1 := by
      calc
        0 = circularGradedDiff 1 - circularGradedDiff 1 := (sub_self _).symm
        _ = (circularGradedDiff 1 + circularGradedDiff 1) - circularGradedDiff 1 := by
          nth_rw 1 [← hL]
        _ = circularGradedDiff 1 := add_sub_cancel_right _ _
    exact h0.symm
  · intro x2
    have hx2 : IsHomogeneousExteriorDegree 2 x2 := by
      refine Submodule.subset_span ⟨![Pi.single 0 (1 : ℂ), Pi.single 1 (1 : ℂ)], ?_⟩
      simp [x2]
    have hL := circularGradedDiff_isGradedDerivation 2 x2 y hx2
    simpa using hL
  · have hdeg0 :
        IsHomogeneousExteriorDegree 1 (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ) : Fin 4 → ℂ)) :=
      (homogeneous_one_iff_exists_generator _).mpr ⟨_, rfl⟩
    have hdeg1 :
        IsHomogeneousExteriorDegree 1 (ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ) : Fin 4 → ℂ)) :=
      (homogeneous_one_iff_exists_generator _).mpr ⟨_, rfl⟩
    have hdeg2 :
        IsHomogeneousExteriorDegree 2
          (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ) : Fin 4 → ℂ) *
            ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ) : Fin 4 → ℂ)) :=
      Submodule.subset_span ⟨![Pi.single 0 (1 : ℂ), Pi.single 1 (1 : ℂ)], by simp⟩
    have hd0 : circularGradedDiff (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ))) = 1 := by
      rw [circularGradedDiff_ι]; simp [circularGradedTargetMap]
    have hd1 : circularGradedDiff (ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) =
        ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
          ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) := by
      rw [circularGradedDiff_ι]; simp [circularGradedTargetMap]
    have hd01 :
        circularGradedDiff
          (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
            ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) =
          ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) := by
      rw [circularGradedDiff_isGradedDerivation 1 _ _ hdeg0, hd0, hd1, one_mul, pow_one,
        neg_one_smul, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]
      simp
    have hmul :
        circularGradedDiff (uPlusForm * uMinusForm) =
          (2 : ℂ) • (ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) * uMinusForm) := by
      have h1 :
          circularGradedDiff
            ((ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
              ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) * uMinusForm) =
            ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) * uMinusForm -
              (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
                ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) * uMinusForm := by
        rw [circularGradedDiff_isGradedDerivation 2 _ _ hdeg2, hd01,
          circularGradedDiff_uMinusForm]
        simp [mul_neg, sub_eq_add_neg]
      have h2 :
          circularGradedDiff (ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) * uMinusForm) =
            (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
              ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) * uMinusForm +
              ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) * uMinusForm := by
        rw [circularGradedDiff_isGradedDerivation 1 _ _ hdeg1, hd1,
          circularGradedDiff_uMinusForm]
        simp [mul_neg]
      unfold uPlusForm
      rw [add_mul, map_add, h1, h2]
      rw [← one_add_one_eq_two, add_smul, one_smul]
      abel
    intro hz
    rw [hmul] at hz
    have hcoeff := congrArg
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 1 3) hz
    have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      1 3 1 3 0).1
    have h23 :
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 1 3
          (ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) *
            (ExteriorAlgebra.ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) *
              ExteriorAlgebra.ι ℂ (Pi.single (3 : Fin 4) (1 : ℂ) : Fin 4 → ℂ))) = 0 := by
      have hc1 :
          contractionOp (LinearMap.proj (1 : Fin 4))
            (ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) *
              (ExteriorAlgebra.ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) *
                ExteriorAlgebra.ι ℂ (Pi.single (3 : Fin 4) (1 : ℂ) : Fin 4 → ℂ))) =
            ExteriorAlgebra.ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) *
              ExteriorAlgebra.ι ℂ (Pi.single (3 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) := by
        rw [contraction_op_generator_mul]
        have h12 :
            contractionOp (LinearMap.proj (1 : Fin 4))
              (ExteriorAlgebra.ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) *
                ExteriorAlgebra.ι ℂ (Pi.single (3 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)) = 0 := by
          rw [contraction_op_generator_mul]
          simp [contraction_on_generator]
        simp [h12]
      have hc3 :
          contractionOp (LinearMap.proj (3 : Fin 4))
            (ExteriorAlgebra.ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) *
              ExteriorAlgebra.ι ℂ (Pi.single (3 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)) =
            -(ExteriorAlgebra.ι ℂ (Pi.single (2 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)) := by
        rw [contraction_op_generator_mul]
        simp [contraction_on_generator, Algebra.algebraMap_eq_smul_one]
      unfold InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hc1, hc3, AlgHom.toLinearMap_apply, map_neg]
      simp [ExteriorAlgebra.algebraMapInv]
    rw [map_zero, map_smul] at hcoeff
    unfold uMinusForm at hcoeff
    rw [mul_sub, map_sub, h23, zero_sub] at hcoeff
    change (2 : ℂ) • -(InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff
      1 3
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1 *
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 3)) = 0
      at hcoeff
    rw [smul_neg, smul_eq_mul, neg_eq_zero, hev] at hcoeff
    norm_num at hcoeff

private def scalarFlipStar : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  LinearMap.id - (2 : ℂ) • LinearMap.smulRight
    (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ)).toLinearMap
    (1 : ExteriorAlgebra ℂ (Fin 4 → ℂ))

private lemma scalarFlipStar_fixes_mul (a b : ExteriorAlgebra ℂ (Fin 4 → ℂ))
    (ha : (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ)) a = 0) :
    scalarFlipStar (a * b) = a * b := by
  unfold scalarFlipStar
  simp [map_mul, ha]

private lemma algebraMapInv_uPlusForm :
    (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ)) uPlusForm = 0 := by
  unfold uPlusForm
  simp [ExteriorAlgebra.algebraMapInv]

private lemma algebraMapInv_uMinusForm :
    (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ)) uMinusForm = 0 := by
  unfold uMinusForm
  simp [ExteriorAlgebra.algebraMapInv]

/-- T5-M1-03: Non-vacuous `circularGradedDiff_yang_mills_bridge_general` with `X` non-off-diagonal
(`idempotencyDefect X ≠ 0`, `genV P X X ≠ 0`) and nontrivial `star ≠ id` fixing `genV P A A ≠ 0`. -/
theorem t5_m1_03_graded_diff_bridge_general_nonvacuous :
    let x := coordinateEquiv (uPlus + uMinus)
    let P := chiralExteriorProj4 (Fin 4 → ℂ)
    let A := circularGaugeConnection4 (circularGradedOmega x)
    let X := P + A
    scalarFlipStar ≠ LinearMap.id ∧
    idempotencyDefect X ≠ 0 ∧
    genV P X X ≠ 0 ∧
    evenGrade P (idempotencyDefect X) - idempotencyDefect (evenGrade P X) = genV P X X ∧
    isSelfDualCurvature scalarFlipStar (genV P A A) ∧
    covariantDerivative A 0 (matrixHodgeStar scalarFlipStar (curvatureFromConnection 0 A)) = 0 ∧
    curvatureFromConnection circularGradedDiff A = genJ P A A + genV P A A := by
  intro x P A X
  have hBr := circularGradedDiff_yang_mills_bridge_general scalarFlipStar x X
  dsimp only at hBr
  have hstar_ne : scalarFlipStar ≠ LinearMap.id := by
    intro h
    have h1 := congrArg (fun f : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) => f 1) h
    simp [scalarFlipStar] at h1
  have hx0 : x = Pi.single 0 1 + Pi.single 4 1 := by
    have h0 : coordinateEquiv uPlus = Pi.single 0 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 0
    have h4 : coordinateEquiv uMinus = Pi.single 4 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 4
    change coordinateEquiv (uPlus + uMinus) = Pi.single 0 1 + Pi.single 4 1
    rw [LinearEquiv.map_add, h0, h4]
  have hω : ∀ i : Fin 8, circularGradedOmega x i =
      if i = 0 then uPlusForm else if i = 4 then uMinusForm else 0 := by
    intro i; fin_cases i <;> simp [circularGradedOmega, hx0]
  have hAA_eq : A * A = genV P A A := by
    dsimp only [P, A]
    unfold circularGaugeConnection4 chiralExteriorProj4
    rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4,
      chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
    ext i j; fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hP2 : P * P = P := chiralProj4_idempotent _
  have hPA : P * A + A * P = A := by
    have hPhi := hBr.1
    rw [genPhi, conePlus, coneMinus] at hPhi
    have h1 : P * A * P = 0 := by
      dsimp only [P, A]
      unfold chiralExteriorProj4 circularGaugeConnection4
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [chiralProj4, chiralDiagBlock4, chiralOffBlock4, Matrix.mul_apply, Fin.sum_univ_four]
    calc
      P * A + A * P = P * A * (1 - P) + (1 - P) * A * P + 2 • (P * A * P) := by noncomm_ring
      _ = A + 2 • 0 := by rw [hPhi, h1]
      _ = A := by simp
  have hDefect_eq : idempotencyDefect X = A * A := by
    unfold idempotencyDefect
    dsimp only [X]
    calc
      (P + A) * (P + A) - (P + A) = (P * P - P) + (P * A + A * P - A) + A * A := by noncomm_ring
      _ = A * A := by rw [hP2, sub_self, hPA, sub_self, zero_add, zero_add]
  have hGenVX_eq : genV P X X = A * A := by
    have hPX : P * X * (1 - P) + (1 - P) * X * P = A := by
      dsimp only [X]
      have hP1 : P * P * (1 - P) = 0 := by
        rw [hP2, mul_sub, mul_one, hP2, sub_self]
      have hP2' : (1 - P) * P * P = 0 := by
        rw [sub_mul, one_mul, hP2, sub_self, zero_mul]
      have hA_off : P * A * (1 - P) + (1 - P) * A * P = A := by
        have h := hBr.1
        simpa [genPhi, conePlus, coneMinus] using h
      calc
        P * (P + A) * (1 - P) + (1 - P) * (P + A) * P
            = (P * P * (1 - P) + (1 - P) * P * P) +
                (P * A * (1 - P) + (1 - P) * A * P) := by noncomm_ring
        _ = A := by rw [hP1, hP2', add_zero, zero_add, hA_off]
    have hz : P * X * (1 - P) * (P * X * (1 - P)) +
        (1 - P) * X * P * ((1 - P) * X * P) = 0 := by
      have hp0 : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP2, sub_self]
      have hp1 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP2, sub_self]
      have hz1 : P * X * (1 - P) * (P * X * (1 - P)) = 0 := by
        calc
          P * X * (1 - P) * (P * X * (1 - P))
              = P * X * ((1 - P) * P) * X * (1 - P) := by noncomm_ring
          _ = 0 := by rw [hp0]; noncomm_ring
      have hz2 : (1 - P) * X * P * ((1 - P) * X * P) = 0 := by
        calc
          (1 - P) * X * P * ((1 - P) * X * P)
              = (1 - P) * X * (P * (1 - P)) * X * P := by noncomm_ring
          _ = 0 := by rw [hp1]; noncomm_ring
      rw [hz1, hz2, add_zero]
    unfold genV conePlus coneMinus
    calc
      anticomm (P * X * (1 - P)) ((1 - P) * X * P)
          = (P * X * (1 - P) + (1 - P) * X * P) * (P * X * (1 - P) + (1 - P) * X * P) -
              (P * X * (1 - P) * (P * X * (1 - P)) + (1 - P) * X * P * ((1 - P) * X * P)) := by
            unfold anticomm; noncomm_ring
      _ = A * A - 0 := by rw [hPX, hz]
      _ = A * A := sub_zero _
  have hAA_ne : A * A ≠ 0 := by
    have hA00 : A 0 0 = 0 := by simp [A, circularGaugeConnection4, chiralOffBlock4]
    have hA01 : A 0 1 = 0 := by simp [A, circularGaugeConnection4, chiralOffBlock4]
    have hA02 : A 0 2 = uPlusForm := by
      simp [A, circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 0, hω 3]
    have hA03 : A 0 3 = 0 := by
      simp [A, circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 1, hω 2]
    have hA20 : A 2 0 = uMinusForm := by
      simp [A, circularGaugeConnection4, chiralOffBlock4, weylLowerExt, hω 4, hω 7]
    have hAA00 : (A * A) 0 0 = uPlusForm * uMinusForm := by
      rw [Matrix.mul_apply, Fin.sum_univ_four, hA00, hA01, hA02, hA03, hA20]
      simp
    intro hz
    have h00 := congrFun (congrFun hz 0) 0
    rw [hAA00, Matrix.zero_apply] at h00
    let p13 : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) :=
      { toFun := fun v => ![0, v 1, 0, v 3]
        map_add' := fun a b => by ext i; fin_cases i <;> simp
        map_smul' := fun c a => by ext i; fin_cases i <;> simp }
    have hp13 : ∀ μ : Fin 4, p13 (Pi.single μ (1 : ℂ)) =
        if μ = 1 ∨ μ = 3 then Pi.single μ (1 : ℂ) else 0 := by
      intro μ; ext i; fin_cases μ <;> fin_cases i <;> simp [p13]
    have hmap := congrArg (ExteriorAlgebra.map p13) h00
    have hp : ExteriorAlgebra.map p13 uPlusForm = ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) := by
      unfold uPlusForm
      rw [map_add, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
        hp13 0, hp13 1]
      simp
    have hm : ExteriorAlgebra.map p13 uMinusForm =
        -(ExteriorAlgebra.ι ℂ (Pi.single 3 (1 : ℂ))) := by
      unfold uMinusForm
      rw [map_sub, map_mul, ExteriorAlgebra.map_apply_ι, ExteriorAlgebra.map_apply_ι,
        hp13 2, hp13 3]
      simp
    rw [map_mul, hp, hm, map_zero, mul_neg] at hmap
    have hc := congrArg
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 1 3) hmap
    have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      1 3 1 3 0).1
    rw [map_neg, map_zero] at hc
    change -(InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 1 3
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1 *
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 3)) = 0
      at hc
    rw [hev] at hc
    norm_num at hc
  have hSD : isSelfDualCurvature scalarFlipStar (genV P A A) := by
    rw [← hAA_eq]
    ext i j
    change scalarFlipStar ((A * A) i j) = (A * A) i j
    rw [Matrix.mul_apply]
    have hinv_ω : ∀ m : Fin 8,
        (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ))
          (circularGradedOmega x m) = 0 := by
      intro m
      rw [hω m]
      split_ifs
      · exact algebraMapInv_uPlusForm
      · exact algebraMapInv_uMinusForm
      · exact map_zero _
    have hinv_zero : ∀ r s : Fin 4,
        (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ)) (A r s) = 0 := by
      intro r s
      fin_cases r <;> fin_cases s <;>
        (dsimp only [A]
         unfold circularGaugeConnection4 chiralOffBlock4 weylUpperExt weylLowerExt) <;>
        simp [map_add, map_sub, map_neg, map_smul, hinv_ω]
    have hterm : ∀ k : Fin 4, scalarFlipStar (A i k * A k j) = A i k * A k j := fun k =>
      scalarFlipStar_fixes_mul (A i k) (A k j) (hinv_zero i k)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => hterm k
  exact ⟨hstar_ne, by rw [hDefect_eq]; exact hAA_ne, by rw [hGenVX_eq]; exact hAA_ne,
    hBr.2.1, hSD, hBr.2.2.2.2.2.2 hSD, hBr.2.2.1⟩

private def evenDiagFlipMap : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![v 0, -v 1, v 2, -v 3]
  map_add' x y := by ext i; fin_cases i <;> (simp; try abel)
  map_smul' c x := by ext i; fin_cases i <;> simp

private def evenDiagStar : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) :=
  (ExteriorAlgebra.map evenDiagFlipMap).toLinearMap

/-- T5-M1-04: Non-vacuous `circularEvenDiff_self_dual_covariant_vanishing` under nontrivial
`evenDiagStar ≠ id`, plus `circularEvenDiff_ι` and sign-mismatch negative compat check. -/
theorem t5_m1_04_even_diff_self_dual_nonvacuous_and_sign_mismatch :
    circularEvenDiff (ExteriorAlgebra.ι ℂ (Pi.single 2 (1 : ℂ))) =
      ExteriorAlgebra.ι ℂ (circularEvenMap (Pi.single 2 (1 : ℂ))) ∧
    evenDiagStar ≠ LinearMap.id ∧
    (let x := coordinateEquiv (uPlus + uMinus)
     let P := chiralExteriorProj4 (Fin 4 → ℂ)
     let A := circularGaugeConnection4 (circularEvenOmega x)
     genV P A A ≠ 0 ∧
     isSelfDualCurvature evenDiagStar (genV P A A) ∧
     matrixHodgeStar evenDiagStar (genV P A A) ≠ 0 ∧
     covariantDerivative A circularEvenDiff (matrixHodgeStar evenDiagStar (genV P A A)) = 0) ∧
    matrixExteriorDerivative circularEvenDiff
        (circularGaugeConnection4 (circularGradedOmega (coordinateEquiv uPlus))) ≠
      peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ))
        (circularGaugeConnection4 (circularGradedOmega (coordinateEquiv uPlus))) := by
  refine ⟨circularEvenDiff_ι _, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun f : Module.End ℂ (ExteriorAlgebra ℂ (Fin 4 → ℂ)) =>
      f (ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ)))) h
    have hflip : evenDiagFlipMap (Pi.single (1 : Fin 4) (1 : ℂ)) =
        -Pi.single (1 : Fin 4) (1 : ℂ) := by
      ext i; fin_cases i <;> simp [evenDiagFlipMap]
    change (ExteriorAlgebra.map evenDiagFlipMap)
        (ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ))) =
      ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ)) at h0
    rw [ExteriorAlgebra.map_apply_ι, hflip, map_neg] at h0
    have h2 :
        (2 : ℂ) • ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) = 0 := by
      rw [← one_add_one_eq_two, add_smul, one_smul]
      calc
        ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) +
            ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)
            = -(ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)) +
                ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) := by
              nth_rw 1 [← h0]
        _ = 0 := neg_add_cancel _
    have hzero :
        ExteriorAlgebra.ι ℂ (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ) = 0 := by
      have h' := congrArg (fun z => (2 : ℂ)⁻¹ • z) h2
      rw [smul_smul, smul_zero, inv_mul_cancel₀ (by norm_num), one_smul] at h'
      exact h'
    have hs := (ExteriorAlgebra.ι_eq_zero_iff (R := ℂ)
      (Pi.single (1 : Fin 4) (1 : ℂ) : Fin 4 → ℂ)).mp hzero
    simpa using congrFun hs 1
  · intro x P A
    have hx0 : x = Pi.single 0 1 + Pi.single 4 1 := by
      have h0 : coordinateEquiv uPlus = Pi.single 0 1 := by
        simpa [frame] using coordinateEquiv_apply_frame 0
      have h4 : coordinateEquiv uMinus = Pi.single 4 1 := by
        simpa [frame] using coordinateEquiv_apply_frame 4
      change coordinateEquiv (uPlus + uMinus) = Pi.single 0 1 + Pi.single 4 1
      rw [LinearEquiv.map_add, h0, h4]
    have hω : ∀ i : Fin 8, circularEvenOmega x i =
        if i = 0 then
          InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0
        else if i = 4 then
          InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 2
        else 0 := by
      intro i
      fin_cases i <;>
        simp [circularEvenOmega,
          InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm, hx0]
    have hGenV_eq : genV P A A = A * A := by
      dsimp only [P, A]
      unfold circularGaugeConnection4 chiralExteriorProj4
      rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4,
        chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
      ext i j; fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
    have hVne : genV P A A ≠ 0 := by
      have hAA00 : (A * A) 0 0 =
          InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
            InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 2 := by
        rw [Matrix.mul_apply, Fin.sum_univ_four]
        have h00 : A 0 0 = 0 := by simp [A, circularGaugeConnection4, chiralOffBlock4]
        have h01 : A 0 1 = 0 := by simp [A, circularGaugeConnection4, chiralOffBlock4]
        have h02 : A 0 2 =
            InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 := by
          simp [A, circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 0, hω 3]
        have h03 : A 0 3 = 0 := by
          simp [A, circularGaugeConnection4, chiralOffBlock4, weylUpperExt, hω 1, hω 2]
        have h20 : A 2 0 =
            InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 2 := by
          simp [A, circularGaugeConnection4, chiralOffBlock4, weylLowerExt, hω 4, hω 7]
        rw [h00, h01, h02, h03, h20]; simp
      intro hz
      rw [hGenV_eq] at hz
      have h00 := congrFun (congrFun hz 0) 0
      rw [hAA00, Matrix.zero_apply] at h00
      have hc := congrArg
        (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 2) h00
      have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
        0 2 0 2 0).1
      rw [map_zero, hev] at hc
      norm_num at hc
    have hSD : isSelfDualCurvature evenDiagStar (genV P A A) := by
      have hω' : ∀ i : Fin 8, circularEvenOmega x i =
          if i = 0 then ExteriorAlgebra.ι ℂ (Pi.single 0 1)
          else if i = 4 then ExteriorAlgebra.ι ℂ (Pi.single 2 1)
          else 0 := by
        intro i; fin_cases i <;> simp [circularEvenOmega, hx0]
      have hf0 : evenDiagFlipMap (Pi.single 0 (1 : ℂ)) = Pi.single 0 1 := by
        ext i; fin_cases i <;> simp [evenDiagFlipMap]
      have hf2 : evenDiagFlipMap (Pi.single 2 (1 : ℂ)) = Pi.single 2 1 := by
        ext i; fin_cases i <;> simp [evenDiagFlipMap]
      have hfix : ∀ i j : Fin 4, evenDiagStar (A i j) = A i j := by
        intro i j
        change (ExteriorAlgebra.map evenDiagFlipMap) (A i j) = A i j
        fin_cases i <;> fin_cases j <;>
          simp [A, circularGaugeConnection4, chiralOffBlock4, weylUpperExt, weylLowerExt, hω',
            ExteriorAlgebra.map_apply_ι, hf0, hf2]
      rw [hGenV_eq]
      unfold isSelfDualCurvature matrixHodgeStar
      ext i j
      simp only [Matrix.mul_apply]
      change (ExteriorAlgebra.map evenDiagFlipMap) (∑ k : Fin 4, A i k * A k j) =
        ∑ k : Fin 4, A i k * A k j
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
      exact congrArg₂ (· * ·) (hfix i k) (hfix k j)
    refine ⟨hVne, hSD, ?_, circularEvenDiff_self_dual_covariant_vanishing evenDiagStar x hSD⟩
    rw [hSD]
    exact hVne
  · intro h
    have h0 := (circularGaugeConnection4_eigencondition_iff circularEvenDiff
      (circularGradedOmega (coordinateEquiv uPlus))).mp h 0
    have hc : coordinateEquiv uPlus = Pi.single 0 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 0
    have hω0 : circularGradedOmega (coordinateEquiv uPlus) 0 = uPlusForm := by
      simp [circularGradedOmega, hc]
    rw [hω0] at h0
    have hbad : (2 : ℂ) • (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
        ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) +
        ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) = uPlusForm := by
      calc
        (2 : ℂ) • (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
            ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) +
            ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))
            = circularEvenDiff uPlusForm := by
              unfold uPlusForm circularEvenDiff
              have hf0 : circularEvenMap (Pi.single 0 (1 : ℂ)) = Pi.single 0 1 := by
                ext i; fin_cases i <;> simp [circularEvenMap]
              have hf1 : circularEvenMap (Pi.single 1 (1 : ℂ)) = Pi.single 1 1 := by
                ext i; fin_cases i <;> simp [circularEvenMap]
              rw [map_add, InfoGeometry.CliffordExteriorLift.exteriorLift_even_derivation,
                InfoGeometry.CliffordExteriorLift.exteriorLift_ι,
                InfoGeometry.CliffordExteriorLift.exteriorLift_ι, hf0, hf1, ← two_smul ℂ]
        _ = uPlusForm := h0
    unfold uPlusForm at hbad
    have hcoeff := congrArg
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1) hbad
    have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      0 1 0 1 0).1
    have hev1 := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
      0 1 1 0 0).2.1
    rw [map_add, map_add, map_smul, smul_eq_mul] at hcoeff
    change (2 : ℂ) * InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) +
      InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) =
      InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
        InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) +
      InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
      (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) at hcoeff
    rw [hev, hev1] at hcoeff
    norm_num at hcoeff

/-- T5-M2-01: Flagged `circularColimit_continuum_transport_tailTower` at `k = 0` and `k = 5`,
`circularLattice_nonabelian_continuum_witness`, and all 11 conjuncts of
`circularColimit_continuum_transport`. -/
theorem t5_m2_01_tailtower_full_transport_and_stages (y : FourSpace) :
    let cone := CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C
    let ι5 := diagTowerStarHom 5
    let ψ5 : Mat4C →+* CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C :=
      (cone.toColimit 5).toRingHom.comp ι5.toRingHom
    let A : FourSpace → Fin 4 → Mat4C :=
      fun z μ => circularConnectionMat4 (witnessCircularField z μ)
    let P_inf := ψ5 chiralProjMat4
    let A_xy := ψ5 (circularConnectionMat4 (witnessCircularField y 0))
    let F_xy := ψ5 (circularCurvatureMat4 (witnessCircularField y 0))
    (ψ5 (continuumCurvature A y 0 1) ≠ 0 ∧
      continuumPlaquetteAction A y 0 1 = 4 ∧
      chiralVorticityVec witnessCoord ≠ 0) ∧
    (Filter.Tendsto (fun a : ℝ => ψ5 (latticeCovariantDiff A (fun _ => 1) y 0 a))
        (𝓝[≠] 0) (nhds (ψ5 (continuumCovariantDeriv A (fun _ => 1) y 0))) ∧
      Filter.Tendsto (fun a : ℝ => ψ5 ((a ^ 2)⁻¹ • (wilsonPlaquette A y 0 1 a - 1)))
        (𝓝[≠] 0) (nhds (ψ5 (continuumCurvature A y 0 1))) ∧
      Filter.Tendsto (fun a : ℝ => ψ5 (circularLinkTransport witnessCircularField y 0 a))
        (𝓝 0) (nhds (1 : CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C)) ∧
      Filter.Tendsto
        (fun a : ℝ => ψ5 (a⁻¹ • (circularLinkTransport witnessCircularField y 0 a - 1)))
        (𝓝[≠] 0) (nhds A_xy) ∧
      (∀ a : ℝ, (cone.toColimit 6).toRingHom
          ((cone.stepHom 5).toRingHom (ι5.toRingHom (wilsonPlaquette A y 0 1 a))) =
        ψ5 (wilsonPlaquette A y 0 1 a)) ∧
      P_inf * P_inf = P_inf ∧
      star P_inf = P_inf ∧
      CanonicalTwoSheetedInductiveColimit.opElectron P_inf A_xy A_xy = A_xy ∧
      CanonicalTwoSheetedInductiveColimit.opQuadraticCoupling P_inf A_xy A_xy = F_xy ∧
      (cone.toColimit 6).toRingHom
          ((cone.stepHom 5).toRingHom
            (ι5.toRingHom (circularCurvatureMat4 (witnessCircularField y 0)))) = F_xy ∧
      CanonicalTwoSheetedInductiveColimit.opSpinDipole P_inf A_xy A_xy =
        CanonicalTwoSheetedInductiveColimit.opBitGrading P_inf * F_xy) ∧
    (let ι0 := diagTowerStarHom 0
     let ψ0 := (cone.toColimit 0).toRingHom.comp ι0.toRingHom
     ψ0 (continuumCurvature A y 0 1) ≠ 0) := by
  intro cone ι5 ψ5 A P_inf A_xy F_xy
  have hW := circularLattice_nonabelian_continuum_witness y
  have hT0 := circularColimit_continuum_transport_tailTower 0 y
  have hT5 := circularColimit_continuum_transport_tailTower 5 y
  have hψ_eq : (ψ5 : Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C) =
      fun M _ => M := by
    funext M n
    change CanonicalTwoSheetedInductiveColimit.towerColimitFn 5 (fun _ => M, M) n = M
    by_cases hn : n < 5 <;> simp [CanonicalTwoSheetedInductiveColimit.towerColimitFn, hn]
  have hCont : Continuous (cone.toColimit 5 |>.toRingHom.comp ι5.toRingHom) := by
    change Continuous (ψ5 : Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C)
    rw [hψ_eq]
    exact continuous_pi fun _ => continuous_id
  have hA_cd : ContDiff ℝ 2 A := by
    have hA_eq : A = fun _ μ => circularConnectionMat4 (witnessCircularField 0 μ) := rfl
    rw [hA_eq]
    exact contDiff_const
  have hAll := circularColimit_continuum_transport cone 5 ι5 hCont witnessCircularField A
    (fun _ => 1) y 0 1 hA_cd (differentiableAt_const 1)
  exact ⟨⟨hT5.1, hW.2.2.2.1, hW.2.1⟩, hAll, hT0.1⟩

/-- T5-M2-02: Spacetime-varying `C²` non-Abelian field where BOTH derivative curl and commutator
are simultaneously nonzero and `wilsonPlaquette` + action converge (plus orientation reversal). -/
theorem t5_m2_02_nonabelian_varying_curl_plus_commutator_plaquette :
    let M0 := circularConnectionMat4 (coordinateEquiv (rootPlus 0))
    let M1 := circularConnectionMat4 (coordinateEquiv (rootMinus 1))
    let A : FourSpace → Fin 4 → Mat4C := fun z μ =>
      if μ = 0 then (z 1 : ℂ) • M0
      else if μ = 1 then (z 0 : ℂ) • M1
      else 0
    let y : FourSpace := frameBasis 0 + frameBasis 1
    (fderiv ℝ (fun z => A z 1) y (frameBasis 0) -
        fderiv ℝ (fun z => A z 0) y (frameBasis 1) ≠ 0) ∧
    (A y 0 * A y 1 - A y 1 * A y 0 ≠ 0) ∧
    continuumCurvature A y 0 1 ≠ 0 ∧
    0 < continuumPlaquetteAction A y 0 1 ∧
    Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A y 0 1 a - 1))
      (𝓝[≠] 0) (nhds (continuumCurvature A y 0 1)) ∧
    Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A y 1 0 a - 1))
      (𝓝[≠] 0) (nhds (-continuumCurvature A y 0 1)) ∧
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A y 0 1 a)
      (𝓝[≠] 0) (nhds (continuumPlaquetteAction A y 0 1)) := by
  intro M0 M1 A y
  have hCd0 : ContDiff ℝ 2 (fun z : FourSpace => (z 1 : ℂ) • M0) :=
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 4))).contDiff).smul contDiff_const
  have hCd1 : ContDiff ℝ 2 (fun z : FourSpace => (z 0 : ℂ) • M1) :=
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))).contDiff).smul contDiff_const
  have hA_cd : ContDiff ℝ 2 A := by
    refine contDiff_pi.mpr fun μ => ?_
    fin_cases μ
    · exact hCd0
    · exact hCd1
    · exact contDiff_const
    · exact contDiff_const
  have hfderiv0 :
      fderiv ℝ (fun z => A z 1) y (frameBasis 0) = M1 := by
    have hfd : HasFDerivAt (fun z : FourSpace => A z 1)
        ((Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))).smulRight M1) y := by
      have h0 : HasFDerivAt (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4)))
          (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))) y :=
        ContinuousLinearMap.hasFDerivAt _
      exact h0.smul_const M1
    rw [hfd.fderiv]
    simp [frameBasis]
  have hfderiv1 :
      fderiv ℝ (fun z => A z 0) y (frameBasis 1) = M0 := by
    have hfd : HasFDerivAt (fun z : FourSpace => A z 0)
        ((Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 4))).smulRight M0) y := by
      have h1 : HasFDerivAt (Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 4)))
          (Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 4))) y :=
        ContinuousLinearMap.hasFDerivAt _
      exact h1.smul_const M0
    rw [hfd.fderiv]
    simp [frameBasis]
  have hy0 : (y 0 : ℝ) = 1 := by simp [y, frameBasis]
  have hy1 : (y 1 : ℝ) = 1 := by simp [y, frameBasis]
  have hAy0 : A y 0 = M0 := by simp [A, hy1]
  have hAy1 : A y 1 = M1 := by simp [A, hy0]
  have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 1
  have hc6 : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 6
  have hCurl_ne : fderiv ℝ (fun z => A z 1) y (frameBasis 0) -
      fderiv ℝ (fun z => A z 0) y (frameBasis 1) ≠ 0 := by
    rw [hfderiv0, hfderiv1]
    intro h
    have h03 := congrFun (congrFun h 0) 3
    simp [M0, M1, circularConnectionMat4, chiralOffBlock4, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, σ1, σ2, hc1, hc6] at h03
  have hComm_ne : A y 0 * A y 1 - A y 1 * A y 0 ≠ 0 := by
    rw [hAy0, hAy1]
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [M0, M1, circularConnectionMat4, chiralOffBlock4, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, σ1, σ2, hc1, hc6, Complex.ext_iff] at h00
  have hCurv_ne : continuumCurvature A y 0 1 ≠ 0 := by
    dsimp only [continuumCurvature]
    rw [hfderiv0, hfderiv1, hAy0, hAy1]
    intro h
    have h03 := congrFun (congrFun h 0) 3
    simp [M0, M1, circularConnectionMat4, chiralOffBlock4, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, σ1, σ2, hc1, hc6] at h03
  have hAct_pos : 0 < continuumPlaquetteAction A y 0 1 := by
    refine lt_of_le_of_ne (continuumPlaquetteAction_nonneg A y 0 1) ?_
    intro h0
    have h0' : (((continuumCurvature A y 0 1)ᴴ * continuumCurvature A y 0 1).trace).re = 0 :=
      h0.symm
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum] at h0'
    have hsum :
        ∀ i ∈ Finset.univ,
          (∑ j : Fin 4, ((star ((continuumCurvature A y 0 1) j i)) *
            (continuumCurvature A y 0 1) j i).re) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => ?_).mp h0'
      rw [Complex.star_def, Complex.conj_mul']
      simp only [← Complex.ofReal_pow, Complex.ofReal_re]
      positivity
    have hentry : ∀ i j : Fin 4, (continuumCurvature A y 0 1) j i = 0 := by
      intro i j
      have hj := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by
        rw [Complex.star_def, Complex.conj_mul']
        simp only [← Complex.ofReal_pow, Complex.ofReal_re]
        positivity).mp (hsum i (Finset.mem_univ i)) j (Finset.mem_univ j)
      rw [Complex.star_def, Complex.conj_mul'] at hj
      simp only [← Complex.ofReal_pow, Complex.ofReal_re, sq_eq_zero_iff, norm_eq_zero] at hj
      exact hj
    exact hCurv_ne (Matrix.ext fun r s => hentry s r)
  have hRev := tendsto_wilsonPlaquette_curvature A y 1 0 hA_cd
  rw [continuumCurvature_antisymm A y 0 1] at hRev
  exact ⟨hCurl_ne, hComm_ne, hCurv_ne, hAct_pos,
    tendsto_wilsonPlaquette_curvature A y 0 1 hA_cd, hRev,
    tendsto_wilsonPlaquetteAction A y 0 1 hA_cd⟩

/-- T5-M2-03: Combined nonzero directional derivative + nonzero commutator in
`latticeCovariantDiff`, plus tracelessness of `continuumCurvature` on `witnessCircularField`. -/
theorem t5_m2_03_varying_covariant_diff_both_terms_and_traceless_curv :
    let y : FourSpace := frameBasis 0
    let A : FourSpace → Fin 4 → Mat4C :=
      fun z μ => circularConnectionMat4 (witnessCircularField z μ)
    let Φ : FourSpace → Mat4C := fun z => (z 0 : ℂ) • chiralProjMat4
    fderiv ℝ Φ y (frameBasis 0) ≠ 0 ∧
    A y 0 * Φ y - Φ y * A y 0 ≠ 0 ∧
    continuumCovariantDeriv A Φ y 0 ≠ 0 ∧
    Filter.Tendsto (fun a : ℝ => latticeCovariantDiff A Φ y 0 a)
      (𝓝[≠] 0) (nhds (continuumCovariantDeriv A Φ y 0)) ∧
    (continuumCurvature A y 0 1).trace = 0 := by
  intro y A Φ
  have hDiff : DifferentiableAt ℝ Φ y := by fun_prop
  have hFderiv : fderiv ℝ Φ y (frameBasis 0) = chiralProjMat4 := by
    have h0 : HasFDerivAt (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4)))
        (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))) y :=
      ContinuousLinearMap.hasFDerivAt _
    have hfd : HasFDerivAt Φ
        ((Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))).smulRight chiralProjMat4) y :=
      h0.smul_const chiralProjMat4
    rw [hfd.fderiv]
    simp [frameBasis]
  have hDeriv_ne : fderiv ℝ Φ y (frameBasis 0) ≠ 0 := by
    rw [hFderiv]
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [chiralProjMat4, chiralProj4, chiralDiagBlock4] at h00
  have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
    simpa [frame] using coordinateEquiv_apply_frame 1
  have hy0 : (y 0 : ℝ) = 1 := by simp [y, frameBasis]
  have hComm_ne : A y 0 * Φ y - Φ y * A y 0 ≠ 0 := by
    intro h
    have h03 := congrFun (congrFun h 0) 3
    simp [A, Φ, hy0, witnessCircularField, circularConnectionMat4, chiralOffBlock4, weylUpperMat,
      pauliSolder2x2, solder, σ1, hc1, chiralProjMat4, chiralProj4, chiralDiagBlock4] at h03
  have hCov_ne : continuumCovariantDeriv A Φ y 0 ≠ 0 := by
    unfold continuumCovariantDeriv
    rw [hFderiv]
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [A, Φ, hy0, witnessCircularField, circularConnectionMat4, chiralOffBlock4, weylUpperMat,
      pauliSolder2x2, solder, σ1, hc1, chiralProjMat4, chiralProj4, chiralDiagBlock4] at h00
  have hTrace0 : (continuumCurvature A y 0 1).trace = 0 := by
    have hDeriv0 : fderiv ℝ (fun z => A z 1) y = 0 := fderiv_const_apply (A y 1)
    have hDeriv1 : fderiv ℝ (fun z => A z 0) y = 0 := fderiv_const_apply (A y 0)
    simp only [continuumCurvature, hDeriv0, hDeriv1, zero_apply,
      zero_add, Matrix.trace_sub, Matrix.trace_mul_comm (A y 0) (A y 1), sub_self]
  exact ⟨hDeriv_ne, hComm_ne, hCov_ne, tendsto_latticeCovariantDiff A Φ y 0 hDiff, hTrace0⟩

/-- T5-Cross-01 (M2 ↔ M3): Wilson plaquette `a → 0` converges to `ymCurvature` for both
`circularGaugeForm` and the spacetime-varying `circularMinkowskiWaveForm (fun t => t ^ 2 + 1)`. -/
theorem t5_cross_m2_m3_wave_and_self_dual_plaquette_limit (y : FourSpace) :
    let A_sd : FourSpace → Fin 4 → Mat4C := fun z ρ => circularGaugeForm z ![frameBasis ρ]
    let f : ℝ → ℝ := fun t => t ^ 2 + 1
    let A_wave : FourSpace → Fin 4 → Mat4C :=
      fun z ρ => circularMinkowskiWaveForm f z ![frameBasis ρ]
    Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A_sd y 0 2 a - 1))
      (𝓝[≠] 0) (nhds (ymCurvature circularGaugeForm y ![frameBasis 0, frameBasis 2])) ∧
    Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A_sd y 0 2 a)
      (𝓝[≠] 0) (nhds (continuumPlaquetteAction A_sd y 0 2)) ∧
    YangMillsPDEMinkowski (circularMinkowskiWaveForm f) ∧
    ymCurvature (circularMinkowskiWaveForm f) ≠ 0 ∧
    Filter.Tendsto (fun a : ℝ => (a ^ 2)⁻¹ • (wilsonPlaquette A_wave y 0 2 a - 1))
      (𝓝[≠] 0)
      (nhds (ymCurvature (circularMinkowskiWaveForm f) y ![frameBasis 0, frameBasis 2])) := by
  intro A_sd f A_wave
  have hsd_cd : ContDiff ℝ 2 A_sd := by
    have heq : A_sd = fun _ ρ => circularGaugeForm 0 ![frameBasis ρ] := rfl
    rw [heq]; exact contDiff_const
  have hf_cd : ContDiff ℝ 2 f := by
    dsimp [f]; exact (contDiff_id.pow 2).add contDiff_const
  have hf0 : f 0 ≠ 0 := by simp [f]
  have hwave_form_cd : ContDiff ℝ 2 (circularMinkowskiWaveForm f) := by
    let lc : FourSpace →L[ℝ] ℝ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun x => x 0 - x 1
          map_add' := fun x y => by simp; ring
          map_smul' := fun c x => by simp; ring }
    have hlc : ContDiff ℝ 2 (fun x : FourSpace => f (lc x)) := hf_cd.comp lc.contDiff
    exact (hlc.smul contDiff_const).add contDiff_const
  have hwave_cd : ContDiff ℝ 2 A_wave := by
    refine contDiff_pi.mpr fun ρ => ?_
    let evρ : (FourSpace [⋀^Fin 1]→L[ℝ] Mat4C) →L[ℝ] Mat4C :=
      ContinuousAlternatingMap.apply ℝ FourSpace Mat4C ![frameBasis ρ]
    exact (evρ.contDiff (n := (2 : WithTop ℕ∞))).comp hwave_form_cd
  have hEq_sd :
      continuumCurvature A_sd y 0 2 =
        ymCurvature circularGaugeForm y ![frameBasis 0, frameBasis 2] := by
    have hsd_diff : Differentiable ℝ circularGaugeForm :=
      (circularGaugeForm_contDiff.of_le (by simp : (2 : WithTop ℕ∞) ≤ ⊤)).differentiable
        (by norm_num)
    rw [ymCurvature_apply_two _ hsd_diff y (frameBasis 0) (frameBasis 2)]
    unfold continuumCurvature
    dsimp only [A_sd]
    have h0 : (fun _ : Fin 1 => frameBasis 0) = ![frameBasis 0] := by funext i; fin_cases i; rfl
    have h2 : (fun _ : Fin 1 => frameBasis 2) = ![frameBasis 2] := by funext i; fin_cases i; rfl
    rw [h0, h2]
  have hEq_wave :
      continuumCurvature A_wave y 0 2 =
        ymCurvature (circularMinkowskiWaveForm f) y ![frameBasis 0, frameBasis 2] := by
    rw [ymCurvature_apply_two _ (hwave_form_cd.differentiable (by norm_num))
      y (frameBasis 0) (frameBasis 2)]
    unfold continuumCurvature
    dsimp only [A_wave]
    have h0 : (fun _ : Fin 1 => frameBasis 0) = ![frameBasis 0] := by funext i; fin_cases i; rfl
    have h2 : (fun _ : Fin 1 => frameBasis 2) = ![frameBasis 2] := by funext i; fin_cases i; rfl
    rw [h0, h2]
  refine ⟨?_, tendsto_wilsonPlaquetteAction A_sd y 0 2 hsd_cd,
    circularMinkowskiWaveForm_solves_yangMillsPDEMinkowski hf_cd,
    circularMinkowskiWaveForm_ymCurvature_ne_zero hf_cd hf0, ?_⟩
  · simpa [hEq_sd] using tendsto_wilsonPlaquette_curvature A_sd y 0 2 hsd_cd
  · simpa [hEq_wave] using tendsto_wilsonPlaquette_curvature A_wave y 0 2 hwave_cd

/-- T5-Cross-02 (M1 ↔ M3 ↔ Baseline): `circularSelfDualExtOmega` is a nonzero homogeneous 1-form
rejecting all `d² = 0` differentials, plus uncovered Baseline Krein/chirality/Clifford/tetraktys
bridges. -/
theorem t5_cross_m1_m3_baseline_bridges
    (t x1 x2 x3 tau y1 y2 y3 : ℝ)
    (X : DoubledMinkowskiCircularChiralYangMillsBridge.CanonicalZorn) (x y : Coordinate)
    (d : Module.End ℂ (ExteriorAlgebra ℂ ChiralFiber)) (hd2 : d.comp d = 0) :
    MatrixIsHomogeneous 1 (circularGaugeConnection4 circularSelfDualExtOmega) ∧
    circularGaugeConnection4 circularSelfDualExtOmega ≠ 0 ∧
    matrixExteriorDerivative d (circularGaugeConnection4 circularSelfDualExtOmega) ≠
      peirceGradingDeriv (chiralExteriorProj4 ChiralFiber)
        (circularGaugeConnection4 circularSelfDualExtOmega) ∧
    (let v := symmSection t x1 x2 x3 + antiSection tau y1 y2 y3
     (1 / 2 : ℝ) * chiralKreinForm (E := FourSpace)
         (circularCoordToKreinFrame v) (circularCoordToKreinFrame v) =
       (t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) - (tau ^ 2 - (y1 ^ 2 + y2 ^ 2 + y3 ^ 2))) ∧
    zornToKreinFrame (leftMultiplication uPlus X) =
      leftChiralProjector (E := FourSpace) (zornToKreinFrame X) ∧
    zornToKreinFrame (leftMultiplication uMinus X) =
      rightChiralProjector (E := FourSpace) (zornToKreinFrame X) ∧
    zornToKreinFrame (leftMultiplication lUnit X) = chirality (zornToKreinFrame X) ∧
    circularCoordToKreinFrame (signedKappa x) = sheetFlip (circularCoordToKreinFrame x) ∧
    weylUpperMat x * weylLowerMat x - weylLowerMat x * weylUpperMat x =
      (-2 * Complex.I) • solder (0, (chiralVorticityVec x 0 : ℂ),
        (chiralVorticityVec x 1 : ℂ), (chiralVorticityVec x 2 : ℂ)) ∧
    weylUpperMat (symmSection t x1 x2 x3) * weylLowerMat (symmSection t x1 x2 x3) =
      (((t ^ 2 - (x1 ^ 2 + x2 ^ 2 + x3 ^ 2)) : ℝ) : ℂ) • 1 ∧
    (circularCurvatureMat4 x).trace = 4 * (wittNorm x : ℂ) ∧
    (circularCurvatureMat4 x * circularCurvatureMat4 x).trace =
      ((4 * (wittNorm x ^ 2 + normSq3 (chiralBoostVec x) -
        normSq3 (chiralVorticityVec x)) : ℝ) : ℂ) ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.genPhi
        (firstSheetProjection (W := Fin 2 → ℂ))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords x))
        (InfoGeometry.Clifford.reconstruct_causal (circularCausalCoords y)) =
      !![0, Matrix.toLin' (weylUpperMat x); Matrix.toLin' (weylLowerMat y), 0] := by
  have hHom : MatrixIsHomogeneous 1 (circularGaugeConnection4 circularSelfDualExtOmega) := by
    have hω_hom : ∀ m : Fin 8, IsHomogeneousExteriorDegree 1 (circularSelfDualExtOmega m) := by
      intro m
      refine (homogeneous_one_iff_exists_generator _).mpr ?_
      refine ⟨fun μ => ((circularSelfDualCoords μ m : ℝ) : ℂ), ?_⟩
      have hv : (fun μ : Fin 4 => ((circularSelfDualCoords μ m : ℝ) : ℂ)) =
          ∑ μ : Fin 4, ((circularSelfDualCoords μ m : ℝ) : ℂ) • Pi.single μ (1 : ℂ) := by
        ext ν
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hv]
      rw [map_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [LinearMap.map_smul]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, weylLowerExt,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact Submodule.zero_mem _
    · exact Submodule.zero_mem _
    · exact Submodule.add_mem _ (hω_hom 0) (hω_hom 3)
    · exact Submodule.sub_mem _ (hω_hom 1) (Submodule.smul_mem _ Complex.I (hω_hom 2))
    · exact Submodule.zero_mem _
    · exact Submodule.zero_mem _
    · exact Submodule.add_mem _ (hω_hom 1) (Submodule.smul_mem _ Complex.I (hω_hom 2))
    · exact Submodule.sub_mem _ (hω_hom 0) (hω_hom 3)
    · exact Submodule.sub_mem _ (hω_hom 4) (hω_hom 7)
    · exact Submodule.add_mem _ (Submodule.neg_mem _ (hω_hom 5))
        (Submodule.smul_mem _ Complex.I (hω_hom 6))
    · exact Submodule.zero_mem _
    · exact Submodule.zero_mem _
    · exact Submodule.sub_mem _ (Submodule.neg_mem _ (hω_hom 5))
        (Submodule.smul_mem _ Complex.I (hω_hom 6))
    · exact Submodule.add_mem _ (hω_hom 4) (hω_hom 7)
    · exact Submodule.zero_mem _
    · exact Submodule.zero_mem _
  have hNe : circularGaugeConnection4 circularSelfDualExtOmega ≠ 0 := by
    intro h
    have h03 := congrFun (congrFun h 0) 3
    have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 1
    have hc2 : coordinateEquiv (rootPlus 1) = Pi.single 2 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 2
    have hc5 : coordinateEquiv (rootMinus 0) = Pi.single 5 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 5
    have hc6 : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 6
    have hω1 : circularSelfDualExtOmega 1 = ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) := by
      simp [circularSelfDualExtOmega, circularSelfDualCoords, hc1, hc2, hc5, hc6, Fin.sum_univ_four]
    have hω2 : circularSelfDualExtOmega 2 = ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) := by
      simp [circularSelfDualExtOmega, circularSelfDualCoords, hc1, hc2, hc5, hc6, Fin.sum_univ_four]
    have h03' :
        ExteriorAlgebra.ι ℂ (Pi.single (0 : Fin 4) (1 : ℂ) -
          Complex.I • Pi.single (1 : Fin 4) (1 : ℂ)) = 0 := by
      simp only [circularGaugeConnection4, chiralOffBlock4, weylUpperExt, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.zero_apply, hω1, hω2] at h03
      simpa [map_sub, map_smul] using h03
    have hvec := (ExteriorAlgebra.ι_eq_zero_iff (R := ℂ) _).mp h03'
    have h0 := congrFun hvec 0
    simp at h0
  refine ⟨hHom, hNe, ?_, (doubledMinkowski_krein_pauli_soldering_bridge t x1 x2 x3 tau y1 y2 y3).1,
    zornToKreinFrame_intertwines_uPlus X, zornToKreinFrame_intertwines_uMinus X,
    zornToKreinFrame_intertwines_chirality X, circularCoordToKreinFrame_intertwines_sheetFlip x,
    weylChannel_commutator_eq_vorticity x, (weylChannel_symmSection_clifford_closure t x1 x2 x3).1,
    (circularCurvatureMat4_trace x).1, circularCurvatureMat4_square_trace x,
    (circularSheet_tetraktys_table x y).1⟩
  intro hcompat
  exact hNe (circularGaugeConnection4_sq_zero_eigencondition_forces_zero d _ hd2 hcompat)

/-! ## Tier 5: Adversarial & Full-Surface Verification Probes (M3) -/

private lemma t5_cir_block_0 :
    circularConnectionMat4 (circularSelfDualCoords 0) = chiralOffBlock4 σ1 0 := by
  ext i j
  have hc : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 1
  fin_cases i <;> fin_cases j <;>
    simp [circularSelfDualCoords, hc, circularConnectionMat4, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]

private lemma t5_cir_block_1 :
    circularConnectionMat4 (circularSelfDualCoords 1) = chiralOffBlock4 σ2 0 := by
  ext i j
  have hc : coordinateEquiv (rootPlus 1) = Pi.single 2 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 2
  fin_cases i <;> fin_cases j <;>
    simp [circularSelfDualCoords, hc, circularConnectionMat4, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]

private lemma t5_cir_block_2 :
    circularConnectionMat4 (circularSelfDualCoords 2) = chiralOffBlock4 0 (-σ2) := by
  ext i j
  have hc : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 6
  fin_cases i <;> fin_cases j <;>
    simp [circularSelfDualCoords, hc, circularConnectionMat4, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]

private lemma t5_cir_block_3 :
    circularConnectionMat4 (circularSelfDualCoords 3) = chiralOffBlock4 0 (-σ1) := by
  ext i j
  have hc : coordinateEquiv (rootMinus 0) = Pi.single 5 1 := by
    simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 5
  fin_cases i <;> fin_cases j <;>
    simp [circularSelfDualCoords, hc, circularConnectionMat4, weylUpperMat, weylLowerMat,
      pauliSolder2x2, solder, chiralOffBlock4, σ0, σ1, σ2, σ3]

private lemma t5_chiralOffBlock4_mul (U₁ L₁ U₂ L₂ : Matrix (Fin 2) (Fin 2) ℂ) :
    chiralOffBlock4 U₁ L₁ * chiralOffBlock4 U₂ L₂ =
      chiralDiagBlock4 (U₁ * L₂) (L₁ * U₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralOffBlock4, chiralDiagBlock4, Matrix.mul_apply, Fin.sum_univ_four]

private lemma t5_frameBasis_apply (μ ν : Fin 4) :
    frameBasis μ ν = if μ = ν then 1 else 0 := by
  fin_cases μ <;> fin_cases ν <;> simp [frameBasis]

private lemma t5_extDeriv_const {k : ℕ} (c : FourSpace [⋀^Fin k]→L[ℝ] Mat4C) (x : FourSpace) :
    @extDeriv ℝ FourSpace Mat4C _ _ _ Matrix.normedAddCommGroup Matrix.normedSpace k
      (fun _ : FourSpace => c) x = 0 := by
  apply ContinuousAlternatingMap.ext
  intro v
  have hd : @extDeriv ℝ FourSpace Mat4C _ _ _ Matrix.normedAddCommGroup Matrix.normedSpace k
      (fun _ : FourSpace => c) x v =
      ∑ i : Fin (k + 1), (-1) ^ i.val •
        fderiv ℝ (fun _ : FourSpace => c (i.removeNth v)) x (v i) :=
    @extDeriv_apply ℝ FourSpace Mat4C _ _ _ Matrix.normedAddCommGroup Matrix.normedSpace k
      (fun _ : FourSpace => c) x (differentiableAt_const c) v
  rw [hd]
  simp [fderiv_const_apply]

private lemma t5_covExtDeriv_const {k : ℕ} (A : Mat4CForm 1)
    (c : FourSpace [⋀^Fin k]→L[ℝ] Mat4C) (x : FourSpace) :
    covExtDeriv A (fun _ => c) x = wedgeComm A (fun _ => c) x := by
  have hsub : covExtDeriv A (fun _ => c) x - wedgeComm A (fun _ => c) x =
      @extDeriv ℝ FourSpace Mat4C _ _ _ Matrix.normedAddCommGroup Matrix.normedSpace k
        (fun _ : FourSpace => c) x := by
    dsimp [covExtDeriv]
    rw [add_sub_cancel_right]
    rfl
  rw [t5_extDeriv_const] at hsub
  exact sub_eq_zero.mp hsub

private lemma t5_ymCurvature_const (A₀ : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C) (x : FourSpace) :
    ymCurvature (fun _ => A₀) x = halfWedgeSelf (fun _ => A₀) x := by
  have hsub : ymCurvature (fun _ => A₀) x - halfWedgeSelf (fun _ => A₀) x =
      @extDeriv ℝ FourSpace Mat4C _ _ _ Matrix.normedAddCommGroup Matrix.normedSpace 1
        (fun _ : FourSpace => A₀) x := by
    dsimp [ymCurvature]
    rw [add_sub_cancel_right]
    rfl
  rw [t5_extDeriv_const] at hsub
  exact sub_eq_zero.mp hsub

/-- T5-01: Origin-vanishing wave profile (`Real.sin`) solves `YangMillsPDEMinkowski` with nonzero
curvature off the light cone. -/
theorem t5_01_minkowski_wave_vanish_origin_and_nonabelian_pde :
    let fSin : ℝ → ℝ := Real.sin
    let fCos : ℝ → ℝ := Real.cos
    fSin 0 = 0 ∧
    YangMillsPDEMinkowski (circularMinkowskiWaveForm fSin) ∧
    ymCurvature (circularMinkowskiWaveForm fSin) (frameBasis 0) ![frameBasis 0, frameBasis 2] ≠
      0 ∧
    YangMillsPDEMinkowski (circularMinkowskiWaveForm fCos) ∧
    ymCurvature (circularMinkowskiWaveForm fCos) ≠ 0 ∧
    waveDirForm ![frameBasis 0] = circularConnectionMat4 (circularSelfDualCoords 0) ∧
    waveSpatialForm ![frameBasis 2] = circularConnectionMat4 (circularSelfDualCoords 3) := by
  intro fSin fCos
  have hSinCont : ContDiff ℝ 2 fSin := Real.contDiff_sin.of_le le_top
  have hCosCont : ContDiff ℝ 2 fCos := Real.contDiff_cos.of_le le_top
  have hDiffWave : Differentiable ℝ (circularMinkowskiWaveForm fSin) := by
    have hSinDiff : Differentiable ℝ fSin := hSinCont.differentiable (by norm_num)
    have hLC : Differentiable ℝ (fun y : FourSpace => fSin (y 0 - y 1)) := by
      let L0 : FourSpace →L[ℝ] ℝ :=
        EuclideanSpace.proj (0 : Fin 4) - EuclideanSpace.proj (1 : Fin 4)
      exact hSinDiff.comp L0.differentiable
    have hsm : Differentiable ℝ (fun y : FourSpace => fSin (y 0 - y 1) • waveDirForm) :=
      hLC.smul_const waveDirForm
    exact hsm.fun_add (differentiable_const waveSpatialForm)
  have hDir0 : waveDirForm ![frameBasis 0] =
      circularConnectionMat4 (circularSelfDualCoords 0) := by
    have h : waveDirForm ![frameBasis 0] =
        ((frameBasis 0 0 - frameBasis 0 1 : ℝ) : ℂ) •
          circularConnectionMat4 (circularSelfDualCoords 0) :=
      rfl
    rw [h, t5_frameBasis_apply, t5_frameBasis_apply]
    simp [circularSelfDualCoords]
  have hSp2 : waveSpatialForm ![frameBasis 2] =
      circularConnectionMat4 (circularSelfDualCoords 3) := by
    have h : waveSpatialForm ![frameBasis 2] =
        (frameBasis 2 2 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 0)) +
        (frameBasis 2 3 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 1)) :=
      rfl
    rw [h, t5_frameBasis_apply, t5_frameBasis_apply]
    simp [circularSelfDualCoords]
  have hF02_sin :
      ymCurvature (circularMinkowskiWaveForm fSin) (frameBasis 0) ![frameBasis 0, frameBasis 2] ≠
        0 := by
    rw [ymCurvature_apply_two _ hDiffWave]
    have hC2 : (fun y : FourSpace => circularMinkowskiWaveForm fSin y (fun _ => frameBasis 2)) =
        fun _ => circularConnectionMat4 (circularSelfDualCoords 3) := by
      funext y
      have hd2 : waveDirForm (fun _ => frameBasis 2) = 0 := by
        have h : waveDirForm (fun _ => frameBasis 2) =
            ((frameBasis 2 0 - frameBasis 2 1 : ℝ) : ℂ) •
              circularConnectionMat4 (coordinateEquiv (rootPlus 0)) :=
          rfl
        rw [h, t5_frameBasis_apply, t5_frameBasis_apply]
        simp
      have hs2 : waveSpatialForm (fun _ => frameBasis 2) =
          circularConnectionMat4 (circularSelfDualCoords 3) :=
        hSp2
      change fSin (y 0 - y 1) • waveDirForm (fun _ => frameBasis 2) +
        waveSpatialForm (fun _ => frameBasis 2) = _
      rw [hd2, hs2, smul_zero, zero_add]
    have hC0 : (fun y : FourSpace => circularMinkowskiWaveForm fSin y (fun _ => frameBasis 0)) =
        fun y => fSin (y 0 - y 1) • circularConnectionMat4 (circularSelfDualCoords 0) := by
      funext y
      have hs0 : waveSpatialForm (fun _ => frameBasis 0) = 0 := by
        have h : waveSpatialForm (fun _ => frameBasis 0) =
            (frameBasis 0 2 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 0)) +
            (frameBasis 0 3 : ℂ) • circularConnectionMat4 (coordinateEquiv (rootMinus 1)) :=
          rfl
        rw [h, t5_frameBasis_apply, t5_frameBasis_apply]
        simp
      have hd0 : waveDirForm (fun _ => frameBasis 0) =
          circularConnectionMat4 (circularSelfDualCoords 0) :=
        hDir0
      change fSin (y 0 - y 1) • waveDirForm (fun _ => frameBasis 0) +
        waveSpatialForm (fun _ => frameBasis 0) = _
      rw [hd0, hs0, add_zero]
    have hfd2 : fderiv ℝ (fun y => circularMinkowskiWaveForm fSin y (fun _ => frameBasis 2))
        (frameBasis 0) (frameBasis 0) = 0 := by
      rw [hC2]
      simp [fderiv_const_apply]
    have hfd0 : fderiv ℝ (fun y => circularMinkowskiWaveForm fSin y (fun _ => frameBasis 0))
        (frameBasis 0) (frameBasis 2) = 0 := by
      let L : FourSpace →L[ℝ] ℝ :=
        EuclideanSpace.proj (0 : Fin 4) - EuclideanSpace.proj (1 : Fin 4)
      have hfSinDeriv : HasDerivAt fSin (Real.cos (L (frameBasis 0))) (L (frameBasis 0)) :=
        Real.hasDerivAt_sin (L (frameBasis 0))
      have hComp : HasFDerivAt (fun y : FourSpace => fSin (L y))
          (Real.cos (L (frameBasis 0)) • L) (frameBasis 0) :=
        hfSinDeriv.comp_hasFDerivAt (frameBasis 0) L.hasFDerivAt
      have hSm := hComp.smul_const (circularConnectionMat4 (circularSelfDualCoords 0))
      have hC0L : (fun y : FourSpace => circularMinkowskiWaveForm fSin y (fun _ => frameBasis 0)) =
          fun y => fSin (L y) • circularConnectionMat4 (circularSelfDualCoords 0) :=
        hC0
      have hfd_eq := congrArg (fun M : FourSpace →L[ℝ] Mat4C => M (frameBasis 2)) hSm.fderiv
      rw [hC0L]
      have hL2 : L (frameBasis 2) = 0 := by
        change frameBasis 2 0 - frameBasis 2 1 = 0
        rw [t5_frameBasis_apply, t5_frameBasis_apply]
        norm_num
      have hSm0 : ((Real.cos (L (frameBasis 0)) • L).smulRight
          (circularConnectionMat4 (circularSelfDualCoords 0))) (frameBasis 2) = 0 := by
        simp [ContinuousLinearMap.smulRight_apply, hL2]
      exact hfd_eq.trans hSm0
    have hEval0 : circularMinkowskiWaveForm fSin (frameBasis 0) (fun _ => frameBasis 0) =
        fSin 1 • circularConnectionMat4 (circularSelfDualCoords 0) := by
      rw [congrFun hC0 (frameBasis 0), t5_frameBasis_apply, t5_frameBasis_apply]
      norm_num
    have hEval2 : circularMinkowskiWaveForm fSin (frameBasis 0) (fun _ => frameBasis 2) =
        circularConnectionMat4 (circularSelfDualCoords 3) :=
      congrFun hC2 (frameBasis 0)
    rw [hfd2, hfd0, sub_self, zero_add, hEval0, hEval2, t5_cir_block_0, t5_cir_block_3]
    intro hzero
    have h00 := congrFun (congrFun hzero 0) 0
    have hSin1_ne : fSin 1 ≠ 0 := by
      have hpi : (1 : ℝ) < Real.pi := lt_of_lt_of_le (by norm_num) Real.two_le_pi
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi zero_lt_one hpi)
    have hsmmul :
        (fSin 1 • chiralOffBlock4 σ1 0) * chiralOffBlock4 0 (-σ1) -
          chiralOffBlock4 0 (-σ1) * (fSin 1 • chiralOffBlock4 σ1 0) =
          fSin 1 • (chiralOffBlock4 σ1 0 * chiralOffBlock4 0 (-σ1) -
            chiralOffBlock4 0 (-σ1) * chiralOffBlock4 σ1 0) := by
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
    rw [hsmmul, t5_chiralOffBlock4_mul, t5_chiralOffBlock4_mul] at h00
    simp only [Matrix.smul_apply, Matrix.sub_apply, chiralDiagBlock4, Matrix.zero_apply,
      Complex.real_smul] at h00
    have h00_val : -(↑(fSin 1) : ℂ) * (2 : ℂ) = 0 := by
      simpa [σ1, Matrix.mul_apply, Fin.sum_univ_two] using h00
    have hre := congrArg Complex.re h00_val
    simp at hre
    exact hSin1_ne hre
  exact ⟨Real.sin_zero, circularMinkowskiWaveForm_solves_yangMillsPDEMinkowski hSinCont,
    hF02_sin, circularMinkowskiWaveForm_solves_yangMillsPDEMinkowski hCosCont,
    circularMinkowskiWaveForm_ymCurvature_ne_zero hCosCont (by simp [fCos]),
    hDir0, hSp2⟩

/-- T5-02: Euclidean `YangMillsPDE` vs Lorentzian `YangMillsPDEMinkowski` solution separation. -/
theorem t5_02_euclidean_vs_minkowski_ym_pde_separation :
    hodgeStar4Eucl (hodgeStar4Eucl (ymCurvature circularGaugeForm)) =
      ymCurvature circularGaugeForm ∧
    hodgeStar4Minkowski (hodgeStar4Minkowski (ymCurvature circularGaugeForm)) =
      -(ymCurvature circularGaugeForm) ∧
    ContDiff ℝ ⊤ (hodgeStar4Eucl (ymCurvature circularGaugeForm)) ∧
    ContDiff ℝ ⊤ (hodgeStar4Minkowski (ymCurvature circularGaugeForm)) ∧
    ¬ YangMillsPDEMinkowski circularGaugeForm ∧
    ¬ YangMillsPDE (circularMinkowskiWaveForm (fun _ => 1)) := by
  have hDiffCirc : Differentiable ℝ circularGaugeForm :=
    circularGaugeForm_contDiff.differentiable (by simp)
  have hCircEq : ymCurvature circularGaugeForm = fun _ => halfWedgeSelf circularGaugeForm 0 := by
    funext x
    have hc : circularGaugeForm = fun _ => circularGaugeOneForm := rfl
    rw [hc, t5_ymCurvature_const]
    rfl
  have hymCont : ContDiff ℝ ⊤ (ymCurvature circularGaugeForm) := by
    rw [hCircEq]
    exact contDiff_const
  refine ⟨hodgeStar4Eucl_involutive _, hodgeStar4Minkowski_sq_neg _,
    hodgeStar4Eucl_contDiff hymCont, hodgeStar4Minkowski_contDiff hymCont, ?_, ?_⟩
  · intro hMink
    have hStarConst :
        hodgeStar4Minkowski (ymCurvature circularGaugeForm) =
          fun _ => hodgeStar4MinkowskiMap (ymCurvature circularGaugeForm 0) := by
      funext y
      have hy : ymCurvature circularGaugeForm y = ymCurvature circularGaugeForm 0 := by
        rw [hCircEq]
      simp [hodgeStar4Minkowski, hy]
    have hW0 :
        wedgeComm circularGaugeForm (hodgeStar4Minkowski (ymCurvature circularGaugeForm)) 0
          ![frameBasis 0, frameBasis 1, frameBasis 2] = 0 := by
      have h012 := congrArg (fun g : Mat4CForm 3 =>
        g 0 ![frameBasis 0, frameBasis 1, frameBasis 2]) hMink
      change covExtDeriv circularGaugeForm
          (hodgeStar4Minkowski (ymCurvature circularGaugeForm)) 0
          ![frameBasis 0, frameBasis 1, frameBasis 2] = 0 at h012
      rw [hStarConst] at h012 ⊢
      rw [t5_covExtDeriv_const] at h012
      exact h012
    dsimp [wedgeComm] at hW0
    rw [wedgeCommAt_apply, Fin.sum_univ_three] at hW0
    have hr0 : (0 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 1, frameBasis 2] := by
      funext i; fin_cases i <;> rfl
    have hr1 : (1 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 0, frameBasis 2] := by
      funext i; fin_cases i <;> rfl
    have hr2 : (2 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 0, frameBasis 1] := by
      funext i; fin_cases i <;> rfl
    have hv0 : ![frameBasis 0, frameBasis 1, frameBasis 2] 0 = frameBasis 0 := rfl
    have hv1 : ![frameBasis 0, frameBasis 1, frameBasis 2] 1 = frameBasis 1 := rfl
    have hv2 : ![frameBasis 0, frameBasis 1, frameBasis 2] 2 = frameBasis 2 := rfl
    rw [hr0, hr1, hr2, hv0, hv1, hv2] at hW0
    have hA : ∀ μ : Fin 4, circularGaugeForm 0 (fun _ => frameBasis μ) =
        circularConnectionMat4 (circularSelfDualCoords μ) := by
      intro μ
      have ha : (fun _ : Fin 1 => frameBasis μ) = ![frameBasis μ] := by
        funext i; fin_cases i; rfl
      rw [ha, circularGaugeForm_apply_basis]
    have hF_eval : ∀ μ ν : Fin 4,
        ymCurvature circularGaugeForm 0 ![frameBasis μ, frameBasis ν] =
          circularConnectionMat4 (circularSelfDualCoords μ) *
            circularConnectionMat4 (circularSelfDualCoords ν) -
          circularConnectionMat4 (circularSelfDualCoords ν) *
            circularConnectionMat4 (circularSelfDualCoords μ) := by
      intro μ ν
      rw [ymCurvature_apply_two _ hDiffCirc]
      have hfc : ∀ w, fderiv ℝ (fun y => circularGaugeForm y (fun _ => w)) 0 = 0 := by
        intro w
        have hc : (fun y => circularGaugeForm y (fun _ => w)) =
            fun _ => circularGaugeOneForm (fun _ => w) := rfl
        rw [hc]
        simp [fderiv_const_apply]
      rw [hfc, hfc, hA, hA]
      simp
    simp only [hodgeStar4Minkowski, hodgeStar4MinkowskiMap_basis_12,
      hodgeStar4MinkowskiMap_basis_02, hodgeStar4MinkowskiMap_basis_01, hA] at hW0
    rw [hF_eval 0 3, hF_eval 3 1, hF_eval 2 3] at hW0
    rw [t5_cir_block_0, t5_cir_block_1, t5_cir_block_2, t5_cir_block_3] at hW0
    simp only [t5_chiralOffBlock4_mul, mat4CCommCLM_apply, map_neg, neg_smul, one_zsmul,
      Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, pow_two] at hW0
    have h03 := congrFun (congrFun hW0 0) 3
    simp [chiralOffBlock4, chiralDiagBlock4, Matrix.mul_apply,
      σ1, σ2, Fin.sum_univ_two] at h03
  · intro hEucl
    let waveConst : Mat4CForm 1 := circularMinkowskiWaveForm (fun _ => 1)
    let waveConst0 : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C := waveConst 0
    have hEqW : waveConst = fun _ => waveConst0 := by
      funext x
      simp [waveConst, waveConst0, circularMinkowskiWaveForm]
    have hDiffW : Differentiable ℝ waveConst := by
      rw [hEqW]
      exact differentiable_const _
    have hCurvEq : ymCurvature waveConst = fun _ => halfWedgeSelf waveConst 0 := by
      funext y
      rw [hEqW, t5_ymCurvature_const]
      rfl
    have hStarConst :
        hodgeStar4Eucl (ymCurvature waveConst) =
          fun _ => hodgeStar4EuclMap (ymCurvature waveConst 0) := by
      funext y
      have hy : ymCurvature waveConst y = ymCurvature waveConst 0 := by
        rw [hCurvEq]
      simp [hodgeStar4Eucl, hy]
    have hW0 :
        wedgeComm waveConst (hodgeStar4Eucl (ymCurvature waveConst)) 0
          ![frameBasis 0, frameBasis 1, frameBasis 2] = 0 := by
      have h012 := congrArg (fun g : Mat4CForm 3 =>
        g 0 ![frameBasis 0, frameBasis 1, frameBasis 2]) hEucl
      change covExtDeriv waveConst (hodgeStar4Eucl (ymCurvature waveConst)) 0
          ![frameBasis 0, frameBasis 1, frameBasis 2] = 0 at h012
      rw [hStarConst] at h012 ⊢
      rw [t5_covExtDeriv_const] at h012
      exact h012
    dsimp [wedgeComm] at hW0
    rw [wedgeCommAt_apply, Fin.sum_univ_three] at hW0
    have hr0 : (0 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 1, frameBasis 2] := by
      funext i; fin_cases i <;> rfl
    have hr1 : (1 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 0, frameBasis 2] := by
      funext i; fin_cases i <;> rfl
    have hr2 : (2 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 0, frameBasis 1] := by
      funext i; fin_cases i <;> rfl
    have hv0 : ![frameBasis 0, frameBasis 1, frameBasis 2] 0 = frameBasis 0 := rfl
    have hv1 : ![frameBasis 0, frameBasis 1, frameBasis 2] 1 = frameBasis 1 := rfl
    have hv2 : ![frameBasis 0, frameBasis 1, frameBasis 2] 2 = frameBasis 2 := rfl
    rw [hr0, hr1, hr2, hv0, hv1, hv2] at hW0
    have hW_basis : ∀ μ : Fin 4,
        waveConst 0 (fun _ => frameBasis μ) =
          if μ = 0 then circularConnectionMat4 (circularSelfDualCoords 0)
          else if μ = 1 then -circularConnectionMat4 (circularSelfDualCoords 0)
          else if μ = 2 then circularConnectionMat4 (circularSelfDualCoords 3)
          else circularConnectionMat4 (circularSelfDualCoords 2) := by
      intro μ
      have hdir : waveDirForm (fun _ => frameBasis μ) =
          ((frameBasis μ 0 - frameBasis μ 1 : ℝ) : ℂ) •
            circularConnectionMat4 (circularSelfDualCoords 0) :=
        rfl
      have hsp : waveSpatialForm (fun _ => frameBasis μ) =
          (frameBasis μ 2 : ℂ) • circularConnectionMat4 (circularSelfDualCoords 3) +
          (frameBasis μ 3 : ℂ) • circularConnectionMat4 (circularSelfDualCoords 2) :=
        rfl
      change (1 : ℝ) • waveDirForm (fun _ => frameBasis μ) +
        waveSpatialForm (fun _ => frameBasis μ) = _
      rw [one_smul, hdir, hsp]
      fin_cases μ <;> simp [t5_frameBasis_apply]
    have hF_eval : ∀ μ ν : Fin 4,
        ymCurvature waveConst 0 ![frameBasis μ, frameBasis ν] =
          waveConst 0 (fun _ => frameBasis μ) * waveConst 0 (fun _ => frameBasis ν) -
          waveConst 0 (fun _ => frameBasis ν) * waveConst 0 (fun _ => frameBasis μ) := by
      intro μ ν
      rw [ymCurvature_apply_two _ hDiffW]
      have hfc : ∀ w, fderiv ℝ (fun y => waveConst y (fun _ => w)) 0 = 0 := by
        intro w
        have hc : (fun y => waveConst y (fun _ => w)) =
            Function.const FourSpace (waveConst 0 (fun _ => w)) := by
          funext y
          rw [congrFun hEqW y]
          rfl
        rw [hc, fderiv_const]
        rfl
      rw [hfc, hfc]
      simp
    simp only [hodgeStar4Eucl, hodgeStar4EuclMap_basis_12,
      hodgeStar4EuclMap_basis_02, hodgeStar4EuclMap_basis_01] at hW0
    rw [hF_eval 0 3, hF_eval 3 1, hF_eval 2 3] at hW0
    simp only [hW_basis, ↓reduceIte] at hW0
    rw [t5_cir_block_0, t5_cir_block_2, t5_cir_block_3] at hW0
    simp only [mat4CCommCLM_apply, neg_mul, mul_neg, one_zsmul, neg_one_zsmul,
      Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, pow_two] at hW0
    have h03 := congrFun (congrFun hW0 0) 3
    simp [chiralOffBlock4, σ1, σ2] at h03

private def t5_asdCLM : FourSpace →L[ℝ] Mat4C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v =>
        -(v 0 : ℂ) • circularConnectionMat4 (circularSelfDualCoords 0) +
        (v 1 : ℂ) • circularConnectionMat4 (circularSelfDualCoords 1) +
        (v 2 : ℂ) • circularConnectionMat4 (circularSelfDualCoords 2) +
        (v 3 : ℂ) • circularConnectionMat4 (circularSelfDualCoords 3)
      map_add' := fun u v => by
        simp only [PiLp.add_apply, Complex.ofReal_add, neg_add, add_smul]
        abel
      map_smul' := fun c v => by
        ext i j
        simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
        ring }

private def t5_asdForm : Mat4CForm 1 :=
  fun _ => ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace)
    (F := Mat4C) (0 : Fin 1) t5_asdCLM

/-- T5-03: Concrete nonzero anti-self-dual Yang–Mills instanton witness (`¬ IsSelfDualForm4`). -/
theorem t5_03_anti_self_dual_nonabelian_instanton_witness :
    IsAntiSelfDualForm4 t5_asdForm ∧
    YangMillsPDE t5_asdForm ∧
    ymCurvature t5_asdForm ≠ 0 ∧
    ¬ IsSelfDualForm4 t5_asdForm := by
  have hCont : ContDiff ℝ ⊤ t5_asdForm := contDiff_const
  have hDiff : Differentiable ℝ t5_asdForm := hCont.differentiable (by simp)
  have hBasis : ∀ x : FourSpace, ∀ μ : Fin 4,
      t5_asdForm x ![frameBasis μ] =
        if μ = 0 then -circularConnectionMat4 (circularSelfDualCoords 0)
        else circularConnectionMat4 (circularSelfDualCoords μ) := by
    intro x μ
    have h : t5_asdForm x ![frameBasis μ] = t5_asdCLM (frameBasis μ) := rfl
    rw [h]
    fin_cases μ <;> simp [t5_asdCLM, t5_frameBasis_apply]
  have hF_eval : ∀ x : FourSpace, ∀ μ ν : Fin 4,
      ymCurvature t5_asdForm x ![frameBasis μ, frameBasis ν] =
        t5_asdForm x ![frameBasis μ] * t5_asdForm x ![frameBasis ν] -
        t5_asdForm x ![frameBasis ν] * t5_asdForm x ![frameBasis μ] := by
    intro x μ ν
    rw [ymCurvature_apply_two _ hDiff]
    have hfc : ∀ w, fderiv ℝ (fun y => t5_asdForm y (fun _ => w)) x = 0 := by
      intro w
      have hc : (fun y => t5_asdForm y (fun _ => w)) = fun _ => t5_asdForm 0 (fun _ => w) := rfl
      rw [hc]
      simp [fderiv_const_apply]
    rw [hfc, hfc]
    have ha0 : (fun _ : Fin 1 => frameBasis μ) = ![frameBasis μ] := by
      funext i; fin_cases i; rfl
    have ha1 : (fun _ : Fin 1 => frameBasis ν) = ![frameBasis ν] := by
      funext i; fin_cases i; rfl
    rw [ha0, ha1]
    simp
  have hF01 : ∀ x, ymCurvature t5_asdForm x ![frameBasis 0, frameBasis 1] =
      -ymCurvature t5_asdForm x ![frameBasis 2, frameBasis 3] := by
    intro x
    rw [hF_eval, hF_eval, hBasis, hBasis, hBasis, hBasis]
    simp only [↓reduceIte, Fin.reduceEq]
    rw [t5_cir_block_0, t5_cir_block_1, t5_cir_block_2, t5_cir_block_3]
    simp only [neg_mul, mul_neg, t5_chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralDiagBlock4, Matrix.mul_apply, σ1, σ2]
  have hF02 : ∀ x, ymCurvature t5_asdForm x ![frameBasis 0, frameBasis 2] =
      -ymCurvature t5_asdForm x ![frameBasis 3, frameBasis 1] := by
    intro x
    rw [hF_eval, hF_eval, hBasis, hBasis, hBasis, hBasis]
    simp only [↓reduceIte, Fin.reduceEq]
    rw [t5_cir_block_0, t5_cir_block_1, t5_cir_block_2, t5_cir_block_3]
    simp only [neg_mul, mul_neg, t5_chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralDiagBlock4, Matrix.mul_apply, σ1, σ2]
  have hF03 : ∀ x, ymCurvature t5_asdForm x ![frameBasis 0, frameBasis 3] =
      -ymCurvature t5_asdForm x ![frameBasis 1, frameBasis 2] := by
    intro x
    rw [hF_eval, hF_eval, hBasis, hBasis, hBasis, hBasis]
    simp only [↓reduceIte, Fin.reduceEq]
    rw [t5_cir_block_0, t5_cir_block_1, t5_cir_block_2, t5_cir_block_3]
    simp only [neg_mul, mul_neg, t5_chiralOffBlock4_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralDiagBlock4, Matrix.mul_apply, σ1, σ2]
  have hASD : IsAntiSelfDualForm4 t5_asdForm := by
    unfold IsAntiSelfDualForm4
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    change hodgeStar4EuclMap (ymCurvature t5_asdForm x) v = (-(ymCurvature t5_asdForm x)) v
    rw [alternating_fourSpace_eq_plucker (hodgeStar4EuclMap (ymCurvature t5_asdForm x)) v,
      alternating_fourSpace_eq_plucker (-(ymCurvature t5_asdForm x)) v]
    rw [hodgeStar4EuclMap_basis_01, hodgeStar4EuclMap_basis_23,
      hodgeStar4EuclMap_basis_02, hodgeStar4EuclMap_basis_31,
      hodgeStar4EuclMap_basis_03, hodgeStar4EuclMap_basis_12]
    simp only [ContinuousAlternatingMap.neg_apply]
    rw [hF01 x, hF02 x, hF03 x]
    simp only [smul_neg, neg_neg]
  have hYM : YangMillsPDE t5_asdForm :=
    antiSelfDual_solves_yangMillsPDE (hCont.of_le le_top) hASD
  have hNe : ymCurvature t5_asdForm ≠ 0 := by
    intro hz
    have h02 := congrFun (congrFun (congrArg (fun g : Mat4CForm 2 =>
      g 0 ![frameBasis 0, frameBasis 2]) hz) 0) 0
    rw [hF_eval 0 0 2, hBasis 0 0, hBasis 0 2] at h02
    simp only [↓reduceIte, Fin.reduceEq, t5_cir_block_0, t5_cir_block_2,
      neg_mul, mul_neg, t5_chiralOffBlock4_mul] at h02
    simp [chiralDiagBlock4, Matrix.mul_apply, σ1, σ2] at h02
  have hNotSD : ¬ IsSelfDualForm4 t5_asdForm := by
    intro hSD
    change hodgeStar4Eucl (ymCurvature t5_asdForm) = ymCurvature t5_asdForm at hSD
    rw [hodgeStar4Eucl_eq_self_iff] at hSD
    have h02 := (hSD 0).2.1
    rw [hF02 0] at h02
    have hadd : ymCurvature t5_asdForm 0 ![frameBasis 3, frameBasis 1] +
        ymCurvature t5_asdForm 0 ![frameBasis 3, frameBasis 1] = 0 := by
      nth_rw 1 [← h02]
      exact neg_add_cancel _
    have h00 := congrFun (congrFun hadd 0) 0
    rw [Matrix.add_apply, hF_eval 0 3 1, hBasis 0 3, hBasis 0 1] at h00
    simp only [Fin.reduceEq, ↓reduceIte, t5_cir_block_3, t5_cir_block_1,
      t5_chiralOffBlock4_mul] at h00
    simp [chiralDiagBlock4, Matrix.mul_apply, σ1, σ2] at h00
  exact ⟨hASD, hYM, hNe, hNotSD⟩

private def t5_varOmega0 : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C :=
  ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace) (F := Mat4C) (0 : Fin 1)
    ((EuclideanSpace.proj (0 : Fin 4)).smulRight
      (circularConnectionMat4 (circularSelfDualCoords 0)))

private def t5_varOmega2 : FourSpace [⋀^Fin 1]→L[ℝ] Mat4C :=
  ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := FourSpace) (F := Mat4C) (0 : Fin 1)
    ((EuclideanSpace.proj (2 : Fin 4)).smulRight
      (circularConnectionMat4 (circularSelfDualCoords 2)))

private def t5_varConn : Mat4CForm 1 :=
  fun x => (x 1 : ℝ) • t5_varOmega0 + (x 0 : ℝ) • t5_varOmega2

/-- T5-04: Non-Abelian spacetime-varying connection with simultaneous `dA ≠ 0`, `[A ∧ A] ≠ 0`,
`F ≠ 0`, `[A ∧ dA] ≠ 0`, and differential Bianchi cancellation `D_A F_A = 0`. -/
theorem t5_04_simultaneous_nonzero_dA_and_commutator_bianchi :
    let x₀ : FourSpace := frameBasis 0 + frameBasis 1
    let dA : Mat4CForm 2 := fun x => ymCurvature t5_varConn x - halfWedgeSelf t5_varConn x
    dA x₀ ![frameBasis 0, frameBasis 2] ≠ 0 ∧
    halfWedgeSelf t5_varConn x₀ ![frameBasis 0, frameBasis 2] ≠ 0 ∧
    ymCurvature t5_varConn x₀ ![frameBasis 0, frameBasis 2] ≠ 0 ∧
    wedgeComm t5_varConn dA x₀ ![frameBasis 0, frameBasis 1, frameBasis 2] ≠ 0 ∧
    covExtDeriv t5_varConn (ymCurvature t5_varConn) = 0 := by
  intro x₀ dA
  have hCont : ContDiff ℝ 2 t5_varConn := by
    let p1 : FourSpace →L[ℝ] ℝ := EuclideanSpace.proj (1 : Fin 4)
    let p0 : FourSpace →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 4)
    have h0 : ContDiff ℝ 2 (fun x : FourSpace => p1 x • t5_varOmega0) :=
      (p1.contDiff.of_le le_top).smul contDiff_const
    have h2 : ContDiff ℝ 2 (fun x : FourSpace => p0 x • t5_varOmega2) :=
      (p0.contDiff.of_le le_top).smul contDiff_const
    exact h0.add h2
  have hDiff : Differentiable ℝ t5_varConn := hCont.differentiable (by norm_num)
  have hEval : ∀ y w : FourSpace,
      t5_varConn y (fun _ => w) =
        (y 1 * w 0 : ℝ) • circularConnectionMat4 (circularSelfDualCoords 0) +
        (y 0 * w 2 : ℝ) • circularConnectionMat4 (circularSelfDualCoords 2) := by
    intro y w
    change ((y 1 : ℝ) • t5_varOmega0 + (y 0 : ℝ) • t5_varOmega2) (fun _ => w) = _
    rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.smul_apply]
    have hv0 : t5_varOmega0 (fun _ => w) =
        w 0 • circularConnectionMat4 (circularSelfDualCoords 0) :=
      rfl
    have hv2 : t5_varOmega2 (fun _ => w) =
        w 2 • circularConnectionMat4 (circularSelfDualCoords 2) :=
      rfl
    rw [hv0, hv2, smul_smul, smul_smul]
  have hFd : ∀ x u w : FourSpace,
      fderiv ℝ (fun y => t5_varConn y (fun _ => w)) x u =
        (u 1 * w 0 : ℝ) • circularConnectionMat4 (circularSelfDualCoords 0) +
        (u 0 * w 2 : ℝ) • circularConnectionMat4 (circularSelfDualCoords 2) := by
    intro x u w
    have hfun : (fun y => t5_varConn y (fun _ => w)) =
        fun y => ((EuclideanSpace.proj (1 : Fin 4) y) •
          (w 0 • circularConnectionMat4 (circularSelfDualCoords 0)) +
          (EuclideanSpace.proj (0 : Fin 4) y) •
          (w 2 • circularConnectionMat4 (circularSelfDualCoords 2))) := by
      funext y
      rw [hEval, ← smul_smul, ← smul_smul]
      rfl
    rw [hfun]
    let L : FourSpace →L[ℝ] Mat4C :=
      (EuclideanSpace.proj (1 : Fin 4)).smulRight
          (w 0 • circularConnectionMat4 (circularSelfDualCoords 0)) +
        (EuclideanSpace.proj (0 : Fin 4)).smulRight
          (w 2 • circularConnectionMat4 (circularSelfDualCoords 2))
    have hEqL : (fun y : FourSpace =>
        (EuclideanSpace.proj (1 : Fin 4) y) •
          (w 0 • circularConnectionMat4 (circularSelfDualCoords 0)) +
        (EuclideanSpace.proj (0 : Fin 4) y) •
          (w 2 • circularConnectionMat4 (circularSelfDualCoords 2))) = L :=
      rfl
    rw [hEqL, L.fderiv]
    dsimp [L]
    rw [add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRight_apply, smul_smul, smul_smul]
    rfl
  have hdA_eval : ∀ x u w : FourSpace,
      dA x ![u, w] =
        fderiv ℝ (fun y => t5_varConn y (fun _ => w)) x u -
        fderiv ℝ (fun y => t5_varConn y (fun _ => u)) x w := by
    intro x u w
    have hy := ymCurvature_apply_two t5_varConn hDiff x u w
    change (ymCurvature t5_varConn x - halfWedgeSelf t5_varConn x) ![u, w] = _
    rw [ContinuousAlternatingMap.sub_apply, hy, halfWedgeSelf_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mat4CCommCLM_apply]
    abel
  have hx₀0 : x₀ 0 = 1 := by
    change (frameBasis 0 + frameBasis 1) 0 = 1
    rw [PiLp.add_apply, t5_frameBasis_apply, t5_frameBasis_apply]
    norm_num
  have hx₀1 : x₀ 1 = 1 := by
    change (frameBasis 0 + frameBasis 1) 1 = 1
    rw [PiLp.add_apply, t5_frameBasis_apply, t5_frameBasis_apply]
    norm_num
  have hdA_02 : dA x₀ ![frameBasis 0, frameBasis 2] =
      circularConnectionMat4 (circularSelfDualCoords 2) := by
    rw [hdA_eval, hFd, hFd]
    simp [t5_frameBasis_apply]
  have hdA_12 : dA x₀ ![frameBasis 1, frameBasis 2] = 0 := by
    rw [hdA_eval, hFd, hFd]
    simp [t5_frameBasis_apply]
  have hdA_01 : dA x₀ ![frameBasis 0, frameBasis 1] =
      -circularConnectionMat4 (circularSelfDualCoords 0) := by
    rw [hdA_eval, hFd, hFd]
    simp [t5_frameBasis_apply]
  have hHW_02 : halfWedgeSelf t5_varConn x₀ ![frameBasis 0, frameBasis 2] =
      circularConnectionMat4 (circularSelfDualCoords 0) *
        circularConnectionMat4 (circularSelfDualCoords 2) -
      circularConnectionMat4 (circularSelfDualCoords 2) *
        circularConnectionMat4 (circularSelfDualCoords 0) := by
    rw [halfWedgeSelf_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mat4CCommCLM_apply, hEval,
      t5_frameBasis_apply, hx₀0, hx₀1]
    simp
  have hdA_ne : dA x₀ ![frameBasis 0, frameBasis 2] ≠ 0 := by
    rw [hdA_02, t5_cir_block_2]
    intro hz
    have h21 := congrFun (congrFun hz 2) 1
    simp [chiralOffBlock4, σ2] at h21
  have hHW_ne : halfWedgeSelf t5_varConn x₀ ![frameBasis 0, frameBasis 2] ≠ 0 := by
    rw [hHW_02, t5_cir_block_0, t5_cir_block_2, t5_chiralOffBlock4_mul, t5_chiralOffBlock4_mul]
    intro hz
    have h00 := congrFun (congrFun hz 0) 0
    simp [chiralDiagBlock4, Matrix.mul_apply, σ1, σ2] at h00
  have hF_ne : ymCurvature t5_varConn x₀ ![frameBasis 0, frameBasis 2] ≠ 0 := by
    rw [ymCurvature_apply_two t5_varConn hDiff x₀, hFd, hFd]
    have hcom :
        ((t5_varConn x₀ (fun _ => frameBasis 0) * t5_varConn x₀ (fun _ => frameBasis 2)) -
          (t5_varConn x₀ (fun _ => frameBasis 2) * t5_varConn x₀ (fun _ => frameBasis 0))) =
        halfWedgeSelf t5_varConn x₀ ![frameBasis 0, frameBasis 2] := by
      rw [halfWedgeSelf_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mat4CCommCLM_apply]
    rw [hcom, hHW_02, t5_cir_block_0, t5_cir_block_2, t5_chiralOffBlock4_mul,
      t5_chiralOffBlock4_mul]
    simp only [t5_frameBasis_apply]
    norm_num
    intro hz
    have h00 := congrFun (congrFun hz 0) 0
    simp [one_smul, zero_smul, chiralDiagBlock4, chiralOffBlock4, σ1, σ2] at h00
  have hComm_dA_ne :
      wedgeComm t5_varConn dA x₀ ![frameBasis 0, frameBasis 1, frameBasis 2] ≠ 0 := by
    have hA0 : t5_varConn x₀ (fun _ => frameBasis 0) = chiralOffBlock4 σ1 0 := by
      rw [hEval, t5_frameBasis_apply, t5_frameBasis_apply, hx₀1]
      simp [t5_cir_block_0]
    have hA1 : t5_varConn x₀ (fun _ => frameBasis 1) = 0 := by
      rw [hEval, t5_frameBasis_apply, t5_frameBasis_apply]
      simp
    have hA2 : t5_varConn x₀ (fun _ => frameBasis 2) = chiralOffBlock4 0 (-σ2) := by
      rw [hEval, t5_frameBasis_apply, t5_frameBasis_apply, hx₀0]
      simp [t5_cir_block_2]
    dsimp [wedgeComm]
    rw [wedgeCommAt_apply, Fin.sum_univ_three]
    have hr0 : (0 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 1, frameBasis 2] := by
      funext i; fin_cases i <;> rfl
    have hr1 : (1 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 0, frameBasis 2] := by
      funext i; fin_cases i <;> rfl
    have hr2 : (2 : Fin 3).removeNth ![frameBasis 0, frameBasis 1, frameBasis 2] =
        ![frameBasis 0, frameBasis 1] := by
      funext i; fin_cases i <;> rfl
    have hv0 : ![frameBasis 0, frameBasis 1, frameBasis 2] 0 = frameBasis 0 := rfl
    have hv1 : ![frameBasis 0, frameBasis 1, frameBasis 2] 1 = frameBasis 1 := rfl
    have hv2 : ![frameBasis 0, frameBasis 1, frameBasis 2] 2 = frameBasis 2 := rfl
    rw [hr0, hr1, hr2, hv0, hv1, hv2, hdA_12, hdA_02, hdA_01, hA0, hA1, hA2]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, pow_two,
      one_zsmul, neg_one_zsmul, map_zero, zero_apply, neg_zero, zero_add, add_zero,
      mat4CCommCLM_apply, mul_neg, neg_mul, sub_neg_eq_add, t5_cir_block_0,
      t5_chiralOffBlock4_mul]
    intro hz
    have h00 := congrFun (congrFun hz 0) 0
    simp [chiralDiagBlock4, Matrix.mul_apply, σ1, σ2] at h00
  exact ⟨hdA_ne, hHW_ne, hF_ne, hComm_dA_ne, bianchi_identity_ymCurvature hCont⟩

/-- T5-05: Flagship `circularGaugeForm_nonabelian_ym_solution`, `circularGaugeForm_isSelfDual`,
and nontrivial `circularGaugeConnection4 circularSelfDualExtOmega ≠ 0`. -/
theorem t5_05_main_circular_ym_bridge_and_ext_omega
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (star d : Module.End ℂ (ExteriorAlgebra ℂ V))
    (X : Matrix (Fin 4) (Fin 4) (ExteriorAlgebra ℂ V))
    (σ : FourSpace → ChiralFiber) (x v : FourSpace) :
    (ymCurvature circularGaugeForm ≠ 0 ∧
      IsSelfDualForm4 circularGaugeForm ∧
      YangMillsPDE circularGaugeForm ∧
      (circularBundleConnection circularGaugeForm σ x v =
        fderiv ℝ σ x v +
          (∑ μ : Fin 4, (v μ : ℂ) • circularConnectionMat4 (circularSelfDualCoords μ)).mulVec
            (σ x))) ∧
    circularGaugeConnection4 circularSelfDualExtOmega ≠ 0 ∧
    (∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A) ∧
    (∃ A B : Matrix (Fin 4) (Fin 4) ℂ, A * B ≠ B * A) := by
  have hMain := circularGaugeForm_nonabelian_ym_solution star d X σ x v
  have hExt_ne : circularGaugeConnection4 circularSelfDualExtOmega ≠ 0 := by
    intro hz
    have h03 : circularGaugeConnection4 circularSelfDualExtOmega 0 3 = 0 := by
      simpa using congrFun (congrFun hz 0) 3
    let evalSq0 : ExteriorAlgebra ℂ ChiralFiber →ₐ[ℂ] TrivSqZeroExt ℂ ChiralFiber :=
      ExteriorAlgebra.lift ℂ
        ⟨TrivSqZeroExt.inrHom ℂ ChiralFiber, fun w => by
          have hfst : ((TrivSqZeroExt.inrHom ℂ ChiralFiber) w).fst = 0 := rfl
          apply TrivSqZeroExt.ext
          · rw [TrivSqZeroExt.fst_mul, hfst]
            simp
          · rw [TrivSqZeroExt.snd_mul, hfst]
            simp⟩
    have hev := congrArg (fun e => (evalSq0 e).snd 0) h03
    have heval_ι : ∀ μ : Fin 4,
        evalSq0 (ExteriorAlgebra.ι ℂ (Pi.single μ 1)) = TrivSqZeroExt.inr (Pi.single μ 1) := by
      intro μ
      dsimp [evalSq0]
      rw [ExteriorAlgebra.lift_ι_apply]
      rfl
    have hc1 : circularSelfDualCoords 0 1 = 1 := by
      have hc : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
        simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 1
      simp [circularSelfDualCoords, hc]
    have hcOther : ∀ μ : Fin 4, μ ≠ 0 → circularSelfDualCoords μ 1 = 0 := by
      intro μ hμ
      have h1 : coordinateEquiv (rootPlus 1) = Pi.single 2 1 := by
        simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 2
      have h2 : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
        simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 6
      have h3 : coordinateEquiv (rootMinus 0) = Pi.single 5 1 := by
        simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 5
      fin_cases μ
      · exact False.elim (hμ rfl)
      · simp [circularSelfDualCoords, h1]
      · simp [circularSelfDualCoords, h2]
      · simp [circularSelfDualCoords, h3]
    have hOm1 : (evalSq0 (circularSelfDualExtOmega 1)).snd 0 = 1 := by
      dsimp [circularSelfDualExtOmega]
      rw [map_sum]
      simp only [AlgHom.map_smul_of_tower, heval_ι]
      rw [Fin.sum_univ_four]
      simp [hc1, hcOther 1 (by decide), hcOther 2 (by decide), hcOther 3 (by decide)]
    have hOm2 : (evalSq0 (circularSelfDualExtOmega 2)).snd 0 = 0 := by
      have h0 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
        simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 1
      have h1 : coordinateEquiv (rootPlus 1) = Pi.single 2 1 := by
        simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 2
      have h2 : coordinateEquiv (rootMinus 1) = Pi.single 6 1 := by
        simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 6
      have h3 : coordinateEquiv (rootMinus 0) = Pi.single 5 1 := by
        simpa [SplitOctonionEllCircularPeirceBasis.frame] using coordinateEquiv_apply_frame 5
      dsimp [circularSelfDualExtOmega]
      rw [map_sum]
      simp only [AlgHom.map_smul_of_tower, heval_ι]
      rw [Fin.sum_univ_four]
      simp [circularSelfDualCoords, h0, h1, h2, h3]
    have h03_eq : circularGaugeConnection4 circularSelfDualExtOmega 0 3 =
        circularSelfDualExtOmega 1 - Complex.I • circularSelfDualExtOmega 2 := by
      simp [circularGaugeConnection4, weylUpperExt, chiralOffBlock4, sub_eq_add_neg]
    rw [h03_eq, map_sub, AlgHom.map_smul_of_tower, map_zero, TrivSqZeroExt.snd_zero,
      TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_smul, Pi.sub_apply, Pi.smul_apply,
      hOm1, hOm2, smul_zero, sub_zero] at hev
    exact one_ne_zero hev
  exact ⟨⟨hMain.1, circularGaugeForm_isSelfDual, hMain.2.2.1, hMain.2.2.2.1⟩,
    hExt_ne, mat4C_noncomm_witness, circularGaugeForm_mat4C_noncomm_witness⟩

/-- T5-06: Bundle local/global projector agreement, `mat4CToRealCLM_mul`, `trivialChiralConnection`,
`mat4COneFormToBundleEnd`, `oneFormCLM`/`circularGaugeOneFormCLM`, and bundle connection Leibniz. -/
theorem t5_06_bundle_projector_local_global_and_leibniz
    (x₀ x v : FourSpace) (σ : FourSpace → ChiralFiber)
    (g : FourSpace → ℝ)
    (hσ : MDifferentiableAt (𝓡 4) 𝓘(ℝ, ChiralFiber) σ x)
    (hg : DifferentiableAt ℝ g x) :
    let e := trivializationAt ChiralFiber (TrivialChiralBundle FourSpace) x₀
    (chiralLocalBundleProjector e x = chiralBundleProjector FourSpace x) ∧
    (chiralProjCLM.comp chiralProjCLM = chiralProjCLM) ∧
    (mat4CToRealCLM (circularGaugeForm x ![frameBasis 0] *
        circularGaugeForm x ![frameBasis 2]) =
      (mat4CToRealCLM (circularGaugeForm x ![frameBasis 0])).comp
        (mat4CToRealCLM (circularGaugeForm x ![frameBasis 2]))) ∧
    (trivialChiralConnection FourSpace σ x v = fderiv ℝ σ x v) ∧
    (mat4COneFormToBundleEnd circularGaugeForm x (σ x) v =
      (circularGaugeForm x (fun _ => v)).mulVec (σ x)) ∧
    (oneFormCLM (circularGaugeForm x) v = circularGaugeForm x (fun _ => v)) ∧
    (oneFormCLM circularGaugeOneForm v = circularGaugeOneFormCLM v) ∧
    (circularBundleConnection circularGaugeForm (fun y => g y • σ y) x v =
      (fderiv ℝ g x v) • σ x + g x • (circularBundleConnection circularGaugeForm σ x v)) := by
  intro e
  have hProj : chiralLocalBundleProjector e x = chiralBundleProjector FourSpace x := by
    ext w i
    simp [e, chiralLocalBundleProjector, chiralBundleProjector,
      Bundle.Trivial.fiberBundle_trivializationAt']
    rfl
  have hTriv : trivialChiralConnection FourSpace σ x v = fderiv ℝ σ x v := by
    dsimp [trivialChiralConnection]
    rw [mvfderiv_eq_fderiv]
    rfl
  have hEnd : mat4COneFormToBundleEnd circularGaugeForm x (σ x) v =
      (circularGaugeForm x (fun _ => v)).mulVec (σ x) :=
    rfl
  have hLeib :
      circularBundleConnection circularGaugeForm (fun y => g y • σ y) x v =
        (fderiv ℝ g x v) • σ x + g x • (circularBundleConnection circularGaugeForm σ x v) := by
    rw [circularBundleConnection_apply, circularBundleConnection_apply]
    have hf : DifferentiableAt ℝ σ x := hσ.differentiableAt
    have hfd : fderiv ℝ (fun y => g y • σ y) x v =
        (fderiv ℝ g x v) • σ x + g x • fderiv ℝ σ x v := by
      rw [fderiv_fun_smul hg hf]
      simp [add_comm]
    have hmul :
        (circularGaugeForm x (fun _ => v)).mulVec (g x • σ x) =
          g x • (circularGaugeForm x (fun _ => v)).mulVec (σ x) := by
      ext i
      simp [Matrix.mulVec, Complex.real_smul]
    rw [hfd, hmul, smul_add]
    abel
  exact ⟨hProj, chiralProjCLM_idempotent, mat4CToRealCLM_mul _ _, hTriv, hEnd,
    oneFormCLM_apply (circularGaugeForm x) v,
    (oneFormCLM_apply circularGaugeOneForm v).trans rfl, hLeib⟩

/-- T5-07: Krein fiber coordinate equivalence, `(2, -2)` indefinite signature witnesses, and
Plücker 6-component extensionality completeness. -/
theorem t5_07_krein_fiber_coord_equiv_and_plucker_completeness
    (u : ChiralFiber) (η₁ η₂ : FourSpace [⋀^Fin 2]→L[ℝ] Mat4C)
    (h01 : η₁ ![frameBasis 0, frameBasis 1] = η₂ ![frameBasis 0, frameBasis 1])
    (h23 : η₁ ![frameBasis 2, frameBasis 3] = η₂ ![frameBasis 2, frameBasis 3])
    (h02 : η₁ ![frameBasis 0, frameBasis 2] = η₂ ![frameBasis 0, frameBasis 2])
    (h31 : η₁ ![frameBasis 3, frameBasis 1] = η₂ ![frameBasis 3, frameBasis 1])
    (h03 : η₁ ![frameBasis 0, frameBasis 3] = η₂ ![frameBasis 0, frameBasis 3])
    (h12 : η₁ ![frameBasis 1, frameBasis 2] = η₂ ![frameBasis 1, frameBasis 2]) :
    (chiralFiberToKreinFrame (chiralProjCLM u) =
      leftChiralProjector (E := FourSpace) (chiralFiberToKreinFrame u)) ∧
    (fiberCoordEquiv.symm (fiberCoordEquiv u) = u) ∧
    (fiberCoordEquiv (Pi.single 0 1) ≠ fiberCoordEquiv (Pi.single 1 1)) ∧
    (fiberKreinPairing (Pi.single 0 1 + Pi.single 2 1) (Pi.single 0 1 + Pi.single 2 1) = 2) ∧
    (fiberKreinPairing (Pi.single 0 1 - Pi.single 2 1) (Pi.single 0 1 - Pi.single 2 1) = -2) ∧
    (η₁ = η₂) := by
  have hInj : fiberCoordEquiv (Pi.single 0 1) ≠ fiberCoordEquiv (Pi.single 1 1) := by
    intro h
    have h0 : (Pi.single 0 (1 : ℂ) : ChiralFiber) = Pi.single 1 1 :=
      fiberCoordEquiv.injective h
    have h00 := congrFun h0 0
    simp at h00
  have hPos : fiberKreinPairing (Pi.single 0 1 + Pi.single 2 1)
      (Pi.single 0 1 + Pi.single 2 1) = 2 := by
    simp [fiberKreinPairing, chiralKreinForm, chiralFiberToKreinFrame,
      PiLp.norm_sq_eq_of_L2, Fin.sum_univ_four]
    norm_num
  have hNeg : fiberKreinPairing (Pi.single 0 1 - Pi.single 2 1)
      (Pi.single 0 1 - Pi.single 2 1) = -2 := by
    simp [fiberKreinPairing, chiralKreinForm, chiralFiberToKreinFrame,
      PiLp.inner_apply, Fin.sum_univ_four]
  have hPluckerExt : η₁ = η₂ := by
    apply ContinuousAlternatingMap.ext
    intro w
    rw [alternating_fourSpace_eq_plucker η₁ w, alternating_fourSpace_eq_plucker η₂ w]
    rw [h01, h23, h02, h31, h03, h12]
  exact ⟨chiralFiberToKreinFrame_intertwines_proj u,
    fiberCoordEquiv.symm_apply_apply u, hInj, hPos, hNeg, hPluckerExt⟩

private lemma t5_m1_05_graded_hodge_witness :
    ∃ x : Coordinate,
      let P := chiralExteriorProj4 (Fin 4 → ℂ)
      let A := circularGaugeConnection4 (circularGradedOmega x)
      genJ P A A ≠ 0 ∧
      curvatureFromConnection 0 A = genV P A A ∧
      covariantDerivative A 0 (genV P A A) = 0 ∧
      matrixHodgeStar scalarFlipStar (curvatureFromConnection 0 A) ≠ 0 := by
  rcases circularGradedDiff_nondegenerate_witness with ⟨x, _, _, _, hGenJ, hGenV⟩
  have hBr := circularGradedDiff_yang_mills_bridge_general scalarFlipStar x 0
  dsimp only at hBr
  refine ⟨x, hGenJ, hBr.2.2.2.2.1, hBr.2.2.2.2.2.1, ?_⟩
  rw [hBr.2.2.2.2.1]
  let A := circularGaugeConnection4 (circularGradedOmega x)
  have hGenV_eq : genV (chiralExteriorProj4 (Fin 4 → ℂ)) A A = A * A := by
    dsimp only [A]
    unfold circularGaugeConnection4 chiralExteriorProj4
    rw [genV, anticomm, conePlus_chiralOffBlock4, coneMinus_chiralOffBlock4,
      chiralOffBlock4_mul, chiralOffBlock4_mul, chiralOffBlock4_mul]
    ext i j; fin_cases i <;> fin_cases j <;> simp [chiralDiagBlock4]
  have hinv_ω : ∀ m : Fin 8,
      (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ))
        (circularGradedOmega x m) = 0 := by
    intro m
    unfold circularGradedOmega
    split_ifs
    · rw [map_smul, algebraMapInv_uPlusForm, smul_zero]
    · rw [map_smul, algebraMapInv_uMinusForm, smul_zero]
  have hinv_zero : ∀ r s : Fin 4,
      (ExteriorAlgebra.algebraMapInv (R := ℂ) (M := Fin 4 → ℂ)) (A r s) = 0 := by
    intro r s
    fin_cases r <;> fin_cases s <;>
      (dsimp only [A]
       unfold circularGaugeConnection4 chiralOffBlock4 weylUpperExt weylLowerExt) <;>
      simp [map_add, map_sub, map_neg, map_smul, hinv_ω]
  have hfix : matrixHodgeStar scalarFlipStar (genV (chiralExteriorProj4 (Fin 4 → ℂ)) A A) =
      genV (chiralExteriorProj4 (Fin 4 → ℂ)) A A := by
    rw [hGenV_eq]
    ext i j
    change scalarFlipStar ((A * A) i j) = (A * A) i j
    rw [Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ =>
      scalarFlipStar_fixes_mul (A i k) (A k j) (hinv_zero i k)
  rw [hfix]
  exact hGenV

/-- T5-M1-05: Covers `matrixExteriorDerivative_chiralOffBlock4` (general ring & incompatible `d`),
`chiralOffBlock4_eigencondition_iff.mp` negative check, `genJ ≠ 0` from graded witness,
`P * A ≠ A * P` and `matrixTraceForm (A * A) = 0` from even witness, and remaining
conjuncts 5–6 plus nonzero Hodge-star target of `circularGradedDiff_yang_mills_bridge_general`. -/
theorem t5_m1_05_offblock_deriv_witnesses_and_bridge_conjuncts
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (dR : Module.End R (ExteriorAlgebra R V))
    (U L : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V)) :
    matrixExteriorDerivative dR (chiralOffBlock4 U L) =
      chiralOffBlock4 (U.map dR) (L.map dR) ∧
    (let U1 : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra ℂ (Fin 4 → ℂ)) := !![uPlusForm, 0; 0, 0]
     matrixExteriorDerivative circularEvenDiff (chiralOffBlock4 U1 0) ≠
       peirceGradingDeriv (chiralExteriorProj4 (Fin 4 → ℂ)) (chiralOffBlock4 U1 0)) ∧
    (∃ x : Coordinate,
      let P := chiralExteriorProj4 (Fin 4 → ℂ)
      let A := circularGaugeConnection4 (circularGradedOmega x)
      genJ P A A ≠ 0 ∧
      curvatureFromConnection 0 A = genV P A A ∧
      covariantDerivative A 0 (genV P A A) = 0 ∧
      matrixHodgeStar scalarFlipStar (curvatureFromConnection 0 A) ≠ 0) ∧
    (∃ x : Coordinate,
      let P := chiralExteriorProj4 (Fin 4 → ℂ)
      let A := circularGaugeConnection4 (circularEvenOmega x)
      A ≠ 0 ∧ genV P A A ≠ 0 ∧ P * A ≠ A * P ∧ matrixTraceForm (A * A) = 0) := by
  refine ⟨matrixExteriorDerivative_chiralOffBlock4 dR U L, ?_,
    t5_m1_05_graded_hodge_witness, circularEvenDiff_nondegenerate_witness⟩
  intro U1 h
  have hU := ((chiralOffBlock4_eigencondition_iff circularEvenDiff U1 0).mp h).1
  have h00 := congrFun (congrFun hU 0) 0
  simp only [U1, Matrix.map_apply, Matrix.of_apply, Matrix.cons_val_zero] at h00
  have hbad : (2 : ℂ) • (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
      ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) +
      ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ)) = uPlusForm := by
    calc
      (2 : ℂ) • (ExteriorAlgebra.ι ℂ (Pi.single 0 (1 : ℂ)) *
          ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))) +
          ExteriorAlgebra.ι ℂ (Pi.single 1 (1 : ℂ))
          = circularEvenDiff uPlusForm := by
            unfold uPlusForm circularEvenDiff
            have hf0 : circularEvenMap (Pi.single 0 (1 : ℂ)) = Pi.single 0 1 := by
              ext i; fin_cases i <;> simp [circularEvenMap]
            have hf1 : circularEvenMap (Pi.single 1 (1 : ℂ)) = Pi.single 1 1 := by
              ext i; fin_cases i <;> simp [circularEvenMap]
            rw [map_add, InfoGeometry.CliffordExteriorLift.exteriorLift_even_derivation,
              InfoGeometry.CliffordExteriorLift.exteriorLift_ι,
              InfoGeometry.CliffordExteriorLift.exteriorLift_ι, hf0, hf1, ← two_smul ℂ]
      _ = uPlusForm := h00
  unfold uPlusForm at hbad
  have hcoeff := congrArg
    (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1) hbad
  have hev := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
    0 1 0 1 0).1
  have hev1 := (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff_eval
    0 1 1 0 0).2.1
  rw [map_add, map_add, map_smul, smul_eq_mul] at hcoeff
  change (2 : ℂ) * InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
    (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
      InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) +
    InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
    (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) =
    InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
    (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 0 *
      InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) +
    InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.blade2Coeff 0 1
    (InfoGeometry.Canonical.DoubledMinkowskiCircularPeirceYangMills.extBasisOneForm 1) at hcoeff
  rw [hev, hev1] at hcoeff
  norm_num at hcoeff

/-- T5-M2-04: Non-vacuous `circularColimit_continuum_transport` with `Φ` giving nonzero
`ψ (continuumCovariantDeriv A Φ y 0) ≠ 0`, plus full `k = 0` `tailTower` `Tendsto` conjuncts
and `(1, 0)` plaquette action convergence on varying non-Abelian `A`. -/
theorem t5_m2_04_colimit_nonvacuous_cov_diff_and_tailtower_k0 :
    let cone := CanonicalTwoSheetedInductiveColimit.tailTowerCone Mat4C
    let ι5 := diagTowerStarHom 5
    let ψ5 : Mat4C →+* CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C :=
      (cone.toColimit 5).toRingHom.comp ι5.toRingHom
    let A : FourSpace → Fin 4 → Mat4C :=
      fun z μ => circularConnectionMat4 (witnessCircularField z μ)
    let Φ : FourSpace → Mat4C := fun z => (z 0 : ℂ) • chiralProjMat4
    let y : FourSpace := frameBasis 0
    ψ5 (continuumCovariantDeriv A Φ y 0) ≠ 0 ∧
    Filter.Tendsto (fun a : ℝ => ψ5 (latticeCovariantDiff A Φ y 0 a))
      (𝓝[≠] 0) (nhds (ψ5 (continuumCovariantDeriv A Φ y 0))) ∧
    (let ι0 := diagTowerStarHom 0
     let ψ0 := (cone.toColimit 0).toRingHom.comp ι0.toRingHom
     Filter.Tendsto (fun a : ℝ => ψ0 ((a ^ 2)⁻¹ • (wilsonPlaquette A y 0 1 a - 1)))
       (𝓝[≠] 0) (nhds (ψ0 (continuumCurvature A y 0 1))) ∧
     Filter.Tendsto (fun a : ℝ => ψ0 (latticeCovariantDiff A (fun _ => 1) y 0 a))
       (𝓝[≠] 0) (nhds (ψ0 (continuumCovariantDeriv A (fun _ => 1) y 0)))) ∧
    (let M0 := circularConnectionMat4 (coordinateEquiv (rootPlus 0))
     let M1 := circularConnectionMat4 (coordinateEquiv (rootMinus 1))
     let A_var : FourSpace → Fin 4 → Mat4C := fun z μ =>
       if μ = 0 then (z 1 : ℂ) • M0
       else if μ = 1 then (z 0 : ℂ) • M1
       else 0
     let y_var : FourSpace := frameBasis 0 + frameBasis 1
     continuumPlaquetteAction A_var y_var 1 0 = continuumPlaquetteAction A_var y_var 0 1 ∧
     Filter.Tendsto (fun a : ℝ => wilsonPlaquetteAction A_var y_var 1 0 a)
       (𝓝[≠] 0) (nhds (continuumPlaquetteAction A_var y_var 0 1))) := by
  intro cone ι5 ψ5 A Φ y
  have hψ_eq : (ψ5 : Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C) =
      fun M _ => M := by
    funext M n
    change CanonicalTwoSheetedInductiveColimit.towerColimitFn 5 (fun _ => M, M) n = M
    by_cases hn : n < 5 <;> simp [CanonicalTwoSheetedInductiveColimit.towerColimitFn, hn]
  have hCont : Continuous (cone.toColimit 5 |>.toRingHom.comp ι5.toRingHom) := by
    change Continuous (ψ5 : Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C)
    rw [hψ_eq]
    exact continuous_pi fun _ => continuous_id
  have hA_cd : ContDiff ℝ 2 A := by
    have hA_eq : A = fun _ μ => circularConnectionMat4 (witnessCircularField 0 μ) := rfl
    rw [hA_eq]
    exact contDiff_const
  have hΦ_diff : DifferentiableAt ℝ Φ y := by fun_prop
  have hCovLim := (circularColimit_continuum_transport cone 5 ι5 hCont witnessCircularField
    A Φ y 0 1 hA_cd hΦ_diff).1
  have hCov_ne : ψ5 (continuumCovariantDeriv A Φ y 0) ≠ 0 := by
    have hFderiv : fderiv ℝ Φ y (frameBasis 0) = chiralProjMat4 := by
      have h0 : HasFDerivAt (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4)))
          (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))) y :=
        ContinuousLinearMap.hasFDerivAt _
      have hfd : HasFDerivAt Φ
          ((Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))).smulRight chiralProjMat4) y :=
        h0.smul_const chiralProjMat4
      rw [hfd.fderiv]
      simp [frameBasis]
    have hy0 : (y 0 : ℝ) = 1 := by simp [y, frameBasis]
    have hc1 : coordinateEquiv (rootPlus 0) = Pi.single 1 1 := by
      simpa [frame] using coordinateEquiv_apply_frame 1
    intro h0
    have h0' : continuumCovariantDeriv A Φ y 0 = 0 := by
      have hEval := congrFun h0 0
      change (ψ5 : Mat4C → CanonicalTwoSheetedInductiveColimit.TowerColimit Mat4C)
        (continuumCovariantDeriv A Φ y 0) 0 = 0 at hEval
      rw [hψ_eq] at hEval
      exact hEval
    unfold continuumCovariantDeriv at h0'
    rw [hFderiv] at h0'
    have h00 := congrFun (congrFun h0' 0) 0
    simp [A, Φ, hy0, witnessCircularField, circularConnectionMat4, chiralOffBlock4, weylUpperMat,
      pauliSolder2x2, solder, σ1, hc1, chiralProjMat4, chiralProj4, chiralDiagBlock4] at h00
  have hT0 := circularColimit_continuum_transport_tailTower 0 y
  refine ⟨hCov_ne, hCovLim, ⟨hT0.2.1, hT0.2.2⟩, ?_⟩
  intro M0 M1 A_var y_var
  have hCd0 : ContDiff ℝ 2 (fun z : FourSpace => (z 1 : ℂ) • M0) :=
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 4))).contDiff).smul contDiff_const
  have hCd1 : ContDiff ℝ 2 (fun z : FourSpace => (z 0 : ℂ) • M1) :=
    ((Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))).contDiff).smul contDiff_const
  have hAvar_cd : ContDiff ℝ 2 A_var := by
    refine contDiff_pi.mpr fun μ => ?_
    fin_cases μ
    · exact hCd0
    · exact hCd1
    · exact contDiff_const
    · exact contDiff_const
  have hAct_eq : continuumPlaquetteAction A_var y_var 1 0 =
      continuumPlaquetteAction A_var y_var 0 1 := by
    unfold continuumPlaquetteAction
    rw [continuumCurvature_antisymm A_var y_var 0 1]
    simp [Matrix.conjTranspose_neg, neg_mul, mul_neg]
  refine ⟨hAct_eq, ?_⟩
  rw [← hAct_eq]
  exact tendsto_wilsonPlaquetteAction A_var y_var 1 0 hAvar_cd

/-- T5-Cross-03: Exercises `minkowski_dualConnection_unique` on concrete non-zero boost/rotation
matrices and checks tracelessness of `continuumCurvature` for spacetime-varying `A_var`. -/
theorem t5_cross_03_minkowski_dual_connection_and_varying_trace :
    (let ω : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else 0
     let ωDual := dualConnectionWithMetric minkowskiEta4 ω
     ω.transpose * minkowskiEta4 + minkowskiEta4 * ωDual = 0 ∧
     ωDual ≠ 0 ∧
     (∀ ω' : Matrix (Fin 4) (Fin 4) ℝ,
       ω.transpose * minkowskiEta4 + minkowskiEta4 * ω' = 0 → ω' = ωDual)) ∧
    (let M0 := circularConnectionMat4 (coordinateEquiv (rootPlus 0))
     let M1 := circularConnectionMat4 (coordinateEquiv (rootMinus 1))
     let A_var : FourSpace → Fin 4 → Mat4C := fun z μ =>
       if μ = 0 then (z 1 : ℂ) • M0
       else if μ = 1 then (z 0 : ℂ) • M1
       else 0
     (continuumCurvature A_var (frameBasis 0 + frameBasis 1) 0 1).trace = 0) := by
  refine ⟨?_, ?_⟩
  · intro ω ωDual
    have hinv : minkowskiEta4⁻¹ = minkowskiEta4 :=
      Matrix.inv_eq_right_inv minkowskiEta4_mul_self
    have hcompat : ω.transpose * minkowskiEta4 + minkowskiEta4 * ωDual = 0 := by
      dsimp only [ωDual, dualConnectionWithMetric]
      rw [hinv]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [minkowskiEta4, ω, Matrix.mul_apply, Fin.sum_univ_four]
    have hne : ωDual ≠ 0 := by
      intro hz
      have h10 := congrFun (congrFun hz 1) 0
      dsimp only [ωDual, dualConnectionWithMetric] at h10
      rw [hinv] at h10
      simp [minkowskiEta4, ω, Matrix.mul_apply, Fin.sum_univ_four] at h10
    refine ⟨hcompat, hne, fun ω' h' => minkowski_dualConnection_unique ω ω' h'⟩
  · intro M0 M1 A_var
    let y_var : FourSpace := frameBasis 0 + frameBasis 1
    have hfd0 : fderiv ℝ (fun z => A_var z 1) y_var (frameBasis 0) = M1 := by
      have hfd : HasFDerivAt (fun z : FourSpace => A_var z 1)
          ((Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))).smulRight M1) y_var := by
        have h0 : HasFDerivAt (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4)))
            (Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 4))) y_var :=
          ContinuousLinearMap.hasFDerivAt _
        exact h0.smul_const M1
      rw [hfd.fderiv]
      simp [frameBasis]
    have hfd1 : fderiv ℝ (fun z => A_var z 0) y_var (frameBasis 1) = M0 := by
      have hfd : HasFDerivAt (fun z : FourSpace => A_var z 0)
          ((Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 4))).smulRight M0) y_var := by
        have h1 : HasFDerivAt (Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 4)))
            (Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 4))) y_var :=
          ContinuousLinearMap.hasFDerivAt _
        exact h1.smul_const M0
      rw [hfd.fderiv]
      simp [frameBasis]
    have htr0 : M0.trace = 0 := by
      simp [M0, circularConnectionMat4, chiralOffBlock4, Matrix.trace, Fin.sum_univ_four]
    have htr1 : M1.trace = 0 := by
      simp [M1, circularConnectionMat4, chiralOffBlock4, Matrix.trace, Fin.sum_univ_four]
    dsimp only [continuumCurvature]
    change (fderiv ℝ (fun z => A_var z 1) y_var (frameBasis 0) -
        fderiv ℝ (fun z => A_var z 0) y_var (frameBasis 1) +
        (A_var y_var 0 * A_var y_var 1 - A_var y_var 1 * A_var y_var 0)).trace = 0
    rw [hfd0, hfd1, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htr0, htr1, sub_zero,
      Matrix.trace_mul_comm (A_var y_var 0) (A_var y_var 1), sub_self, add_zero]

/-- T4-06: Complete declaration list across Baseline (85), M1 (32), M2 (30), and M3 (87). -/
private def e2eAuditDecls : Array Name :=
  #[ -- Baseline (`InfoGeometry.Lie.DoubledMinkowskiCircularChiralYangMillsBridge`) — 85 decls
     ``DoubledMinkowskiCircularChiralYangMillsBridge.CanonicalZorn
   , ``DoubledMinkowskiCircularChiralYangMillsBridge.Coordinate
   , ``DoubledMinkowskiCircularChiralYangMillsBridge.FourSpace
   , ``DoubledMinkowskiCircularChiralYangMillsBridge.KreinFrame4
   , ``circularPlusCoord
   , ``circularSignedMinusCoord
   , ``circularCoordToKreinFrame
   , ``zornToKreinFrame
   , ``zornToKreinFrame_apply
   , ``circularCoordToKreinFrame_single_0
   , ``circularCoordToKreinFrame_single_1
   , ``circularCoordToKreinFrame_single_2
   , ``circularCoordToKreinFrame_single_3
   , ``circularCoordToKreinFrame_single_4
   , ``circularCoordToKreinFrame_single_5
   , ``circularCoordToKreinFrame_single_6
   , ``circularCoordToKreinFrame_single_7
   , ``zornToKreinFrame_frame
   , ``chiralKreinForm_circularCoordToKreinFrame
   , ``chiralKreinForm_diag_eq_two_wittNorm
   , ``doubledMinkowski_krein_pauli_soldering_bridge
   , ``minkowskiEta4
   , ``minkowskiEta4_mul_self
   , ``minkowskiEta4_det
   , ``isUnit_minkowskiEta4_det
   , ``minkowski_dualConnection_unique
   , ``minkowskiEta4_mat4R_noncomm_witness
   , ``zornToKreinFrame_intertwines_uPlus
   , ``zornToKreinFrame_intertwines_uMinus
   , ``zornToKreinFrame_intertwines_chirality
   , ``signedKappa
   , ``signedKappa_involutive
   , ``circularCoordToKreinFrame_intertwines_sheetFlip
   , ``weylUpperMat
   , ``weylLowerMat
   , ``weylUpperMat_uPlus
   , ``weylUpperMat_rootPlus
   , ``weylLowerMat_uMinus
   , ``weylLowerMat_rootMinus
   , ``weylUpperMat_rootPlus_comm
   , ``chiralBoostVec
   , ``chiralVorticityVec
   , ``normSq3
   , ``weylUpperMat_mul_weylLowerMat
   , ``weylLowerMat_mul_weylUpperMat
   , ``weylChannel_commutator_eq_vorticity
   , ``weylChannel_noncomm_sheet_blocks_witness
   , ``weylUpperMat_mat2C_noncomm_witness
   , ``weylChannel_symmSection_clifford_closure
   , ``circularSheetOperator
   , ``circularCausalCoords
   , ``reconstruct_circularCausalCoords
   , ``circularSheet_tetraktys_table
   , ``chiralOffBlock4
   , ``chiralDiagBlock4
   , ``chiralProj4
   , ``chiralProj4_idempotent
   , ``chiralOffBlock4_mul
   , ``mat2R_noncomm_witness
   , ``chiralProj4_mat4R_noncomm_witness
   , ``chiralDiagBlock4_mul
   , ``chiralDiagBlock4_trace
   , ``chiralDiagBlock4_conjTranspose
   , ``conePlus_chiralOffBlock4
   , ``coneMinus_chiralOffBlock4
   , ``genPhi_chiralOffBlock4
   , ``chiralProjMat4
   , ``chiralProjMat4_idempotent
   , ``chiralProjMat4_star
   , ``circularConnectionMat4
   , ``circularConnectionMat4_mat4C_noncomm_witness
   , ``weylUpperExt
   , ``weylLowerExt
   , ``chiralExteriorProj4
   , ``circularGaugeConnection4
   , ``circularGaugeConnection4_evalScalar
   , ``circularGaugeConnection4_yang_mills_bridge
   , ``circularCurvatureMat4
   , ``circularCurvatureMat4_eq_genV
   , ``circularCurvatureMat4_eq_diagBlocks
   , ``circularCurvatureMat4_trace
   , ``circularCurvatureMat4_hilbertSchmidt_action
   , ``circularCurvatureMat4_square_trace
   , ``circularCurvatureMat4_vorticity_action_gap
   , ``circularConnection_starColimit_transport
     -- M1 (`InfoGeometry.Lie.DoubledMinkowskiGradedDifferentialBridge`) — 32 decls
   , ``InfoGeometry.Lie.mat2_exterior_noncomm_witness
   , ``InfoGeometry.Lie.mat4_exterior_noncomm_witness
   , ``InfoGeometry.Lie.chiralOffBlock4_eq_iff
   , ``InfoGeometry.Lie.matrixExteriorDerivative_chiralOffBlock4
   , ``InfoGeometry.Lie.chiralExteriorProj4_peirceGradingDeriv_offBlock
   , ``InfoGeometry.Lie.chiralOffBlock4_eigencondition_iff
   , ``InfoGeometry.Lie.circularGaugeConnection4_eigencondition_iff
   , ``InfoGeometry.Lie.circularGaugeConnection4_sq_zero_eigencondition_forces_zero
   , ``InfoGeometry.Lie.circularGradedTargetMap
   , ``InfoGeometry.Lie.circularGradedDiff
   , ``InfoGeometry.Lie.circularGradedDiff_ι
   , ``InfoGeometry.Lie.circularGradedDiff_ne_zero
   , ``InfoGeometry.Lie.circularGradedDiff_isGradedDerivation
   , ``InfoGeometry.Lie.uPlusForm
   , ``InfoGeometry.Lie.uMinusForm
   , ``InfoGeometry.Lie.circularGradedDiff_uPlusForm
   , ``InfoGeometry.Lie.circularGradedDiff_uMinusForm
   , ``InfoGeometry.Lie.circularGradedOmega
   , ``InfoGeometry.Lie.circularGradedDiff_eigencondition
   , ``InfoGeometry.Lie.circularGradedDiff_yang_mills_bridge_general
   , ``InfoGeometry.Lie.circularGradedDiff_yang_mills_bridge
   , ``InfoGeometry.Lie.circularGradedDiff_nondegenerate_witness
   , ``InfoGeometry.Lie.circularEvenMap
   , ``InfoGeometry.Lie.circularEvenDiff
   , ``InfoGeometry.Lie.circularEvenDiff_ι
   , ``InfoGeometry.Lie.circularEvenDiff_ne_zero
   , ``InfoGeometry.Lie.circularEvenOmega
   , ``InfoGeometry.Lie.circularEvenOmega_homogeneous
   , ``InfoGeometry.Lie.circularEvenDiff_eigencondition
   , ``InfoGeometry.Lie.circularEvenDiff_covariant_vanishing
   , ``InfoGeometry.Lie.circularEvenDiff_self_dual_covariant_vanishing
   , ``InfoGeometry.Lie.circularEvenDiff_nondegenerate_witness
     -- M2 (`InfoGeometry.Lie.DoubledMinkowskiLatticeContinuumLimit`) — 30 decls
   , ``InfoGeometry.Lie.Mat4C
   , ``InfoGeometry.Lie.circularLinkTransport
   , ``InfoGeometry.Lie.circularLinkTransport_continuous
   , ``InfoGeometry.Lie.latticeCovariantDiff
   , ``InfoGeometry.Lie.continuumCovariantDeriv
   , ``InfoGeometry.Lie.latticeCovariantDiff_at_zero
   , ``InfoGeometry.Lie.continuumCovariantDeriv_zero_const
   , ``InfoGeometry.Lie.continuumCovariantDeriv_abelian_const
   , ``InfoGeometry.Lie.continuumCovariantDeriv_nonabelian_const_nonzero
   , ``InfoGeometry.Lie.continuumCovariantDeriv_connection_sq_zero
   , ``InfoGeometry.Lie.tendsto_latticeCovariantDiff
   , ``InfoGeometry.Lie.wilsonPlaquette
   , ``InfoGeometry.Lie.continuumCurvature
   , ``InfoGeometry.Lie.wilsonPlaquette_diag_trivial
   , ``InfoGeometry.Lie.continuumCurvature_zero
   , ``InfoGeometry.Lie.continuumCurvature_abelian_const_zero
   , ``InfoGeometry.Lie.continuumCurvature_antisymm
   , ``InfoGeometry.Lie.tendsto_wilsonPlaquette_curvature
   , ``InfoGeometry.Lie.wilsonPlaquetteAction
   , ``InfoGeometry.Lie.continuumPlaquetteAction
   , ``InfoGeometry.Lie.continuumPlaquetteAction_nonneg
   , ``InfoGeometry.Lie.wilsonPlaquette_at_zero
   , ``InfoGeometry.Lie.tendsto_wilsonPlaquetteAction
   , ``InfoGeometry.Lie.witnessCoord
   , ``InfoGeometry.Lie.witnessCircularField
   , ``InfoGeometry.Lie.circularLattice_nonabelian_continuum_witness
   , ``InfoGeometry.Lie.circularLattice_nonabelian_continuum_smooth_witness
   , ``InfoGeometry.Lie.circularColimit_continuum_transport
   , ``InfoGeometry.Lie.diagTowerStarHom
   , ``InfoGeometry.Lie.circularColimit_continuum_transport_tailTower
     -- M3 (`InfoGeometry.Lie.DoubledMinkowskiManifoldYangMillsPDE`) — 87 decls
   , ``InfoGeometry.Lie.ChiralFiber
   , ``InfoGeometry.Lie.TrivialChiralBundle
   , ``InfoGeometry.Lie.mat4C_noncomm_witness
   , ``InfoGeometry.Lie.mat4CToRealCLM
   , ``InfoGeometry.Lie.mat4CToRealCLM_apply
   , ``InfoGeometry.Lie.mat4CToRealCLM_mul
   , ``InfoGeometry.Lie.chiralProjCLM
   , ``InfoGeometry.Lie.chiralProjCLM_idempotent
   , ``InfoGeometry.Lie.chiralBundleProjector
   , ``InfoGeometry.Lie.chiralBundleProjector_idempotent
   , ``InfoGeometry.Lie.chiralLocalBundleProjector
   , ``InfoGeometry.Lie.chiralLocalBundleProjector_idempotent
   , ``InfoGeometry.Lie.gaugeConnection
   , ``InfoGeometry.Lie.gaugeConnection_apply
   , ``InfoGeometry.Lie.chiralFiberToKreinFrame
   , ``InfoGeometry.Lie.fiberCoordEquiv
   , ``InfoGeometry.Lie.fiberKreinPairing
   , ``InfoGeometry.Lie.chiralFiberToKreinFrame_intertwines_proj
   , ``InfoGeometry.Lie.fiberKreinPairing_chiralProj_isotropic
   , ``InfoGeometry.Lie.trivialChiralConnection
   , ``InfoGeometry.Lie.mat4COneFormToBundleEnd
   , ``InfoGeometry.Lie.circularBundleConnection
   , ``InfoGeometry.Lie.circularBundleConnection_apply
   , ``InfoGeometry.Lie.instNormedAddCommGroupMat4CFormValue
   , ``InfoGeometry.Lie.instNormedSpaceMat4CFormValue
   , ``InfoGeometry.Lie.Mat4CForm
   , ``InfoGeometry.Lie.oneFormCLM
   , ``InfoGeometry.Lie.oneFormCLM_apply
   , ``InfoGeometry.Lie.mat4CCommCLM
   , ``InfoGeometry.Lie.mat4CCommCLM_apply
   , ``InfoGeometry.Lie.wedgeCommAt
   , ``InfoGeometry.Lie.wedgeCommAt_apply
   , ``InfoGeometry.Lie.wedgeComm
   , ``InfoGeometry.Lie.halfWedgeSelf
   , ``InfoGeometry.Lie.ymCurvature
   , ``InfoGeometry.Lie.covExtDeriv
   , ``InfoGeometry.Lie.halfWedgeSelf_apply
   , ``InfoGeometry.Lie.ymCurvature_apply_two
   , ``InfoGeometry.Lie.covExtDeriv_neg
   , ``InfoGeometry.Lie.bianchi_identity_ymCurvature
   , ``InfoGeometry.Lie.alternating_fourSpace_eq_plucker
   , ``InfoGeometry.Lie.hodgeStar4EuclMap
   , ``InfoGeometry.Lie.hodgeStar4Eucl
   , ``InfoGeometry.Lie.hodgeStar4EuclMap_basis_01
   , ``InfoGeometry.Lie.hodgeStar4EuclMap_basis_23
   , ``InfoGeometry.Lie.hodgeStar4EuclMap_basis_02
   , ``InfoGeometry.Lie.hodgeStar4EuclMap_basis_31
   , ``InfoGeometry.Lie.hodgeStar4EuclMap_basis_03
   , ``InfoGeometry.Lie.hodgeStar4EuclMap_basis_12
   , ``InfoGeometry.Lie.hodgeStar4EuclMap_involutive
   , ``InfoGeometry.Lie.hodgeStar4Eucl_involutive
   , ``InfoGeometry.Lie.hodgeStar4Eucl_contDiff
   , ``InfoGeometry.Lie.hodgeStar4Eucl_eq_self_iff
   , ``InfoGeometry.Lie.hodgeStar4MinkowskiMap
   , ``InfoGeometry.Lie.hodgeStar4Minkowski
   , ``InfoGeometry.Lie.hodgeStar4MinkowskiMap_basis_01
   , ``InfoGeometry.Lie.hodgeStar4MinkowskiMap_basis_23
   , ``InfoGeometry.Lie.hodgeStar4MinkowskiMap_basis_02
   , ``InfoGeometry.Lie.hodgeStar4MinkowskiMap_basis_31
   , ``InfoGeometry.Lie.hodgeStar4MinkowskiMap_basis_03
   , ``InfoGeometry.Lie.hodgeStar4MinkowskiMap_basis_12
   , ``InfoGeometry.Lie.hodgeStar4MinkowskiMap_sq_neg
   , ``InfoGeometry.Lie.hodgeStar4Minkowski_sq_neg
   , ``InfoGeometry.Lie.hodgeStar4Minkowski_contDiff
   , ``InfoGeometry.Lie.YangMillsPDE
   , ``InfoGeometry.Lie.YangMillsPDEMinkowski
   , ``InfoGeometry.Lie.IsSelfDualForm4
   , ``InfoGeometry.Lie.IsAntiSelfDualForm4
   , ``InfoGeometry.Lie.selfDual_solves_yangMillsPDE
   , ``InfoGeometry.Lie.antiSelfDual_solves_yangMillsPDE
   , ``InfoGeometry.Lie.circularSelfDualCoords
   , ``InfoGeometry.Lie.circularGaugeOneFormCLM
   , ``InfoGeometry.Lie.circularGaugeOneForm
   , ``InfoGeometry.Lie.circularGaugeForm
   , ``InfoGeometry.Lie.circularGaugeForm_contDiff
   , ``InfoGeometry.Lie.circularGaugeForm_apply_basis
   , ``InfoGeometry.Lie.circularGaugeForm_mat4C_noncomm_witness
   , ``InfoGeometry.Lie.circularGaugeForm_ymCurvature_ne_zero
   , ``InfoGeometry.Lie.circularGaugeForm_isSelfDual
   , ``InfoGeometry.Lie.circularGaugeForm_solves_yangMillsPDE
   , ``InfoGeometry.Lie.circularSelfDualExtOmega
   , ``InfoGeometry.Lie.circularGaugeForm_nonabelian_ym_solution
   , ``InfoGeometry.Lie.waveDirForm
   , ``InfoGeometry.Lie.waveSpatialForm
   , ``InfoGeometry.Lie.circularMinkowskiWaveForm
   , ``InfoGeometry.Lie.circularMinkowskiWaveForm_solves_yangMillsPDEMinkowski
   , ``InfoGeometry.Lie.circularMinkowskiWaveForm_ymCurvature_ne_zero ]

run_cmd do
  let policy := defaultPolicySnapshot
  let batch ← liftCoreM <| collectHardEvidenceBatch policy e2eAuditDecls
  for decl in e2eAuditDecls do
    let some ev := batch[decl]?
      | throwError "missing HardEvidence for {decl}"
    unless ev.forbiddenAxioms.isEmpty do
      throwError "forbidden axioms on {decl}: {ev.forbiddenAxioms}"
    if ev.hasSorryAx then
      throwError "unexpected sorryAx dependency on {decl}"
    if ev.unsafeLeakage then
      throwError "unexpected unsafeLeakage on {decl}"
    if ev.repDepthViolation then
      throwError "unexpected repDepthViolation on {decl}"
    if ev.forbiddenRegionKind then
      throwError "unexpected forbiddenRegionKind on {decl}"

end InfoGeometry.Lie.DoubledMinkowskiExtensionsE2ETest
