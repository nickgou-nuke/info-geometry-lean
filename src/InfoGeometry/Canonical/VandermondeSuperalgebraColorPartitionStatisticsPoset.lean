/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.CorrelationSymmetrization
import InfoGeometry.Canonical.CorrelationAntisymmetrization
import InfoGeometry.Canonical.GLSupermatrixGradedLie
import InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus
import InfoGeometry.Canonical.Z3TrialityCapstone
import InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock
import InfoGeometry.Arithmetic.MobiusWittenWeylDenominator
import InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge
import InfoGeometry.Canonical.VandermondeExclusionBridge
import InfoGeometry.Canonical.LaughlinStateQuantumHallBridge
import InfoGeometry.Canonical.BerezinFermionicIntegrationBridge
import InfoGeometry.Canonical.WeylCharacterThetaBridge
import InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow
import InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow
import InfoGeometry.Supergeometry.BerezinianDecomposition
import InfoGeometry.Canonical.CattoGurseyBlockGrading
import InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-!
# Vandermonde, superalgebra, color, and partition-statistics synthesis

This owner records the typed progression of Stream VI and proves one new
cross-lane theorem: on the cubic moment curve `(1,t,t²)`, the existing
supercolor baryon determinant is the existing Mathlib Vandermonde determinant.
Consequently its vanishing is exactly the node-collision condition. The
remaining components are referenced from their owning modules with their
original carriers and hypotheses; this file does not identify distinct
algebras or promote supplied structure fields into constructed facts.
-/

noncomputable section

namespace InfoGeometry.Canonical.VandermondeSuperalgebraColorPartitionStatisticsPoset

open InfoGeometry.Canonical.VandermondeExclusionBridge
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Superalgebra.PeirceDeWittZornQuantization

/-! ## The color moment curve and Vandermonde exclusion bridge -/

variable {R : Type*} [CommRing R]

/-- The three-color point on the quadratic moment curve. -/
def colorMomentCurve (t : R) : ColorVec3 R := ⟨1, t, t ^ 2⟩

/-- The node sequence used by the `3 × 3` Vandermonde matrix. -/
def momentNodes (t₁ t₂ t₃ : R) : Fin 3 → R
  | 0 => t₁
  | 1 => t₂
  | 2 => t₃

/-- The color baryon singlet on the quadratic moment curve is the ordinary
three-node Vandermonde product, with the source owners' fixed orientation. -/
theorem baryonDet_colorMomentCurve_eq_vandermonde_product
    (t₁ t₂ t₃ : R) :
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂)
        (colorMomentCurve t₃) =
      (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) := by
  simp [ColorVec3.baryonDet, ColorVec3.dot, ColorVec3.cross, colorMomentCurve]
  ring

/-- The supercolor baryon singlet equals the determinant of Mathlib's actual
`Fin 3` Vandermonde matrix on the moment nodes. -/
theorem baryonDet_colorMomentCurve_eq_vandermonde_determinant
    (t₁ t₂ t₃ : R) :
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂)
        (colorMomentCurve t₃) =
      FiniteVandermondeExclusionWitness.determinant (momentNodes t₁ t₂ t₃) := by
  rw [baryonDet_colorMomentCurve_eq_vandermonde_product]
  simp only [FiniteVandermondeExclusionWitness.determinant,
    FiniteVandermondeExclusionWitness.matrix, Matrix.det_fin_three,
    Matrix.vandermonde_apply, momentNodes]
  norm_num
  ring

/-- On the moment curve, the baryon singlet vanishes exactly when two of the
three spectral nodes collide. This reuses the domain-sensitive Vandermonde
collision theorem rather than assuming nonzero determinant or positivity. -/
theorem baryonDet_colorMomentCurve_eq_zero_iff_collision
    [IsDomain R] (t₁ t₂ t₃ : R) :
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂)
        (colorMomentCurve t₃) = 0 ↔
      ∃ i j : Fin 3, momentNodes t₁ t₂ t₃ i = momentNodes t₁ t₂ t₃ j ∧ i ≠ j := by
  rw [baryonDet_colorMomentCurve_eq_vandermonde_determinant]
  exact FiniteVandermondeExclusionWitness.determinant_eq_zero_iff_collision
    (momentNodes t₁ t₂ t₃)

/-- On the integral-domain carrier, the moment-curve color baryon is nonzero
exactly when its three spectral parameters are pairwise distinct. This makes
the collision criterion explicit in the color coordinates. -/
theorem baryonDet_colorMomentCurve_ne_zero_iff_pairwise_ne
    [IsDomain R] (t₁ t₂ t₃ : R) :
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂)
        (colorMomentCurve t₃) ≠ 0 ↔
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ := by
  rw [baryonDet_colorMomentCurve_eq_vandermonde_determinant]
  rw [FiniteVandermondeExclusionWitness.determinant_ne_zero_iff_injective]
  constructor
  · intro hinj
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have he : momentNodes t₁ t₂ t₃ 0 = momentNodes t₁ t₂ t₃ 1 := by
        simp [momentNodes, h]
      exact Fin.zero_ne_one (hinj he)
    · intro h
      have he : momentNodes t₁ t₂ t₃ 0 = momentNodes t₁ t₂ t₃ 2 := by
        simp [momentNodes, h]
      exact (by decide : (0 : Fin 3) ≠ 2) (hinj he)
    · intro h
      have he : momentNodes t₁ t₂ t₃ 1 = momentNodes t₁ t₂ t₃ 2 := by
        simp [momentNodes, h]
      exact (by decide : (1 : Fin 3) ≠ 2) (hinj he)
  · rintro ⟨h12, h13, h23⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [momentNodes]

/-! ## Existing-owner route theorems -/

/-- Stream VI starts with the genuine two-state channel split and its
phase-linear antisymmetric specialization. -/
theorem streamVI_correlation_split_route
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (reference comparison : InfoGeometry.Krein.DoubledSpace E)
    (X Y : InfoGeometry.Canonical.RelationalInformationCore.PerturbationChannel E)
    (hX : IsPhaseLinear (E := E) X)
    (hY : IsPhaseLinear (E := E) Y) :
    (InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation
        (E := E) reference comparison X Y =
      InfoGeometry.Canonical.CorrelationSymmetrization.symmetricTwoStateChannelCorrelation
        (E := E) reference comparison X Y +
      InfoGeometry.Canonical.CorrelationSymmetrization.antisymmetricTwoStateChannelCorrelation
        (E := E) reference comparison X Y) ∧
    (InfoGeometry.Canonical.CorrelationAntisymmetrization.symmetricPhaseShiftedTwoStateChannelCorrelation
        (E := E) comparison comparison X Y = 0) := by
  exact ⟨
    InfoGeometry.Canonical.CorrelationSymmetrization.twoStateChannelCorrelation_eq_symmetric_add_antisymmetric
      reference comparison X Y,
    InfoGeometry.Canonical.CorrelationAntisymmetrization.symmetricPhaseShiftedTwoStateChannelCorrelation_self_eq_zero_of_IsPhaseLinear
      comparison X Y hX hY⟩

/-- The color collision theorem and its hypotheses are exposed as a reusable
terminal bridge for the supercolor/Vandermonde lanes. -/
theorem streamVI_color_exclusion_route [IsDomain R] (t₁ t₂ t₃ : R) :
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂)
        (colorMomentCurve t₃) =
      FiniteVandermondeExclusionWitness.determinant (momentNodes t₁ t₂ t₃) ∧
    (ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂)
        (colorMomentCurve t₃) = 0 ↔
      ∃ i j : Fin 3, momentNodes t₁ t₂ t₃ i = momentNodes t₁ t₂ t₃ j ∧ i ≠ j) := by
  exact ⟨baryonDet_colorMomentCurve_eq_vandermonde_determinant t₁ t₂ t₃,
    baryonDet_colorMomentCurve_eq_zero_iff_collision t₁ t₂ t₃⟩

/-- The first route is the already-proved graded Jacobi theorem on the actual
`gl(m|n)` supermatrix carrier. -/
abbrev streamVI_gl_super_jacobi_route :=
  @InfoGeometry.Canonical.GLSupermatrixGradedLie.gl_graded_super_jacobi

/-- On the native homogeneous block carrier, the supertrace annihilates the
superbracket; homogeneity is retained as an explicit premise. -/
theorem streamVI_supertrace_superbracket_route
    {m n : ℕ} {R : Type*} [CommRing R]
    (p q : InfoGeometry.Canonical.GLSupermatrixGradedLie.Parity)
    (X Y : InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix m n R)
    (hX : InfoGeometry.Canonical.GLSupermatrixGradedLie.IsHomogeneous p X)
    (hY : InfoGeometry.Canonical.GLSupermatrixGradedLie.IsHomogeneous q Y) :
    InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace
      (InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket p q X Y) = 0 :=
  InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace_superbracket_eq_zero
    p q X Y hX hY

/-- Existing source route for the `Z₃` plane and cubic graded differential. -/
theorem streamVI_z3_substrate_route
    {A : Type*} [MonoidWithZero A] (P : InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus.Z3QuantumPlane A)
    {B : Type*} [Zero B] [Add B] [Mul B]
    (D : InfoGeometry.Canonical.Z3GrassmannDifferentialCalculus.Z3DifferentialCalculus B)
    (x y : B) :
    (P.omega ^ 3 = 1 ∧ P.theta1 ^ 3 = 0 ∧ P.theta2 ^ 3 = 0 ∧
      P.theta1 * P.theta2 = P.omega * (P.theta2 * P.theta1)) ∧
    (D.d (D.d (D.d x)) = 0 ∧
      D.d (x * y) = D.d x * y + D.omegaPow (D.degree x) * (x * D.d y)) := by
  exact ⟨InfoGeometry.Canonical.Z3TrialityCapstone.z3_quantum_plane_substrate_packet P,
    InfoGeometry.Canonical.Z3TrialityCapstone.z3_grassmann_differential_substrate_packet D x y⟩

/-- The `κ=2` and `κ=3` local partition factors are the native finite
geometric sums for fermions and order-three parafermions. -/
theorem streamVI_local_partition_route (x : ℝ) :
    InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock.parafermionLocalFactor 2 x = 1 + x ∧
    InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock.parafermionLocalFactor 3 x = 1 + x + x ^ 2 := by
  exact ⟨InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock.parafermionLocalFactor_two x,
    InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock.parafermionLocalFactor_three x⟩

/-- The finite occupation cutoffs converge to the bosonic geometric factor
under the actual summability hypothesis `|x| < 1`. -/
theorem streamVI_bosonic_limit_route (x : ℝ) (hx : |x| < 1) :
    Filter.Tendsto
      (fun κ : ℕ =>
        InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock.parafermionLocalFactor κ x)
      Filter.atTop (nhds ((1 - x)⁻¹)) :=
  InfoGeometry.Canonical.PrimeParafermionGrandCanonicalClock.tendsto_parafermionLocalFactor_atTop x hx

/-- The existing one-mode Berezin contraction evaluates a one-particle state
at the selected covector. -/
theorem streamVI_berezin_contraction_route
    {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (u : U) (alpha : U →ₗ[R] R) :
    InfoGeometry.Canonical.BerezinFermionicIntegrationBridge.berezinIntegralOp u
        (InfoGeometry.Canonical.SingleParticleFockStateBridge.singleParticleState alpha) =
      alpha u • InfoGeometry.Canonical.FockVacuumAnnihilationBridge.vacuumState R U :=
  InfoGeometry.Canonical.BerezinFermionicIntegrationBridge.berezin_integral_single_particle u alpha

/-- Tripotent triality projectors are obtained conditionally from an explicit
operator equation `O^3 = O`. -/
theorem streamVI_tripotent_route
    {Vspace : Type*} [AddCommGroup Vspace] [Module ℝ Vspace]
    (O : InfoGeometry.Algebra.OSp12.Op Vspace) (hO : O ^ 3 = O) :
    InfoGeometry.Algebra.OSp12.projVac O * InfoGeometry.Algebra.OSp12.projVac O =
        InfoGeometry.Algebra.OSp12.projVac O ∧
      InfoGeometry.Algebra.OSp12.projUp O * InfoGeometry.Algebra.OSp12.projUp O =
        InfoGeometry.Algebra.OSp12.projUp O ∧
      InfoGeometry.Algebra.OSp12.projDown O * InfoGeometry.Algebra.OSp12.projDown O =
        InfoGeometry.Algebra.OSp12.projDown O ∧
      InfoGeometry.Algebra.OSp12.projVac O + InfoGeometry.Algebra.OSp12.projUp O +
          InfoGeometry.Algebra.OSp12.projDown O = 1 := by
  exact ⟨(InfoGeometry.Canonical.Z3TrialityCapstone.hadjiivanov_tripotent_projector_packet
    O hO).1,
    (InfoGeometry.Canonical.Z3TrialityCapstone.hadjiivanov_tripotent_projector_packet
      O hO).2.1,
    (InfoGeometry.Canonical.Z3TrialityCapstone.hadjiivanov_tripotent_projector_packet
      O hO).2.2.1,
    (InfoGeometry.Canonical.Z3TrialityCapstone.hadjiivanov_tripotent_projector_packet
      O hO).2.2.2.1⟩

/-- Finite Möbius, Weyl-denominator, and Witten-supertrace identities, with
the nonzero local-factor premise retained for boson cancellation. -/
theorem streamVI_finite_witten_weyl_route
    (P : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q : ℕ → ℂ)
    (h : ∀ p ∈ P.primes, (1 : ℂ) - q p ≠ 0) :
    InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P q =
        InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeWeylDenominator P.primes q ∧
      InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P q =
        InfoGeometry.Arithmetic.PrimonFinite.STrF P.primes q ∧
      InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeBosonicInverseDenominator P.primes q *
        InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial P q = 1 :=
  InfoGeometry.Arithmetic.MobiusWittenWeylDenominator.finite_mobius_witten_weyl_packet P q h

/-- The existing `V₄` Fourier inversion is reused on a finite nonempty state
type with its explicit grading and thermodynamic parameters. -/
theorem streamVI_v4_fourier_route
    {α : Type*} [Fintype α] [Nonempty α]
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α)
    (grade : α → InfoGeometry.Topology.V4RootSystem.V4Group)
    (β μ : ℝ) (g : InfoGeometry.Topology.V4RootSystem.V4Group) :
    (1 / 4 : ℝ) *
        ∑ k : Fin 4,
          InfoGeometry.Canonical.V4GroupFourierTransform.v4Character k g *
            InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge.v4TwistedPartition
              params grade β μ k =
      InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge.v4SectorPartition
        params grade β μ g :=
  InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge.v4Fourier_sector_inversion
    params grade β μ g

/-- The A₂ Weyl shadow is its proved alternating packet under the basic
transposition. -/
theorem streamVI_weyl_a2_route
    (C : InfoGeometry.Canonical.WeylA2AlternatingDeterminantShadow.Chart) :
    C.swap01.alternatingDenominatorFactor = -C.alternatingDenominatorFactor ∧
      C.swap01.alternatingNumeratorFactor = -C.alternatingNumeratorFactor :=
  C.alternating_determinant_packet

/-- The rank-one `SU(2)` Weyl denominator identity is retained alongside the
three-node `A₂` alternating factor. -/
theorem streamVI_weyl_a1_route (θ : ℝ) :
    Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ)) =
      2 * Complex.I * (Real.sin θ : ℂ) :=
  InfoGeometry.Canonical.WeylCharacterThetaBridge.weyl_denominator_su2 θ

/-- The proved Weyl polynomial divisibility route is the two-node statement
owned by the polynomial shadow module. -/
theorem streamVI_weyl_two_node_divisibility_route
    {S : Type*} [CommRing S]
    (P : InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow.TwoNodePolynomialShadow S) :
    P.denominator ∣ P.numerator :=
  P.denominator_dvd_numerator

/-- The existing Laughlin owner supplies these finite numeric readouts. -/
theorem streamVI_laughlin_numeric_route
    (L : QuantumHall.LaughlinState) (e : ℝ) :
    0 < L.fillingFactor ∧
      L.quasiHoleCharge e * (L.m : ℝ) = e ∧
      0 < L.anyonBraidPhase :=
  ⟨L.filling_factor_pos, L.quasi_hole_charge_mult e, L.anyon_braid_phase_pos⟩

/-- The corrected `gl(6|21)` carrier has supertrace `-15` on its identity. -/
theorem streamVI_color_supertrace_route {R : Type*} [CommRing R] :
    InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace
        (1 : InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix 6 21 R) = -15 :=
  InfoGeometry.Canonical.CattoGurseyBlockGrading.supertrace_identity_6_21

/-! ## The 8-Stage Acyclic Causal Poset (`𝔙₁ ≺ 𝔙₂ ≺ ⋯ ≺ 𝔙₈`) -/

/-- The 8-stage causal poset of Stream VI: Vandermonde, Superalgebras, Color
Superalgebras, and Partition Statistics (`𝔙₁ ≺ 𝔙₂ ≺ ⋯ ≺ 𝔙₈`). -/
inductive VandermondeSuperalgebraColorPartitionStage : Type
  | V1_TwoStateExchangeCorrelationSplit
  | V2_Z2KoszulSuperLieAndBerezinCalculus
  | V3_Z3TernaryQuantumPlaneAndTriality
  | V4_CyclotomicPartitionWittenAndV4Fourier
  | V5_VandermondeExclusionAndLaughlinBraiding
  | V6_WeylA1A2DenominatorAndDivisibility
  | V7_SuperLUSchurFactorizationAndBerezinian
  | V8_CattoGurseySuperalgebraAndMomentCurveBaryon
  deriving DecidableEq, Repr, Inhabited

namespace VandermondeSuperalgebraColorPartitionStage

/-- Strictly monotone integer rank `0..7` witnessing `𝔙₁ ≺ 𝔙₂ ≺ ⋯ ≺ 𝔙₈`. -/
def rank : VandermondeSuperalgebraColorPartitionStage → ℕ
  | .V1_TwoStateExchangeCorrelationSplit => 0
  | .V2_Z2KoszulSuperLieAndBerezinCalculus => 1
  | .V3_Z3TernaryQuantumPlaneAndTriality => 2
  | .V4_CyclotomicPartitionWittenAndV4Fourier => 3
  | .V5_VandermondeExclusionAndLaughlinBraiding => 4
  | .V6_WeylA1A2DenominatorAndDivisibility => 5
  | .V7_SuperLUSchurFactorizationAndBerezinian => 6
  | .V8_CattoGurseySuperalgebraAndMomentCurveBaryon => 7

theorem rank_injective : Function.Injective rank := by
  intro x y h
  cases x <;> cases y <;> revert h <;> decide

instance instLinearOrderVandermondeSuperalgebraColorPartitionStage :
    LinearOrder VandermondeSuperalgebraColorPartitionStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal edges of the Stream VI poset (`𝔙₁ → 𝔙₂, 𝔙₃ → 𝔙₄ → 𝔙₅, 𝔙₆ → 𝔙₇ → 𝔙₈`). -/
def causalEdge :
    VandermondeSuperalgebraColorPartitionStage →
    VandermondeSuperalgebraColorPartitionStage → Prop
  | .V1_TwoStateExchangeCorrelationSplit, .V2_Z2KoszulSuperLieAndBerezinCalculus => True
  | .V1_TwoStateExchangeCorrelationSplit, .V3_Z3TernaryQuantumPlaneAndTriality => True
  | .V2_Z2KoszulSuperLieAndBerezinCalculus, .V3_Z3TernaryQuantumPlaneAndTriality => True
  | .V2_Z2KoszulSuperLieAndBerezinCalculus, .V4_CyclotomicPartitionWittenAndV4Fourier => True
  | .V3_Z3TernaryQuantumPlaneAndTriality, .V4_CyclotomicPartitionWittenAndV4Fourier => True
  | .V4_CyclotomicPartitionWittenAndV4Fourier, .V5_VandermondeExclusionAndLaughlinBraiding => True
  | .V4_CyclotomicPartitionWittenAndV4Fourier, .V6_WeylA1A2DenominatorAndDivisibility => True
  | .V5_VandermondeExclusionAndLaughlinBraiding, .V6_WeylA1A2DenominatorAndDivisibility => True
  | .V5_VandermondeExclusionAndLaughlinBraiding, .V7_SuperLUSchurFactorizationAndBerezinian => True
  | .V6_WeylA1A2DenominatorAndDivisibility, .V7_SuperLUSchurFactorizationAndBerezinian => True
  | .V7_SuperLUSchurFactorizationAndBerezinian, .V8_CattoGurseySuperalgebraAndMomentCurveBaryon => True
  | _, _ => False

instance instDecidableRelCausalEdge : DecidableRel causalEdge := by
  intro a b
  cases a <;> cases b <;> unfold causalEdge <;> infer_instance

theorem causalEdge_strict_rank_mono {a b : VandermondeSuperalgebraColorPartitionStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> revert h <;> decide

theorem causalEdge_irrefl (a : VandermondeSuperalgebraColorPartitionStage) :
    ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

theorem transGen_causalEdge_strict_rank_mono {a b : VandermondeSuperalgebraColorPartitionStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (causalEdge_strict_rank_mono hbc)

theorem causalEdge_acyclic (a : VandermondeSuperalgebraColorPartitionStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

theorem strict_eight_stage_chain :
    VandermondeSuperalgebraColorPartitionStage.V1_TwoStateExchangeCorrelationSplit <
      .V2_Z2KoszulSuperLieAndBerezinCalculus ∧
    VandermondeSuperalgebraColorPartitionStage.V2_Z2KoszulSuperLieAndBerezinCalculus <
      .V3_Z3TernaryQuantumPlaneAndTriality ∧
    VandermondeSuperalgebraColorPartitionStage.V3_Z3TernaryQuantumPlaneAndTriality <
      .V4_CyclotomicPartitionWittenAndV4Fourier ∧
    VandermondeSuperalgebraColorPartitionStage.V4_CyclotomicPartitionWittenAndV4Fourier <
      .V5_VandermondeExclusionAndLaughlinBraiding ∧
    VandermondeSuperalgebraColorPartitionStage.V5_VandermondeExclusionAndLaughlinBraiding <
      .V6_WeylA1A2DenominatorAndDivisibility ∧
    VandermondeSuperalgebraColorPartitionStage.V6_WeylA1A2DenominatorAndDivisibility <
      .V7_SuperLUSchurFactorizationAndBerezinian ∧
    VandermondeSuperalgebraColorPartitionStage.V7_SuperLUSchurFactorizationAndBerezinian <
      .V8_CattoGurseySuperalgebraAndMomentCurveBaryon := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end VandermondeSuperalgebraColorPartitionStage

/-! ## Axiom I & Rung 0–1: Socratic Supertrace Aporia, Grassmann Berezin
    Derivative-Integration, & `ℤ₃` Ternary `q`-Binomial Cube Law (`𝔙₁ ≺ 𝔙₂ ≺ 𝔙₃`) -/

/-- **Lemma 1a (The Socratic Supercommutator Trace Aporia vs. Supertrace Invariance — `𝔙₂`)**:
For two odd supermatrices `oddMatrix B₁ C₁` and `oddMatrix B₂ C₂` in `SuperMatrix m n R`:
1. Their odd-odd superbracket `superbracket .odd .odd` is `evenMatrix (B₁ * C₂ + B₂ * C₁) (C₁ * B₂ + C₂ * B₁)`,
2. Its **ordinary matrix trace** equals `2 * Matrix.trace (B₁ * C₂ + B₂ * C₁)` (and on `SuperMatrix 1 1 ℤ`
   with `B₁ = 1, C₂ = 1, B₂ = 0, C₁ = 0`, the ordinary trace is `2 ≠ 0`),
3. Its **supertrace** vanishes identically (`GLSupermatrixGradedLie.supertrace = 0`) because
   `Tr(B₁ C₂ + B₂ C₁) - Tr(C₁ B₂ + C₂ B₁) = 0`. -/
theorem odd_superbracket_ordinary_trace_vs_supertrace
    {m n : ℕ} {R : Type*} [CommRing R]
    (B₁ B₂ : Matrix (Fin m) (Fin n) R) (C₁ C₂ : Matrix (Fin n) (Fin m) R) :
    Matrix.trace
        (InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket .odd .odd
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix B₁ C₁)
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix B₂ C₂)) =
      2 * Matrix.trace (B₁ * C₂ + B₂ * C₁) ∧
    InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace
        (InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket .odd .odd
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix B₁ C₁)
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix B₂ C₂)) = 0 ∧
    Matrix.trace
        (InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket .odd .odd
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix
            (1 : Matrix (Fin 1) (Fin 1) ℤ) (0 : Matrix (Fin 1) (Fin 1) ℤ))
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix
            (0 : Matrix (Fin 1) (Fin 1) ℤ) (1 : Matrix (Fin 1) (Fin 1) ℤ))) = 2 := by
  have hBr :
      InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket .odd .odd
        (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix B₁ C₁)
        (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix B₂ C₂) =
      InfoGeometry.Canonical.GLSupermatrixGradedLie.evenMatrix
        (B₁ * C₂ + B₂ * C₁) (C₁ * B₂ + C₂ * B₁) :=
    InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket_odd_odd B₁ B₂ C₁ C₂
  have hTr :
      Matrix.trace
        (InfoGeometry.Canonical.GLSupermatrixGradedLie.evenMatrix
          (B₁ * C₂ + B₂ * C₁) (C₁ * B₂ + C₂ * B₁)) =
      2 * Matrix.trace (B₁ * C₂ + B₂ * C₁) := by
    have hE :
        Matrix.trace
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.evenMatrix
            (B₁ * C₂ + B₂ * C₁) (C₁ * B₂ + C₂ * B₁)) =
        Matrix.trace (B₁ * C₂ + B₂ * C₁) + Matrix.trace (C₁ * B₂ + C₂ * B₁) := by
      simp [Matrix.trace, Matrix.diag,
        InfoGeometry.Canonical.GLSupermatrixGradedLie.evenMatrix]
    rw [hE, Matrix.trace_add, Matrix.trace_add,
        Matrix.trace_mul_comm C₁ B₂, Matrix.trace_mul_comm C₂ B₁]
    ring
  have hSTr :
      InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace
        (InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket .odd .odd
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix B₁ C₁)
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix B₂ C₂)) = 0 :=
    InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace_superbracket_eq_zero
      .odd .odd _ _ ⟨B₁, C₁, rfl⟩ ⟨B₂, C₂, rfl⟩
  have hWitness :
      Matrix.trace
        (InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket .odd .odd
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix
            (1 : Matrix (Fin 1) (Fin 1) ℤ) (0 : Matrix (Fin 1) (Fin 1) ℤ))
          (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix
            (0 : Matrix (Fin 1) (Fin 1) ℤ) (1 : Matrix (Fin 1) (Fin 1) ℤ))) = 2 := by
    rw [InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket_odd_odd]
    simp [Matrix.trace, Matrix.diag,
      InfoGeometry.Canonical.GLSupermatrixGradedLie.evenMatrix]
  exact ⟨by rw [hBr, hTr], hSTr, hWitness⟩

/-- One-generator Grassmann numbers `R[θ]/(θ²)` represented on `R × R` as `(a, b) = a + bθ`. -/
def grassmannMul (x y : R × R) : R × R :=
  (x.1 * y.1, x.1 * y.2 + x.2 * y.1)

/-- The odd Grassmann generator `θ = (0, 1)`. -/
def grassmannTheta : R × R := (0, 1)

/-- Berezin integral `∫ dθ (a + bθ) = b`. -/
def berezinIntegral1 (f : R × R) : R := f.2

/-- Left Grassmann derivative `∂_θ (a + bθ) = (b, 0)` viewed in `R[θ]/(θ²)`, with scalar readout `b`. -/
def grassmannDeriv1 (f : R × R) : R × R := (f.2, 0)

/-- **Lemma 1b (Grassmann Square-Zero Nilpotency & Berezin Derivative-Integration Identity — `𝔙₂`)**:
On `R[θ]/(θ²)`:
1. `θ² = grassmannMul θ θ = (0, 0)`,
2. `(a, 0) + grassmannMul (b, 0) θ = (a, b)`,
3. The Berezin integral `∫ dθ (a + bθ) = b` equals the scalar part of `∂_θ (a + bθ) = (b, 0)`,
4. Integration by parts without boundary terms: `∫ dθ (∂_θ f) = 0`. -/
theorem grassmann_berezin_integral_eq_derivative (a b : R) (f : R × R) :
    grassmannMul (grassmannTheta (R := R)) (grassmannTheta (R := R)) = (0, 0) ∧
    ((a, (0 : R)) + grassmannMul (b, 0) (grassmannTheta (R := R)) = (a, b)) ∧
    berezinIntegral1 (a, b) = (grassmannDeriv1 (a, b)).1 ∧
    berezinIntegral1 (grassmannDeriv1 f) = 0 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · ext <;> simp [grassmannMul, grassmannTheta]
  · ext <;> simp [grassmannMul, grassmannTheta]

/-- **Theorem 1 (`ℤ₃` Ternary `q`-Binomial Cube Law `(A + B)³ = A³ + B³` — `𝔙₃`)**:
In any associative ring `B_ring` with central element `ω` (`ω * A = A * ω`, `ω * B = B * ω`)
satisfying the 3rd cyclotomic relation `1 + ω + ω ^ 2 = 0` and the `ℤ₃` braiding law
`A * B = ω * (B * A)`:
1. `ω ^ 3 = 1`,
2. `(A + B) ^ 2 = A ^ 2 + (1 + ω) * (B * A) + B ^ 2`,
3. `(A + B) ^ 3 = A ^ 3 + B ^ 3`,
4. If `A ^ 3 = 0` and `B ^ 3 = 0` (cube-zero nilpotency), then `(A + B) ^ 3 = 0`. -/
theorem z3_q_binomial_cube_law
    {B_ring : Type*} [Ring B_ring]
    (ω A B : B_ring)
    (hωA : ω * A = A * ω) (hωB : ω * B = B * ω)
    (hbraid : A * B = ω * (B * A))
    (hcyc : 1 + ω + ω ^ 2 = 0) :
    ω ^ 3 = 1 ∧
    (A + B) ^ 2 = A ^ 2 + (1 + ω) * (B * A) + B ^ 2 ∧
    (A + B) ^ 3 = A ^ 3 + B ^ 3 ∧
    (A ^ 3 = 0 → B ^ 3 = 0 → (A + B) ^ 3 = 0) := by
  have hω3 : ω ^ 3 = 1 := by
    calc
      ω ^ 3 = (ω - 1) * (1 + ω + ω ^ 2) + 1 := by noncomm_ring
      _ = (ω - 1) * 0 + 1 := by rw [hcyc]
      _ = 1 := by simp
  have hSq : (A + B) ^ 2 = A ^ 2 + (1 + ω) * (B * A) + B ^ 2 := by
    calc
      (A + B) ^ 2 = A * A + A * B + B * A + B * B := by noncomm_ring
      _ = A * A + ω * (B * A) + B * A + B * B := by rw [hbraid]
      _ = A ^ 2 + (1 + ω) * (B * A) + B ^ 2 := by noncomm_ring
  have hABA : A * (B * A) = ω * (B * (A * A)) := by
    calc
      A * (B * A) = (A * B) * A := by noncomm_ring
      _ = (ω * (B * A)) * A := by rw [hbraid]
      _ = ω * (B * (A * A)) := by noncomm_ring
  have hA2B : A * (A * B) = ω ^ 2 * (B * (A * A)) := by
    calc
      A * (A * B) = A * (ω * (B * A)) := by rw [hbraid]
      _ = (A * ω) * (B * A) := by noncomm_ring
      _ = (ω * A) * (B * A) := by rw [← hωA]
      _ = ω * (A * (B * A)) := by noncomm_ring
      _ = ω * (ω * (B * (A * A))) := by rw [hABA]
      _ = ω ^ 2 * (B * (A * A)) := by noncomm_ring
  have hBAB : B * (A * B) = ω * (B * (B * A)) := by
    calc
      B * (A * B) = B * (ω * (B * A)) := by rw [hbraid]
      _ = (B * ω) * (B * A) := by noncomm_ring
      _ = (ω * B) * (B * A) := by rw [← hωB]
      _ = ω * (B * (B * A)) := by noncomm_ring
  have hAB2 : (A * B) * B = ω ^ 2 * (B * (B * A)) := by
    calc
      (A * B) * B = (ω * (B * A)) * B := by rw [hbraid]
      _ = ω * (B * (A * B)) := by noncomm_ring
      _ = ω * (ω * (B * (B * A))) := by rw [hBAB]
      _ = ω ^ 2 * (B * (B * A)) := by noncomm_ring
  have hCube : (A + B) ^ 3 = A ^ 3 + B ^ 3 := by
    calc
      (A + B) ^ 3 =
          A ^ 3 + A * (A * B) + A * (B * A) + B * (A * A) +
            (A * B) * B + B * (A * B) + B * (B * A) + B ^ 3 := by noncomm_ring
      _ = A ^ 3 + ω ^ 2 * (B * (A * A)) + ω * (B * (A * A)) + B * (A * A) +
            ω ^ 2 * (B * (B * A)) + ω * (B * (B * A)) + B * (B * A) + B ^ 3 := by
            rw [hA2B, hABA, hAB2, hBAB]
      _ = A ^ 3 + (1 + ω + ω ^ 2) * (B * (A * A)) +
            (1 + ω + ω ^ 2) * (B * (B * A)) + B ^ 3 := by noncomm_ring
      _ = A ^ 3 + 0 * (B * (A * A)) + 0 * (B * (B * A)) + B ^ 3 := by rw [hcyc]
      _ = A ^ 3 + B ^ 3 := by noncomm_ring
  refine ⟨hω3, hSq, hCube, ?_⟩
  intro hA3 hB3
  rw [hCube, hA3, hB3, add_zero]

/-! ## Deduction 1: Cyclotomic Partition Quotients & `ℤ₃` Color Singlet Confinement (`𝔙₄`) -/

/-- Universal truncated geometric partition polynomial `Q_κ(x) = ∑_{j < κ} x^j` over any ring. -/
def truncatedPartitionPoly {S : Type*} [Semiring S] (κ : ℕ) (x : S) : S :=
  ∑ j ∈ Finset.range κ, x ^ j

/-- **Theorem 2 (Cyclotomic Partition Quotients, Fermion/Parafermion Identities, & Color Confinement — `𝔙₄`)**:
In any commutative ring `R`:
1. `(1 - x) * truncatedPartitionPoly κ x = 1 - x ^ κ`,
2. Fermionic `κ = 2` factor: `truncatedPartitionPoly 2 x = 1 + x` and `(1 - x) * (1 + x) = 1 - x ^ 2`,
3. Parafermionic `κ = 3` factor: `truncatedPartitionPoly 3 x = 1 + x + x ^ 2` and
   `(1 - x) * (1 + x + x ^ 2) = 1 - x ^ 3`,
4. At any primitive cube root `ω` satisfying `1 + ω + ω ^ 2 = 0`, the `κ = 3` color partition
   factor vanishes (`truncatedPartitionPoly 3 ω = 0`). -/
theorem cyclotomic_partition_quotient_and_color_confinement
    (κ : ℕ) (x ω : R) (hω : 1 + ω + ω ^ 2 = 0) :
    (1 - x) * truncatedPartitionPoly κ x = 1 - x ^ κ ∧
    truncatedPartitionPoly 2 x = 1 + x ∧
    (1 - x) * truncatedPartitionPoly 2 x = 1 - x ^ 2 ∧
    truncatedPartitionPoly 3 x = 1 + x + x ^ 2 ∧
    (1 - x) * truncatedPartitionPoly 3 x = 1 - x ^ 3 ∧
    truncatedPartitionPoly 3 ω = 0 := by
  have hGeom : (1 - x) * truncatedPartitionPoly κ x = 1 - x ^ κ := by
    unfold truncatedPartitionPoly
    exact mul_neg_geom_sum x κ
  have h2 : truncatedPartitionPoly 2 x = 1 + x := by
    unfold truncatedPartitionPoly
    simp [Finset.sum_range_succ]
  have h3 : truncatedPartitionPoly 3 x = 1 + x + x ^ 2 := by
    unfold truncatedPartitionPoly
    simp [Finset.sum_range_succ, add_assoc]
  have h3ω : truncatedPartitionPoly 3 ω = 0 := by
    have h3' : truncatedPartitionPoly 3 ω = 1 + ω + ω ^ 2 := by
      unfold truncatedPartitionPoly
      simp [Finset.sum_range_succ, add_assoc]
    rw [h3', hω]
  exact ⟨hGeom, h2, by rw [h2]; ring, h3, by rw [h3]; ring, h3ω⟩

/-! ## Deduction 2: `A₂ = 𝔰𝔩₃` Weyl Denominator, Laughlin Odd-`m` Jastrow Braiding,
    Block Super-LU Factorization, & Moment-Curve Diquark/Baryon Identity (`𝔙₅ ≺ 𝔙₆ ≺ 𝔙₇ ≺ 𝔙₈`) -/

/-- The `A₂ = 𝔰𝔩₃` alternating Weyl denominator sum over `S₃`:
`(y z² - z y²) - (x z² - z x²) + (x y² - y x²)`. -/
def weylA2Alternating (x y z : R) : R :=
  (y * z ^ 2 - z * y ^ 2) - (x * z ^ 2 - z * x ^ 2) + (x * y ^ 2 - y * x ^ 2)

/-- The 3-particle Laughlin Jastrow factor at odd filling index `m = 2k + 1`. -/
def laughlinJastrow3 (k : ℕ) (x y z : R) : R :=
  (weylA2Alternating x y z) ^ (2 * k + 1)

/-- **Theorem 3 (`A₂` Weyl Denominator Factorization & Laughlin Odd-`m` Braiding Antisymmetry — `𝔙₅, 𝔙₆`)**:
1. `weylA2Alternating x y z = (y - x) * (z - x) * (z - y)`,
2. `weylA2Alternating` equals the moment-curve baryon singlet `ColorVec3.baryonDet` and
   Mathlib's `Fin 3` Vandermonde determinant `FiniteVandermondeExclusionWitness.determinant`,
3. For every `k : ℕ` (odd power `m = 2k + 1`), `laughlinJastrow3 k` reverses sign under every
   transposition `(x ↔ y)`, `(y ↔ z)`, and `(x ↔ z)`. -/
theorem weylA2_factorization_and_laughlin_odd_braiding
    (k : ℕ) (x y z : R) :
    weylA2Alternating x y z = (y - x) * (z - x) * (z - y) ∧
    weylA2Alternating x y z =
      ColorVec3.baryonDet (colorMomentCurve x) (colorMomentCurve y) (colorMomentCurve z) ∧
    weylA2Alternating x y z =
      FiniteVandermondeExclusionWitness.determinant (momentNodes x y z) ∧
    laughlinJastrow3 k y x z = -laughlinJastrow3 k x y z ∧
    laughlinJastrow3 k x z y = -laughlinJastrow3 k x y z ∧
    laughlinJastrow3 k z y x = -laughlinJastrow3 k x y z := by
  have hFact : weylA2Alternating x y z = (y - x) * (z - x) * (z - y) := by
    unfold weylA2Alternating
    ring
  have hBar :
      weylA2Alternating x y z =
        ColorVec3.baryonDet (colorMomentCurve x) (colorMomentCurve y) (colorMomentCurve z) := by
    rw [hFact, baryonDet_colorMomentCurve_eq_vandermonde_product]
  have hVan :
      weylA2Alternating x y z =
        FiniteVandermondeExclusionWitness.determinant (momentNodes x y z) := by
    rw [hBar, baryonDet_colorMomentCurve_eq_vandermonde_determinant]
  have hOddNeg (u : R) : (-u) ^ (2 * k + 1) = -(u ^ (2 * k + 1)) :=
    Odd.neg_pow ⟨k, rfl⟩ u
  have hSwap12 : weylA2Alternating y x z = -weylA2Alternating x y z := by
    unfold weylA2Alternating; ring
  have hSwap23 : weylA2Alternating x z y = -weylA2Alternating x y z := by
    unfold weylA2Alternating; ring
  have hSwap13 : weylA2Alternating z y x = -weylA2Alternating x y z := by
    unfold weylA2Alternating; ring
  refine ⟨hFact, hBar, hVan, ?_, ?_, ?_⟩
  · unfold laughlinJastrow3
    rw [hSwap12, hOddNeg]
  · unfold laughlinJastrow3
    rw [hSwap23, hOddNeg]
  · unfold laughlinJastrow3
    rw [hSwap13, hOddNeg]

/-- **Theorem 4 (Universal Block Super-LU Bruhat–Schur Factorization — `𝔙₇`)**:
For any `m × m` block `A`, `m × n` block `B`, `n × m` block `C`, and `n × n` blocks `D, D_inv`
satisfying `D * D_inv = 1` and `D_inv * D = 1`, the block Super-LU factors
`L = fromBlocks 1 (B * D_inv) 0 1`, `H = fromBlocks (A - B * D_inv * C) 0 0 D`, and
`R = fromBlocks 1 0 (D_inv * C) 1` satisfy `L * H * R = fromBlocks A B C D`. -/
theorem block_super_lu_factorization
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R)
    (C : Matrix (Fin n) (Fin m) R) (D D_inv : Matrix (Fin n) (Fin n) R)
    (hD_right : D * D_inv = 1) (hD_left : D_inv * D = 1) :
    Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) R) (B * D_inv) 0 (1 : Matrix (Fin n) (Fin n) R) *
      Matrix.fromBlocks (A - B * D_inv * C) 0 0 D *
      Matrix.fromBlocks (1 : Matrix (Fin m) (Fin m) R) 0 (D_inv * C) (1 : Matrix (Fin n) (Fin n) R) =
    Matrix.fromBlocks A B C D := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  have hBD : B * D_inv * D = B := by
    rw [Matrix.mul_assoc, hD_left, Matrix.mul_one]
  have hDC : D * (D_inv * C) = C := by
    rw [← Matrix.mul_assoc, hD_right, Matrix.one_mul]
  have hBDC : B * (D_inv * C) = B * D_inv * C :=
    (Matrix.mul_assoc B D_inv C).symm
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add, hBD, hDC, hBDC, sub_add_cancel]

/-- **Theorem 5 (Catto–Gürsey Supertrace & Moment-Curve Diquark/Baryon Vandermonde Identity — `𝔙₈`)**:
1. On `SuperMatrix 6 21 R`, `supertrace (1 : SuperMatrix 6 21 R) = -15`,
2. On the spectral moment curve `u(t_c) = (1, t_c, t_c²)`, the 2-quark Zorn/Catto–Gürsey
   diquark cross product factors as:
   `ColorVec3.cross (colorMomentCurve t₁) (colorMomentCurve t₂) =
     ⟨(t₂ - t₁) * (t₁ * t₂), -(t₂ - t₁) * (t₁ + t₂), t₂ - t₁⟩`,
3. Taking the scalar dot product with the third quark `u(t₃) = (1, t₃, t₃²)` yields the
   3-quark baryon singlet determinant, which coincides identically with the `A₂ = 𝔰𝔩₃`
   Weyl denominator `weylA2Alternating t₁ t₂ t₃`, the Vandermonde product
   `(t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂)`, and Mathlib's `Fin 3` Vandermonde determinant! -/
theorem catto_gursey_supertrace_and_moment_curve_baryon_vandermonde
    (t₁ t₂ t₃ : R) :
    InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace
      (1 : InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix 6 21 R) = -15 ∧
    ColorVec3.cross (colorMomentCurve t₁) (colorMomentCurve t₂) =
      ⟨(t₂ - t₁) * (t₁ * t₂), -(t₂ - t₁) * (t₁ + t₂), t₂ - t₁⟩ ∧
    ColorVec3.dot (ColorVec3.cross (colorMomentCurve t₁) (colorMomentCurve t₂))
        (colorMomentCurve t₃) =
      ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) ∧
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
      weylA2Alternating t₁ t₂ t₃ ∧
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
      (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) ∧
    ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
      FiniteVandermondeExclusionWitness.determinant (momentNodes t₁ t₂ t₃) := by
  have hCross :
      ColorVec3.cross (colorMomentCurve t₁) (colorMomentCurve t₂) =
        ⟨(t₂ - t₁) * (t₁ * t₂), -(t₂ - t₁) * (t₁ + t₂), t₂ - t₁⟩ := by
    ext <;> simp [ColorVec3.cross, colorMomentCurve] <;> ring
  have hWeyl :
      ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
        weylA2Alternating t₁ t₂ t₃ := by
    rw [baryonDet_colorMomentCurve_eq_vandermonde_product]
    unfold weylA2Alternating
    ring
  have hDotCross :
      ColorVec3.dot (ColorVec3.cross (colorMomentCurve t₁) (colorMomentCurve t₂))
          (colorMomentCurve t₃) =
        ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) := by
    simp [ColorVec3.baryonDet, ColorVec3.dot, ColorVec3.cross, colorMomentCurve]
    ring
  exact ⟨InfoGeometry.Canonical.CattoGurseyBlockGrading.supertrace_identity_6_21,
         hCross,
         hDotCross,
         hWeyl,
         baryonDet_colorMomentCurve_eq_vandermonde_product t₁ t₂ t₃,
         baryonDet_colorMomentCurve_eq_vandermonde_determinant t₁ t₂ t₃⟩

/-! ## Master 8-Stage Synthesis (`𝔙₁ ≺ 𝔙₂ ≺ ⋯ ≺ 𝔙₈`) -/

/-- **Master Stream VI Synthesis
(`vandermonde_superalgebra_color_partition_statistics_master_synthesis`)**:
Seals the complete 8-stage causal poset (`𝔙₁ ≺ 𝔙₂ ≺ ⋯ ≺ 𝔙₈`):
0. Strict 8-stage linear chain and acyclicity of `VandermondeSuperalgebraColorPartitionStage`,
1. `𝔙₁`: Two-state correlation symmetrization/antisymmetrization split (`streamVI_correlation_split_route`),
2. `𝔙₂`: Socratic ordinary-trace aporia (`Tr = 2`) vs. supertrace vanishing (`STr = 0`) on odd
   supercommutators, plus Grassmann Berezin derivative-integration (`∫ dθ = ∂_θ`),
3. `𝔙₃`: `ℤ₃` ternary `q`-binomial cube law `(A + B)³ = A³ + B³` (when `1 + ω + ω² = 0` and
   `A B = ω B A`),
4. `𝔙₄`: Cyclotomic partition polynomial identity `(1 - x) Q_κ(x) = 1 - x^κ`, `Φ₂(x) = 1 + x`,
   `Φ₃(x) = 1 + x + x²`, `ℤ₃` color confinement `Φ₃(ω) = 0`, finite Witten–Weyl cancellation
   (`Z_B · STr_F = 1`), and `V₄` Walsh–Fourier 4-sector inversion,
5. `𝔙₅`–`𝔙₆`: Vandermonde collision equivalence (`baryonDet = 0 ↔ ∃ i ≠ j, t_i = t_j`),
   `A₂ = 𝔰𝔩₃` Weyl denominator factorization, Laughlin odd-`m` Jastrow braiding antisymmetry,
   and two-node polynomial divisibility `(X - a) ∣ (X^n - a^n)`,
6. `𝔙₇`: Noncommutative `2 × 2` and block Super-LU Bruhat–Schur factorization `L * H * R = M`,
7. `𝔙₈`: Catto–Gürsey hadronic supermatrix identity supertrace `STr(I_{6|21}) = -15`,
   moment-curve diquark factorization, and the 3-quark baryon singlet = `A₂` color Vandermonde
   determinant `(t₂ - t₁)(t₃ - t₁)(t₃ - t₂)`. -/
theorem vandermonde_superalgebra_color_partition_statistics_master_synthesis
    [IsDomain R]
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (reference comparison : InfoGeometry.Krein.DoubledSpace E)
    (X_ch Y_ch : InfoGeometry.Canonical.RelationalInformationCore.PerturbationChannel E)
    (hX_ch : IsPhaseLinear (E := E) X_ch) (hY_ch : IsPhaseLinear (E := E) Y_ch)
    {B_ring : Type*} [Ring B_ring]
    (ω_b A_b B_b : B_ring)
    (hωA : ω_b * A_b = A_b * ω_b) (hωB : ω_b * B_b = B_b * ω_b)
    (hbraid : A_b * B_b = ω_b * (B_b * A_b)) (hcyc : 1 + ω_b + ω_b ^ 2 = 0)
    (κ : ℕ) (x_p ω_p : R) (hω_p : 1 + ω_p + ω_p ^ 2 = 0)
    (P_pr : InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister)
    (q_pr : ℕ → ℂ) (hq_pr : ∀ p ∈ P_pr.primes, (1 : ℂ) - q_pr p ≠ 0)
    {α : Type*} [Fintype α] [Nonempty α]
    (params : InfoGeometry.GrandCanonical.GrandCanonicalTwoParam α)
    (grade : α → InfoGeometry.Topology.V4RootSystem.V4Group)
    (β_gc μ_gc : ℝ) (g_v4 : InfoGeometry.Topology.V4RootSystem.V4Group)
    (k_laugh : ℕ) (t₁ t₂ t₃ : R)
    (P_div : InfoGeometry.Canonical.WeylPolynomialDivisibilityShadow.TwoNodePolynomialShadow R)
    (M_lu : Matrix (Fin 2) (Fin 2) R) (invD : R) (hD_lu : M_lu 1 1 * invD = 1) :
    -- (0) Strict 8-stage causal chain and acyclicity
    ((∀ s : VandermondeSuperalgebraColorPartitionStage,
        ¬ Relation.TransGen VandermondeSuperalgebraColorPartitionStage.causalEdge s s) ∧
     VandermondeSuperalgebraColorPartitionStage.V1_TwoStateExchangeCorrelationSplit <
       .V2_Z2KoszulSuperLieAndBerezinCalculus ∧
     VandermondeSuperalgebraColorPartitionStage.V2_Z2KoszulSuperLieAndBerezinCalculus <
       .V3_Z3TernaryQuantumPlaneAndTriality ∧
     VandermondeSuperalgebraColorPartitionStage.V3_Z3TernaryQuantumPlaneAndTriality <
       .V4_CyclotomicPartitionWittenAndV4Fourier ∧
     VandermondeSuperalgebraColorPartitionStage.V4_CyclotomicPartitionWittenAndV4Fourier <
       .V5_VandermondeExclusionAndLaughlinBraiding ∧
     VandermondeSuperalgebraColorPartitionStage.V5_VandermondeExclusionAndLaughlinBraiding <
       .V6_WeylA1A2DenominatorAndDivisibility ∧
     VandermondeSuperalgebraColorPartitionStage.V6_WeylA1A2DenominatorAndDivisibility <
       .V7_SuperLUSchurFactorizationAndBerezinian ∧
     VandermondeSuperalgebraColorPartitionStage.V7_SuperLUSchurFactorizationAndBerezinian <
       .V8_CattoGurseySuperalgebraAndMomentCurveBaryon) ∧
    -- (1) Stage 𝔙₁: Two-state exchange & phase-linear correlation split
    (InfoGeometry.Canonical.ModularTwoStateCorrelation.twoStateChannelCorrelation
       (E := E) reference comparison X_ch Y_ch =
       InfoGeometry.Canonical.CorrelationSymmetrization.symmetricTwoStateChannelCorrelation
         (E := E) reference comparison X_ch Y_ch +
       InfoGeometry.Canonical.CorrelationSymmetrization.antisymmetricTwoStateChannelCorrelation
         (E := E) reference comparison X_ch Y_ch ∧
     InfoGeometry.Canonical.CorrelationAntisymmetrization.symmetricPhaseShiftedTwoStateChannelCorrelation
       (E := E) comparison comparison X_ch Y_ch = 0) ∧
    -- (2) Stage 𝔙₂: Socratic trace aporia (Tr = 2 vs. STr = 0) & Grassmann Berezin calculus
    (Matrix.trace
       (InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket .odd .odd
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix
           (1 : Matrix (Fin 1) (Fin 1) ℤ) (0 : Matrix (Fin 1) (Fin 1) ℤ))
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix
           (0 : Matrix (Fin 1) (Fin 1) ℤ) (1 : Matrix (Fin 1) (Fin 1) ℤ))) = 2 ∧
     InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace
       (InfoGeometry.Canonical.GLSupermatrixGradedLie.superbracket .odd .odd
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix
           (1 : Matrix (Fin 1) (Fin 1) ℤ) (0 : Matrix (Fin 1) (Fin 1) ℤ))
         (InfoGeometry.Canonical.GLSupermatrixGradedLie.oddMatrix
           (0 : Matrix (Fin 1) (Fin 1) ℤ) (1 : Matrix (Fin 1) (Fin 1) ℤ))) = 0 ∧
     grassmannMul (grassmannTheta (R := R)) (grassmannTheta (R := R)) = (0, 0) ∧
     berezinIntegral1 (t₁, t₂) = (grassmannDeriv1 (t₁, t₂)).1) ∧
    -- (3) Stage 𝔙₃: ℤ₃ ternary q-binomial cube law (A + B)³ = A³ + B³
    (ω_b ^ 3 = 1 ∧ (A_b + B_b) ^ 3 = A_b ^ 3 + B_b ^ 3) ∧
    -- (4) Stage 𝔙₄: Cyclotomic partition quotients, color confinement, Witten cancellation, & V₄ Fourier
    ((1 - x_p) * truncatedPartitionPoly κ x_p = 1 - x_p ^ κ ∧
     truncatedPartitionPoly 2 x_p = 1 + x_p ∧
     truncatedPartitionPoly 3 x_p = 1 + x_p + x_p ^ 2 ∧
     truncatedPartitionPoly 3 ω_p = 0 ∧
     InfoGeometry.Arithmetic.PrimeWeylDenominatorBridge.finitePrimeBosonicInverseDenominator
         P_pr.primes q_pr *
       InfoGeometry.Arithmetic.MobiusDirichletInverseBridge.finiteMobiusDirichletPolynomial
         P_pr q_pr = 1 ∧
     (1 / 4 : ℝ) *
         ∑ k : Fin 4,
           InfoGeometry.Canonical.V4GroupFourierTransform.v4Character k g_v4 *
             InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge.v4TwistedPartition
               params grade β_gc μ_gc k =
       InfoGeometry.Canonical.PeirceV4GrandCanonicalFourierBridge.v4SectorPartition
         params grade β_gc μ_gc g_v4) ∧
    -- (5) Stage 𝔙₅–𝔙₆: Vandermonde exclusion, A₂ Weyl denominator, Laughlin odd-m braiding, & divisibility
    ((ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) = 0 ↔
        ∃ i j : Fin 3, momentNodes t₁ t₂ t₃ i = momentNodes t₁ t₂ t₃ j ∧ i ≠ j) ∧
     weylA2Alternating t₁ t₂ t₃ = (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) ∧
     laughlinJastrow3 k_laugh t₂ t₁ t₃ = -laughlinJastrow3 k_laugh t₁ t₂ t₃ ∧
     P_div.denominator ∣ P_div.numerator) ∧
    -- (6) Stage 𝔙₇: Super-LU factorization L * H * R = M
    (InfoGeometry.Supergeometry.Berezinian.factorL M_lu invD *
       InfoGeometry.Supergeometry.Berezinian.factorH M_lu invD *
       InfoGeometry.Supergeometry.Berezinian.factorR M_lu invD = M_lu) ∧
    -- (7) Stage 𝔙₈: Catto–Gürsey STr(I_{6|21}) = -15 & Moment-Curve Baryon = A₂ Color Vandermonde
    (InfoGeometry.Canonical.GLSupermatrixGradedLie.supertrace
       (1 : InfoGeometry.Canonical.GLSupermatrixGradedLie.SuperMatrix 6 21 R) = -15 ∧
     ColorVec3.cross (colorMomentCurve t₁) (colorMomentCurve t₂) =
       ⟨(t₂ - t₁) * (t₁ * t₂), -(t₂ - t₁) * (t₁ + t₂), t₂ - t₁⟩ ∧
     ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
       (t₂ - t₁) * (t₃ - t₁) * (t₃ - t₂) ∧
     ColorVec3.baryonDet (colorMomentCurve t₁) (colorMomentCurve t₂) (colorMomentCurve t₃) =
       FiniteVandermondeExclusionWitness.determinant (momentNodes t₁ t₂ t₃)) := by
  have hTrAp := odd_superbracket_ordinary_trace_vs_supertrace
    (1 : Matrix (Fin 1) (Fin 1) ℤ) (0 : Matrix (Fin 1) (Fin 1) ℤ)
    (0 : Matrix (Fin 1) (Fin 1) ℤ) (1 : Matrix (Fin 1) (Fin 1) ℤ)
  have hBer1 := grassmann_berezin_integral_eq_derivative t₁ t₂ (t₁, t₂)
  have hZ3Cube := z3_q_binomial_cube_law ω_b A_b B_b hωA hωB hbraid hcyc
  have hCyc := cyclotomic_partition_quotient_and_color_confinement κ x_p ω_p hω_p
  have hWit := streamVI_finite_witten_weyl_route P_pr q_pr hq_pr
  have hWeyl := weylA2_factorization_and_laughlin_odd_braiding k_laugh t₁ t₂ t₃
  have hCG := catto_gursey_supertrace_and_moment_curve_baryon_vandermonde t₁ t₂ t₃
  exact ⟨⟨VandermondeSuperalgebraColorPartitionStage.causalEdge_acyclic,
          VandermondeSuperalgebraColorPartitionStage.strict_eight_stage_chain.1,
          VandermondeSuperalgebraColorPartitionStage.strict_eight_stage_chain.2.1,
          VandermondeSuperalgebraColorPartitionStage.strict_eight_stage_chain.2.2.1,
          VandermondeSuperalgebraColorPartitionStage.strict_eight_stage_chain.2.2.2.1,
          VandermondeSuperalgebraColorPartitionStage.strict_eight_stage_chain.2.2.2.2.1,
          VandermondeSuperalgebraColorPartitionStage.strict_eight_stage_chain.2.2.2.2.2.1,
          VandermondeSuperalgebraColorPartitionStage.strict_eight_stage_chain.2.2.2.2.2.2⟩,
         streamVI_correlation_split_route reference comparison X_ch Y_ch hX_ch hY_ch,
         ⟨hTrAp.2.2, hTrAp.2.1, hBer1.1, hBer1.2.2.1⟩,
         ⟨hZ3Cube.1, hZ3Cube.2.2.1⟩,
         ⟨hCyc.1, hCyc.2.1, hCyc.2.2.2.1, hCyc.2.2.2.2.2, hWit.2.2,
          streamVI_v4_fourier_route params grade β_gc μ_gc g_v4⟩,
         ⟨baryonDet_colorMomentCurve_eq_zero_iff_collision t₁ t₂ t₃,
          hWeyl.1, hWeyl.2.2.2.1,
          streamVI_weyl_two_node_divisibility_route P_div⟩,
         InfoGeometry.Supergeometry.Berezinian.super_lu_factorization M_lu invD hD_lu,
         ⟨hCG.1, hCG.2.1, hCG.2.2.2.2.1, hCG.2.2.2.2.2⟩⟩

end InfoGeometry.Canonical.VandermondeSuperalgebraColorPartitionStatisticsPoset
