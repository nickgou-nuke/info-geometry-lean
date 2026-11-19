/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Erlangen.SmoothCartanGeometry
import InfoGeometry.Canonical.BirkhoffHilbertChordSectorClosure
import InfoGeometry.Canonical.KleinIcosahedralHauptmodulAndGaloisResolvent
import InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
import InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas
import InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge
import InfoGeometry.Canonical.OperatorFrechetForms
import InfoGeometry.Thermo.OnsagerDifferentialFormsBridge

/-!
# Six-Pillar Plücker–Grassmann–Klein–Clifford–Möbius–Evanston × R1–R2–R3 Cross-Spine Synthesis

Dedicated leaf synthesis module uniting all four cross-spine bridges connecting the
Six-Pillar projective/Clifford/Klein geometry spine (`Spine II`) with the R1–R2–R3
operator-algebra / Krein / Clifford-rotor spine (`Spine I`) without introducing any
internal circular dependencies or typeclass diamonds (`open scoped Erlangen20Unification`
and `open scoped FiniteTensorProduct` remain omitted):

1. **Bridge 1 (`principalTransition_gaugeTransformL_cocycle`)**:
   Contravariant Maurer–Cartan gauge transformation `gaugeTransformL` in R1
   intertwining smooth `SmoothCartanGeometry` right-`H`-equivariant
   `Bundle.Trivialization H C.proj` transition cocycles (`cartanPrincipalTransition_cocycle`:
   `t₁₃ = t₁₂ * t₂₃ ⇒ gaugeTransformL (t₁₂ * t₂₃) Γ = gaugeTransformL t₂₃ (gaugeTransformL t₁₂ Γ)`),
   curvature covariance `Ad(t₁₂⁻¹)`, pure-gauge flatness, and pullback Cartan potential `s* ω`.
2. **Bridge 2 (`biquatBivector_peirce_grace_krein_polarization`)**:
   Single-equation polarization splitting Clifford's elliptic biquaternion square
   `(d + ω₄ m)² = -(‖d‖² + ‖m‖²) - 2 kleinQ(d, m) ω₄` via R1's chiral Peirce
   corners `e₊ = (1 + ω₄)/2`, `e₋ = (1 - ω₄)/2` (`invS e₊ = ω₄`) into
   `-‖d ± m‖² e_±`, identifying the half-sum with Euclidean/Grace bivector energy
   and constructing the explicit Walsh linear equivalence
   `((Fin 3 → ℝ) × (Fin 3 → ℝ)) ≃ₗ[ℝ] SplitDoubledSpace (EuclideanSpace ℝ (Fin 3))`
   carrying `(d, m) ↦ (‖d‖² + ‖m‖², 2 kleinQ(d, m))` in the Hilbert and Krein pairings.
3. **Bridge 3 (`gibbsBKM_onsager_birkhoffHilbert_chord_metric`)**:
   Demonstrates the `T`-odd Casimir lineality obstruction (`casimir_skewSymm_violates_cone_salience`),
   constructs the closed salient proper cone `onsagerBKMProperCone H` on symmetric bounded
   endomorphisms `SymEnd H` (linking `OperatorFrechetForms` Maxwell symmetry and
   `OnsagerClosure.OnsagerCasimirSystem` `T`-even dissipation), derives projective cross-ratio
   distance and congruence monotonicity via `BirkhoffHilbertChordSectorClosure`, and supplies a
   concrete positive-definite `2 × 2` witness on `EuclideanSpace ℝ (Fin 2)`.
4. **Bridge 4 (`binaryIcosahedral_spinGroup_cliffordOneForms_erlangen20`)**:
   Constructs the injective spinor lift `su2ToSpin30Hom : SU2 →* spinGroup q30` using the
   oriented minus-sign `Cl⁰(3, 0)` quaternion identification `(i, j, k) ↦ (-e₂e₃, -e₃e₁, -e₁e₂)`,
   verifies exact double-cover kernel `su2SignSet` onto `q30.IsometryEquiv q30`, and composes
   with `R1R2R3UnifiedTriangleBridge.spinGroup_cliffordOneForms_naturality` to yield
   `2I`-equivariant universal noncommutative 1-forms `d_u : Cl(q₃,₀) → Ω¹_univ(Cl(q₃,₀))`
   paired with Klein's aligned icosahedral `(F, H, T)` invariance.

No `sorry`, `admit`, custom axioms, or `native_decide` are used.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Canonical.SixPillarR1R2R3CrossSpineSynthesis

open Bundle Matrix
open scoped Manifold InnerProductSpace
open InfoGeometry.Erlangen.SmoothCartanGeometry
open InfoGeometry.Projective.GeneralHilbertConeMetric
open InfoGeometry.Erlangen.BirkhoffHilbertConeMetric
open InfoGeometry.Canonical.BirkhoffHilbertChordSectorClosure
open InfoGeometry.Erlangen.KleinIcosahedralQuinticModularJ
open InfoGeometry.Canonical.KleinIcosahedralHauptmodulAndGaloisResolvent
open InfoGeometry.Projective.PluckerAffineScrew
open InfoGeometry.Clifford.CliffordExtensiveRotorsAndBiquaternions
open InfoGeometry.Clifford.CliffordQuaternionFactorizationAndMasterAtlas
open InfoGeometry.Clifford.GradedGraceContraction (clifford_ι_injective)
open InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge
open InfoGeometry.Canonical.OperatorFrechetForms
open InfoGeometry.Canonical.NoncommutativeGibbsExpectationBridge
open InfoGeometry.Canonical.NoncommutativeGibbsBKMHessianBridge
open SouriauOnsagerBKM
open InfoGeometry.Thermo.OnsagerClosure
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.DerivationDifferentialForms
open InfoGeometry.OperatorAlgebra.MaurerCartanTower
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceSpine.UniversalNoncommutativeOneForms
open InfoGeometry.Krein
open InfoGeometry.KK.ClNNFredholmBridge
open InfoGeometry.Synthesis.CartanHestenesRotorSpinConnectionMaurerCartanSynthesis

/-! ## Closed T16 Non-Commutativity Witnesses for Concrete Matrix Carriers -/

section NonCommutativityWitnesses

/-- Closed T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem crossSpine_mat2R_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  ⟨posMatA, posMatB, posMatA_mul_posMatB_ne⟩

/-- Closed T16 non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ`. -/
theorem crossSpine_mat2C_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℂ, A * B ≠ B * A :=
  ⟨matQuatI, matQuatJ, matQuatI_mul_matQuatJ_ne⟩

end NonCommutativityWitnesses

/-! ## Bridge 1: Contravariant R1 `gaugeTransformL` ↔ Smooth Čech Principal Transition Cocycle -/

section Bridge1_CechGaugeTransformL

/-- Right-action (contravariant) R1 Maurer–Cartan gauge transform
`gaugeTransformL g Γ := g⁻¹ Γ g + g⁻¹ D(g)` on `ActionOperatorForm K 1`. -/
def gaugeTransformL {R A : Type*} [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.LieActionLane R A) (g : Aˣ)
    (Γ : ActionOperatorForm K 1) : ActionOperatorForm K 1 :=
  actionConjugateForm K g⁻¹ Γ + actionThetaL K g

theorem gaugeTransformL_apply {R A : Type*} [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.LieActionLane R A) (g : Aˣ)
    (Γ : ActionOperatorForm K 1) (v : Fin 1 → K.L) :
    gaugeTransformL K g Γ v =
      (↑g⁻¹ : A) * Γ v * (g : A) + (↑g⁻¹ : A) * K.operatorAction (v 0) (g : A) :=
  rfl

theorem gaugeTransformL_eq_actionGaugeOneForm_inv {R A : Type*} [CommRing R] [Ring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.LieActionLane R A) (hK : IsLeibnizAction K) (g : Aˣ)
    (Γ : ActionOperatorForm K 1) :
    gaugeTransformL K g Γ = actionGaugeOneForm K Γ g⁻¹ := by
  unfold gaugeTransformL
  rw [actionGaugeOneForm_eq_add_actionThetaL_inv K hK Γ g⁻¹, inv_inv]

/-- Contravariant composition & curvature covariance for `gaugeTransformL` under any
Leibniz `LieActionLane`: `g₁₂ * g₂₃` acts by first applying `g₁₂`, then `g₂₃`. -/
theorem gaugeTransformL_cocycle {R A : Type*} [CommRing R] [Ring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.LieActionLane R A) (hK : IsLeibnizAction K)
    (g₁₂ g₂₃ : Aˣ) (Γ : ActionOperatorForm K 1) :
    gaugeTransformL K (g₁₂ * g₂₃) Γ =
        gaugeTransformL K g₂₃ (gaugeTransformL K g₁₂ Γ) ∧
      gaugeTransformL K 1 Γ = Γ ∧
      gaugeTransformL K g₁₂⁻¹ (gaugeTransformL K g₁₂ Γ) = Γ ∧
      actionCurvature K (gaugeTransformL K g₁₂ Γ) =
        actionConjugateForm K g₁₂⁻¹ (actionCurvature K Γ) ∧
      actionCurvature K (gaugeTransformL K g₁₂ 0) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gaugeTransformL_eq_actionGaugeOneForm_inv K hK (g₁₂ * g₂₃) Γ,
      gaugeTransformL_eq_actionGaugeOneForm_inv K hK g₁₂ Γ,
      gaugeTransformL_eq_actionGaugeOneForm_inv K hK g₂₃ _,
      _root_.mul_inv_rev,
      ← actionGaugeOneForm_mul K hK Γ g₂₃⁻¹ g₁₂⁻¹]
  · rw [gaugeTransformL_eq_actionGaugeOneForm_inv K hK 1 Γ, inv_one,
      actionGaugeOneForm_one K hK]
  · rw [gaugeTransformL_eq_actionGaugeOneForm_inv K hK g₁₂ Γ,
      gaugeTransformL_eq_actionGaugeOneForm_inv K hK g₁₂⁻¹ _,
      inv_inv, actionGaugeOneForm_mul K hK, mul_inv_cancel, actionGaugeOneForm_one K hK]
  · rw [gaugeTransformL_eq_actionGaugeOneForm_inv K hK g₁₂ Γ]
    exact actionCurvature_actionGaugeOneForm K hK Γ g₁₂⁻¹
  · unfold gaugeTransformL
    rw [map_zero, zero_add]
    exact actionThetaL_flat K hK g₁₂

/-- Smooth local identity section `x ↦ e⁻¹(x, 1)` induced by a bundle trivialization `e` of
a `SmoothCartanGeometry`. -/
def cartanLocalSection
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e : Bundle.Trivialization H C.proj) (x : M) : P :=
  e.toPartialHomeomorph.symm (x, (1 : H))

/-- Čech transition map `t_{e₁, e₂}(x) = (e₁ (e₂⁻¹(x, 1))).2 ∈ H` between two
trivializations of `SmoothCartanGeometry`. -/
def cartanPrincipalTransition
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e₁ e₂ : Bundle.Trivialization H C.proj) (x : M) : H :=
  (e₁ (cartanLocalSection C e₂ x)).2

/-- Local pullback Cartan gauge potential `A_e(x) = s_e* ω : Tₓ M →L[ℝ] 𝔤`. -/
def cartanPullbackGaugePotential
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e : Bundle.Trivialization H C.proj) (x : M) :
    TangentSpace IM x →L[ℝ] 𝔤 :=
  (C.omega (cartanLocalSection C e x)).toContinuousLinearMap.comp
    (mfderiv IM IP (cartanLocalSection C e) x)

private lemma cartanLocalSection_proj
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e : Bundle.Trivialization H C.proj) {x : M} (hx : x ∈ e.baseSet) :
    C.proj (cartanLocalSection C e x) = x :=
  e.proj_symm_apply' hx

private lemma cartanLocalSection_apply
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e : Bundle.Trivialization H C.proj) {x : M} (hx : x ∈ e.baseSet) :
    e (cartanLocalSection C e x) = (x, (1 : H)) :=
  e.apply_symm_apply' hx

private lemma cartanSectionThrough_self
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e : Bundle.Trivialization H C.proj)
    (he : ∀ (h : H) (p : P), p ∈ e.source → e (C.rightAct h p) = (C.proj p, (e p).2 * h))
    {p : P} (hp : p ∈ e.source) :
    C.rightAct (e p).2 (cartanLocalSection C e (C.proj p)) = p := by
  have hx : C.proj p ∈ e.baseSet := e.mem_source.mp hp
  have hs_mem : cartanLocalSection C e (C.proj p) ∈ e.source := by
    rw [e.mem_source, cartanLocalSection_proj C e hx]
    exact hx
  have hact_mem : C.rightAct (e p).2 (cartanLocalSection C e (C.proj p)) ∈ e.source := by
    rw [e.mem_source, C.proj_rightAct, cartanLocalSection_proj C e hx]
    exact hx
  have heq : e (C.rightAct (e p).2 (cartanLocalSection C e (C.proj p))) = e p := by
    rw [he _ _ hs_mem, cartanLocalSection_proj C e hx]
    have hloc := congrArg Prod.snd (cartanLocalSection_apply C e hx)
    change (e (cartanLocalSection C e (C.proj p))).2 = (1 : H) at hloc
    rw [hloc, one_mul]
    exact e.mk_proj_snd hp
  calc
    C.rightAct (e p).2 (cartanLocalSection C e (C.proj p)) =
        e.toPartialEquiv.symm (e (C.rightAct (e p).2 (cartanLocalSection C e (C.proj p)))) :=
      (e.left_inv hact_mem).symm
    _ = e.toPartialEquiv.symm (e p) := by rw [heq]
    _ = p := e.left_inv hp

private lemma cartanPrincipalTransition_coord_change
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e₁ e₂ : Bundle.Trivialization H C.proj)
    (he₁ : ∀ (h : H) (p : P), p ∈ e₁.source → e₁ (C.rightAct h p) = (C.proj p, (e₁ p).2 * h))
    (he₂ : ∀ (h : H) (p : P), p ∈ e₂.source → e₂ (C.rightAct h p) = (C.proj p, (e₂ p).2 * h))
    {p : P} (hp₁ : p ∈ e₁.source) (hp₂ : p ∈ e₂.source) :
    (e₁ p).2 = cartanPrincipalTransition C e₁ e₂ (C.proj p) * (e₂ p).2 := by
  have hx₁ : C.proj p ∈ e₁.baseSet := e₁.mem_source.mp hp₁
  have hx₂ : C.proj p ∈ e₂.baseSet := e₂.mem_source.mp hp₂
  have hs₁ : cartanLocalSection C e₂ (C.proj p) ∈ e₁.source := by
    rw [e₁.mem_source, cartanLocalSection_proj C e₂ hx₂]
    exact hx₁
  have hsec := cartanSectionThrough_self C e₂ he₂ hp₂
  have hcomp := congrArg e₁ hsec
  rw [he₁ _ _ hs₁] at hcomp
  exact (congrArg Prod.snd hcomp).symm

theorem cartanPrincipalTransition_self
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e : Bundle.Trivialization H C.proj) {x : M} (hx : x ∈ e.baseSet) :
    cartanPrincipalTransition C e e x = 1 := by
  rw [cartanPrincipalTransition, cartanLocalSection_apply C e hx]

theorem cartanPrincipalTransition_cocycle
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e₁ e₂ e₃ : Bundle.Trivialization H C.proj)
    (he₁ : ∀ (h : H) (p : P), p ∈ e₁.source → e₁ (C.rightAct h p) = (C.proj p, (e₁ p).2 * h))
    (he₂ : ∀ (h : H) (p : P), p ∈ e₂.source → e₂ (C.rightAct h p) = (C.proj p, (e₂ p).2 * h))
    {x : M} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet) (hx₃ : x ∈ e₃.baseSet) :
    cartanPrincipalTransition C e₁ e₃ x =
      cartanPrincipalTransition C e₁ e₂ x * cartanPrincipalTransition C e₂ e₃ x := by
  let p : P := cartanLocalSection C e₃ x
  have hp₁ : p ∈ e₁.source := by
    rw [e₁.mem_source, cartanLocalSection_proj C e₃ hx₃]
    exact hx₁
  have hp₂ : p ∈ e₂.source := by
    rw [e₂.mem_source, cartanLocalSection_proj C e₃ hx₃]
    exact hx₂
  have h12 := cartanPrincipalTransition_coord_change C e₁ e₂ he₁ he₂ hp₁ hp₂
  have hproj : C.proj p = x := cartanLocalSection_proj C e₃ hx₃
  rw [hproj] at h12
  exact h12

theorem cartanPrincipalTransition_inv
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e₁ e₂ : Bundle.Trivialization H C.proj)
    (he₁ : ∀ (h : H) (p : P), p ∈ e₁.source → e₁ (C.rightAct h p) = (C.proj p, (e₁ p).2 * h))
    (he₂ : ∀ (h : H) (p : P), p ∈ e₂.source → e₂ (C.rightAct h p) = (C.proj p, (e₂ p).2 * h))
    {x : M} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet) :
    (cartanPrincipalTransition C e₁ e₂ x)⁻¹ = cartanPrincipalTransition C e₂ e₁ x := by
  apply inv_eq_of_mul_eq_one_right
  rw [← cartanPrincipalTransition_cocycle C e₁ e₂ e₁ he₁ he₂ hx₁ hx₂ hx₁]
  exact cartanPrincipalTransition_self C e₁ hx₁

/-- **Bridge 1 (`SmoothCartanGeometry` ↔ R1 `MaurerCartanTower`)**:
For any smooth Cartan geometry `C`, right-`H`-equivariant local trivializations `e₁, e₂, e₃`, and
group representation `ρ : H →* Aˣ` into any Leibniz `LieActionLane R A`, the Čech principal
transition cocycle `t₁₃ = t₁₂ * t₂₃` on triple overlaps satisfies contravariant R1
`gaugeTransformL` patching, `Ad(t₁₂⁻¹)` curvature covariance, pure-gauge flatness, and pullback
Cartan potential evaluation `s₁* ω`. -/
theorem principalTransition_gaugeTransformL_cocycle
    {EP EM HP HM : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [NormedAddCommGroup EM] [NormedSpace ℝ EM]
    [TopologicalSpace HP] [TopologicalSpace HM]
    {IP : ModelWithCorners ℝ EP HP} {IM : ModelWithCorners ℝ EM HM}
    {P M : Type*} [TopologicalSpace P] [ChartedSpace HP P]
    [TopologicalSpace M] [ChartedSpace HM M]
    {H : Type*} [Group H] [TopologicalSpace H]
    {𝔤 𝔥 : Type*} [TopologicalSpace 𝔤] [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
    [TopologicalSpace 𝔥] [LieRing 𝔥] [LieAlgebra ℝ 𝔥]
    (C : SmoothCartanGeometry EP EM HP HM IP IM P M H 𝔤 𝔥)
    (e₁ e₂ e₃ : Bundle.Trivialization H C.proj)
    (he₁ : ∀ (h : H) (p : P), p ∈ e₁.source → e₁ (C.rightAct h p) = (C.proj p, (e₁ p).2 * h))
    (he₂ : ∀ (h : H) (p : P), p ∈ e₂.source → e₂ (C.rightAct h p) = (C.proj p, (e₂ p).2 * h))
    {x : M} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet) (hx₃ : x ∈ e₃.baseSet)
    {R A : Type*} [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.LieActionLane R A) (hK : IsLeibnizAction K)
    (ρ : H →* Aˣ) (Γ : ActionOperatorForm K 1) (v : TangentSpace IM x) :
    (cartanPrincipalTransition C e₁ e₃ x =
        cartanPrincipalTransition C e₁ e₂ x * cartanPrincipalTransition C e₂ e₃ x ∧
      gaugeTransformL K (ρ (cartanPrincipalTransition C e₁ e₃ x)) Γ =
        gaugeTransformL K (ρ (cartanPrincipalTransition C e₂ e₃ x))
          (gaugeTransformL K (ρ (cartanPrincipalTransition C e₁ e₂ x)) Γ)) ∧
      gaugeTransformL K (ρ (cartanPrincipalTransition C e₂ e₁ x))
          (gaugeTransformL K (ρ (cartanPrincipalTransition C e₁ e₂ x)) Γ) = Γ ∧
      actionCurvature K (gaugeTransformL K (ρ (cartanPrincipalTransition C e₁ e₂ x)) Γ) =
        actionConjugateForm K (ρ (cartanPrincipalTransition C e₁ e₂ x))⁻¹ (actionCurvature K Γ) ∧
      actionCurvature K (gaugeTransformL K (ρ (cartanPrincipalTransition C e₁ e₂ x)) 0) = 0 ∧
      cartanPullbackGaugePotential C e₁ x v =
        C.omega (cartanLocalSection C e₁ x)
          (mfderiv IM IP (cartanLocalSection C e₁) x v) := by
  have hcc : cartanPrincipalTransition C e₁ e₃ x =
      cartanPrincipalTransition C e₁ e₂ x * cartanPrincipalTransition C e₂ e₃ x :=
    cartanPrincipalTransition_cocycle C e₁ e₂ e₃ he₁ he₂ hx₁ hx₂ hx₃
  have hinv : (cartanPrincipalTransition C e₁ e₂ x)⁻¹ = cartanPrincipalTransition C e₂ e₁ x :=
    cartanPrincipalTransition_inv C e₁ e₂ he₁ he₂ hx₁ hx₂
  have hgt := gaugeTransformL_cocycle K hK
    (ρ (cartanPrincipalTransition C e₁ e₂ x)) (ρ (cartanPrincipalTransition C e₂ e₃ x)) Γ
  refine ⟨⟨hcc, ?_⟩, ?_, hgt.2.2.2.1, hgt.2.2.2.2, rfl⟩
  · rw [hcc, map_mul]
    exact hgt.1
  · rw [← hinv, map_inv]
    exact hgt.2.2.1

end Bridge1_CechGaugeTransformL

/-! ## Bridge 2: Elliptic Biquaternions (`Cl(0,4)`) ↔ Peirce (`invS`) ↔ Grace ↔ Split `(3,3)` Krein -/

section Bridge2_BiquaternionPeirceKreinWalsh

private lemma biquatIdempPlus_ω4_laws :
    1 - biquatIdempPlus = biquatIdempMinus ∧
      PeirceSpine.invS biquatIdempPlus = ω₄ ℝ ∧
      biquatIdempPlus * ω₄ ℝ = biquatIdempPlus ∧
      biquatIdempMinus * ω₄ ℝ = -biquatIdempMinus := by
  have hb := biquat_chiral_peirce_decomposition
  have hωeq : ωEven ℝ 2 = ω₄ ℝ := ωEven_two_eq_ω₄ ℝ
  have hsub : 1 - biquatIdempPlus = biquatIdempMinus :=
    sub_eq_of_eq_add' hb.2.2.2.2.2.2.1.symm
  have hinvS : PeirceSpine.invS biquatIdempPlus = ω₄ ℝ := by
    dsimp [PeirceSpine.invS, biquatIdempPlus]
    rw [hωeq]
    module
  have hωsq : ω₄ ℝ * ω₄ ℝ = 1 := ω₄_sq ℝ
  have hPω : biquatIdempPlus * ω₄ ℝ = biquatIdempPlus := by
    dsimp [biquatIdempPlus]
    rw [hωeq, smul_mul_assoc, add_mul, one_mul, hωsq, add_comm]
  have hMω : biquatIdempMinus * ω₄ ℝ = -biquatIdempMinus := by
    dsimp [biquatIdempMinus]
    rw [hωeq, smul_mul_assoc, sub_mul, one_mul, hωsq, ← smul_neg, neg_sub]
  exact ⟨hsub, hinvS, hPω, hMω⟩

private lemma biquatIdemp_peirce_algebraMap_and_ω4 (c k : ℝ) :
    let Bsq : CliffordAlgebra (cliffordNegSqForm ℝ 4) := algebraMap ℝ _ c - k • ω₄ ℝ
    peirce11 biquatIdempPlus Bsq = (c - k) • biquatIdempPlus ∧
      peirce00 biquatIdempPlus Bsq = (c + k) • biquatIdempMinus := by
  intro Bsq
  have hb := biquat_chiral_peirce_decomposition
  have hl := biquatIdempPlus_ω4_laws
  have hPP := hb.2.2.1
  have hMM := hb.2.2.2.1
  constructor
  · dsimp [peirce11, Bsq]
    rw [mul_sub, sub_mul, ← Algebra.commutes c biquatIdempPlus, ← Algebra.smul_def,
      smul_mul_assoc, hPP, mul_smul_comm, smul_mul_assoc, hl.2.2.1, hPP, sub_smul]
  · dsimp [peirce00, Bsq]
    rw [hl.1, mul_sub, sub_mul, ← Algebra.commutes c biquatIdempMinus, ← Algebra.smul_def,
      smul_mul_assoc, hMM, mul_smul_comm, smul_mul_assoc, hl.2.2.2, neg_mul, hMM,
      smul_neg, sub_neg_eq_add, add_smul]

private lemma vec3_dot_polarization (d m : Fin 3 → ℝ) :
    -(d ⬝ᵥ d + m ⬝ᵥ m) - 2 * (d ⬝ᵥ m) = -((d + m) ⬝ᵥ (d + m)) ∧
      -(d ⬝ᵥ d + m ⬝ᵥ m) + 2 * (d ⬝ᵥ m) = -((d - m) ⬝ᵥ (d - m)) ∧
      (1 / 2 : ℝ) * ((d + m) ⬝ᵥ (d + m) + (d - m) ⬝ᵥ (d - m)) = d ⬝ᵥ d + m ⬝ᵥ m ∧
      (1 / 4 : ℝ) * ((d + m) ⬝ᵥ (d + m) - (d - m) ⬝ᵥ (d - m)) = d ⬝ᵥ m := by
  simp only [dotProduct, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_three]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- Walsh linear equivalence mapping Plücker direction-moment pairs `(d, m)` onto
R2's graded doubled Hilbert/Krein space `SplitDoubledSpace (EuclideanSpace ℝ (Fin 3))` via
`(u, v) = (1 / √2) (d + m, d - m)`. -/
def walshPluckerSplitDoubledEquiv :
    ((Fin 3 → ℝ) × (Fin 3 → ℝ)) ≃ₗ[ℝ] SplitDoubledSpace (EuclideanSpace ℝ (Fin 3)) where
  toFun dm :=
    ⟨to_doubled
      (WithLp.toLp (2 : ENNReal) ((1 / Real.sqrt 2) • (dm.1 + dm.2)))
      (WithLp.toLp (2 : ENNReal) ((1 / Real.sqrt 2) • (dm.1 - dm.2)))⟩
  invFun w :=
    let x : Fin 3 → ℝ := WithLp.ofLp (WithLp.fst w.toDoubled)
    let ξ : Fin 3 → ℝ := WithLp.ofLp (WithLp.snd w.toDoubled)
    ((1 / Real.sqrt 2) • (x + ξ), (1 / Real.sqrt 2) • (x - ξ))
  left_inv dm := by
    have h2ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    simp only [fst_to_doubled, snd_to_doubled, WithLp.ofLp_toLp]
    ext i <;> simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    · field_simp [h2ne]
      rw [hsq2]
      ring
    · field_simp [h2ne]
      rw [hsq2]
      ring
  right_inv w := by
    have h2ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext
    · ext i
      simp only [fst_to_doubled, WithLp.ofLp_toLp, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
        smul_eq_mul]
      field_simp [h2ne]
      rw [hsq2]
      ring
    · ext i
      simp only [snd_to_doubled, WithLp.ofLp_toLp, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
        smul_eq_mul]
      field_simp [h2ne]
      rw [hsq2]
      ring
  map_add' dm₁ dm₂ := by
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> ext i <;>
      simp only [SplitDoubledSpace.toDoubled_add, fst_to_doubled, snd_to_doubled,
        WithLp.add_fst, WithLp.add_snd, WithLp.ofLp_add, WithLp.ofLp_toLp,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add] <;>
      ring
  map_smul' c dm := by
    apply SplitDoubledSpace.ext
    apply DoubledSpace.ext <;> ext i <;>
      simp only [RingHom.id_apply, SplitDoubledSpace.toDoubled_smul, fst_to_doubled,
        snd_to_doubled, WithLp.smul_fst, WithLp.smul_snd, WithLp.ofLp_smul, WithLp.ofLp_toLp,
        Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd] <;>
      ring

private lemma walshPluckerSplitDoubledEquiv_toDoubled (d m : Fin 3 → ℝ) :
    (walshPluckerSplitDoubledEquiv (d, m)).toDoubled =
      to_doubled
        (WithLp.toLp (2 : ENNReal) ((1 / Real.sqrt 2) • (d + m)))
        (WithLp.toLp (2 : ENNReal) ((1 / Real.sqrt 2) • (d - m))) := rfl

private lemma doubled_inner_to_doubled {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x ξ y η : E) :
    ⟪to_doubled x ξ, to_doubled y η⟫_ℝ = ⟪x, y⟫_ℝ + ⟪ξ, η⟫_ℝ := by
  simp only [to_doubled, WithLp.prod_inner_apply]

private lemma euclidean3_inner_toLp (x y : Fin 3 → ℝ) :
    ⟪WithLp.toLp (2 : ENNReal) x, WithLp.toLp (2 : ENNReal) y⟫_ℝ = x ⬝ᵥ y := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, Fin.sum_univ_three]
  ring

theorem walshPluckerSplitDoubledEquiv_hilbert_and_krein (d m : Fin 3 → ℝ) :
    ⟪walshPluckerSplitDoubledEquiv (d, m), walshPluckerSplitDoubledEquiv (d, m)⟫_ℝ =
        d ⬝ᵥ d + m ⬝ᵥ m ∧
      (1 / 2 : ℝ) *
          KreinSpace.kreinInner (walshPluckerSplitDoubledEquiv (d, m))
            (walshPluckerSplitDoubledEquiv (d, m)) =
        (directionMomentEquiv.symm (d, m)).kleinQ := by
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpol := vec3_dot_polarization d m
  have hinv2 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
    calc
      (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / (Real.sqrt 2 * Real.sqrt 2) := by ring
      _ = (1 / 2 : ℝ) := by rw [hsq2]
  have hHilb :
      ⟪walshPluckerSplitDoubledEquiv (d, m), walshPluckerSplitDoubledEquiv (d, m)⟫_ℝ =
        (1 / 2 : ℝ) * ((d + m) ⬝ᵥ (d + m) + (d - m) ⬝ᵥ (d - m)) := by
    rw [SplitDoubledSpace.inner_eq (E := EuclideanSpace ℝ (Fin 3)),
      walshPluckerSplitDoubledEquiv_toDoubled,
      doubled_inner_to_doubled,
      euclidean3_inner_toLp, euclidean3_inner_toLp]
    trans ((1 / Real.sqrt 2 * (1 / Real.sqrt 2)) *
        ((d + m) ⬝ᵥ (d + m) + (d - m) ⬝ᵥ (d - m)))
    · simp only [dotProduct, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
        Fin.sum_univ_three]
      ring
    · rw [hinv2]
  have hKrein :
      KreinSpace.kreinInner (walshPluckerSplitDoubledEquiv (d, m))
          (walshPluckerSplitDoubledEquiv (d, m)) =
        (1 / 2 : ℝ) * ((d + m) ⬝ᵥ (d + m) - (d - m) ⬝ᵥ (d - m)) := by
    rw [KreinSpace.kreinInner_def]
    change ⟪KreinSpace.jCLM (H := SplitDoubledSpace (EuclideanSpace ℝ (Fin 3)))
        (walshPluckerSplitDoubledEquiv (d, m)),
      walshPluckerSplitDoubledEquiv (d, m)⟫_ℝ = _
    rw [SplitDoubledSpace.jCLM_eq_splitDoubledSpectralEpsilon,
      SplitDoubledSpace.splitDoubledSpectralEpsilon, SplitDoubledSpace.conjEnd_apply,
      SplitDoubledSpace.inner_eq, walshPluckerSplitDoubledEquiv_toDoubled,
      spectral_epsilon_to_doubled]
    dsimp only
    rw [doubled_inner_to_doubled, inner_neg_left,
      euclidean3_inner_toLp, euclidean3_inner_toLp]
    trans ((1 / Real.sqrt 2 * (1 / Real.sqrt 2)) *
        ((d + m) ⬝ᵥ (d + m) - (d - m) ⬝ᵥ (d - m)))
    · simp only [dotProduct, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
        Fin.sum_univ_three]
      ring
    · rw [hinv2]
  constructor
  · exact hHilb.trans hpol.2.2.1
  · rw [hKrein, ← mul_assoc, kleinQ_directionMoment]
    have hquarter : ((1 / 2 : ℝ) * (1 / 2 : ℝ)) = (1 / 4 : ℝ) := by norm_num
    rw [hquarter]
    exact hpol.2.2.2

/-- **Bridge 2 (`Clifford 1878 Biquaternions` ↔ R1 `PeirceSpine` ↔ R2 `(3, 3)` Krein)**:
Splits `(D + ω₄ M)² = -(‖d‖² + ‖m‖²) - 2 kleinQ(d, m) ω₄` at the chiral Peirce projector
`P = biquatIdempPlus` (`invS P = ω₄`), recovering `-‖d ± m‖² e_±` in the two corners and
identifying the Walsh transform `(u, v) = (1 / √2)(d + m, d - m)` as an exact Hilbert-Krein
polarization into `SplitDoubledSpace (EuclideanSpace ℝ (Fin 3))`. -/
theorem biquatBivector_peirce_grace_krein_polarization (d m : Fin 3 → ℝ) :
    let P := biquatIdempPlus
    let B := biquatBivector ℝ d m
    1 - P = biquatIdempMinus ∧
      PeirceSpine.invS P = ω₄ ℝ ∧
      peirce11 P (B * B) = -(((d + m) ⬝ᵥ (d + m)) • biquatIdempPlus) ∧
      peirce00 P (B * B) = -(((d - m) ⬝ᵥ (d - m)) • biquatIdempMinus) ∧
      (1 / 2 : ℝ) * (((d + m) ⬝ᵥ (d + m)) + ((d - m) ⬝ᵥ (d - m))) = d ⬝ᵥ d + m ⬝ᵥ m ∧
      (1 / 4 : ℝ) * (((d + m) ⬝ᵥ (d + m)) - ((d - m) ⬝ᵥ (d - m))) =
        (directionMomentEquiv.symm (d, m)).kleinQ ∧
      ⟪walshPluckerSplitDoubledEquiv (d, m), walshPluckerSplitDoubledEquiv (d, m)⟫_ℝ =
        d ⬝ᵥ d + m ⬝ᵥ m ∧
      (1 / 2 : ℝ) *
          KreinSpace.kreinInner (walshPluckerSplitDoubledEquiv (d, m))
            (walshPluckerSplitDoubledEquiv (d, m)) =
        (directionMomentEquiv.symm (d, m)).kleinQ := by
  intro P B
  have hl := biquatIdempPlus_ω4_laws
  have hc := biquatIdemp_peirce_algebraMap_and_ω4 (-(d ⬝ᵥ d + m ⬝ᵥ m)) (2 * (d ⬝ᵥ m))
  have hpol := vec3_dot_polarization d m
  have hwk := walshPluckerSplitDoubledEquiv_hilbert_and_krein d m
  have hBsq : B * B =
      algebraMap ℝ (CliffordAlgebra (cliffordNegSqForm ℝ 4)) (-(d ⬝ᵥ d + m ⬝ᵥ m)) -
        (2 * (d ⬝ᵥ m)) • ω₄ ℝ :=
    biquatBivector_sq ℝ d m
  refine ⟨hl.1, hl.2.1, ?_, ?_, hpol.2.2.1, ?_, hwk.1, hwk.2⟩
  · rw [hBsq]
    have h1 := hc.1
    rw [h1, hpol.1, neg_smul]
  · rw [hBsq]
    have h2 := hc.2
    rw [h2, hpol.2.1, neg_smul]
  · rw [hpol.2.2.2, ← kleinQ_directionMoment d m]

end Bridge2_BiquaternionPeirceKreinWalsh

/-! ## Bridge 3: Birkhoff–Hilbert Cone Metric on the Salient `T`-Even Onsager / Gibbs-BKM Cone -/

section Bridge3_OnsagerBKMBirkhoffHilbert

/-- Antisymmetric `T`-odd Casimir generator `!![0, 1; -1, 0]`: both `A` and `-A` have
identically zero quadratic form `vᵀ (±A) v = 0`, obstructing cone salience if `T`-odd
Casimir terms are retained in the cone carrier. -/
def casimirSkewMat2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

theorem casimir_skewSymm_violates_cone_salience :
    casimirSkewMat2.transpose = -casimirSkewMat2 ∧
      casimirSkewMat2 ≠ 0 ∧
      (∀ v : Fin 2 → ℝ, 0 ≤ dotProduct v (casimirSkewMat2 *ᵥ v)) ∧
      (∀ v : Fin 2 → ℝ, 0 ≤ dotProduct v ((-casimirSkewMat2) *ᵥ v)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [casimirSkewMat2]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [casimirSkewMat2] at h01
  · intro v
    have hz : dotProduct v (casimirSkewMat2 *ᵥ v) = 0 := by
      simp [casimirSkewMat2, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    linarith
  · intro v
    have hz : dotProduct v ((-casimirSkewMat2) *ᵥ v) = 0 := by
      simp [casimirSkewMat2, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    linarith

/-- Submodule of symmetric bounded linear endomorphisms `S : H →L[ℝ] H`
(`⟪u, S w⟫ = ⟪S u, w⟫`, i.e., `T`-even Onsager / Gibbs-BKM sector). -/
def symEndSubmodule (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    Submodule ℝ (H →L[ℝ] H) where
  carrier := { S | ∀ u w : H, ⟪u, S w⟫_ℝ = ⟪S u, w⟫_ℝ }
  zero_mem' _ _ := by simp
  add_mem' ha hb u w := by simp [inner_add_left, inner_add_right, ha u w, hb u w]
  smul_mem' c S hS u w := by simp [inner_smul_left, inner_smul_right, hS u w]

/-- Symmetric bounded endomorphism wrapper (`T`-even Onsager / Gibbs-BKM subspace),
bundled as a 1-field structure for fast, diamond-free `NormedAddCommGroup` and
`NormedSpace ℝ` synthesis. -/
@[ext]
structure SymEnd (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  toCLM : H →L[ℝ] H
  symm : ∀ u w : H, ⟪u, toCLM w⟫_ℝ = ⟪toCLM u, w⟫_ℝ

namespace SymEnd

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private lemma symEnd_nsmul_symm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : SymEnd H) (n : ℕ) (u w : H) :
    ⟪u, (n • a.toCLM) w⟫_ℝ = ⟪(n • a.toCLM) u, w⟫_ℝ := by
  induction n with
  | zero => simp
  | succ k ih =>
      simp only [add_nsmul, one_nsmul, _root_.add_apply, inner_add_left, inner_add_right, ih,
        a.symm u w]

instance : Add (SymEnd H) := ⟨fun a b => ⟨a.toCLM + b.toCLM, fun u w => by
  simp only [_root_.add_apply, inner_add_left, inner_add_right, a.symm u w, b.symm u w]⟩⟩
instance : Zero (SymEnd H) := ⟨⟨0, fun _ _ => by simp⟩⟩
instance : Inhabited (SymEnd H) := ⟨0⟩
instance : Neg (SymEnd H) := ⟨fun a => ⟨-a.toCLM, fun u w => by
  simp only [_root_.neg_apply, inner_neg_left, inner_neg_right, a.symm u w]⟩⟩
instance : Sub (SymEnd H) := ⟨fun a b => ⟨a.toCLM - b.toCLM, fun u w => by
  simp only [_root_.sub_apply, inner_sub_left, inner_sub_right, a.symm u w, b.symm u w]⟩⟩
instance : SMul ℕ (SymEnd H) := ⟨fun n a => ⟨n • a.toCLM, fun u w =>
  symEnd_nsmul_symm a n u w⟩⟩
instance : SMul ℤ (SymEnd H) := ⟨fun z a => ⟨z • a.toCLM, fun u w => by
  cases z with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, natCast_zsmul]
      exact symEnd_nsmul_symm a n u w
  | negSucc n =>
      simp only [negSucc_zsmul, _root_.neg_apply, inner_neg_left, inner_neg_right,
        symEnd_nsmul_symm a (n + 1) u w]⟩⟩
instance : SMul ℝ (SymEnd H) := ⟨fun c a => ⟨c • a.toCLM, fun u w => by
  simp only [_root_.smul_apply, real_inner_smul_left, real_inner_smul_right, a.symm u w]⟩⟩

@[simp] lemma toCLM_zero : (0 : SymEnd H).toCLM = 0 := rfl
@[simp] lemma toCLM_add (a b : SymEnd H) : (a + b).toCLM = a.toCLM + b.toCLM := rfl
@[simp] lemma toCLM_neg (a : SymEnd H) : (-a).toCLM = -a.toCLM := rfl
@[simp] lemma toCLM_sub (a b : SymEnd H) : (a - b).toCLM = a.toCLM - b.toCLM := rfl
@[simp] lemma toCLM_smul (c : ℝ) (a : SymEnd H) : (c • a).toCLM = c • a.toCLM := rfl

lemma toCLM_injective : Function.Injective (toCLM : SymEnd H → (H →L[ℝ] H)) :=
  fun a b h => by cases a; cases b; cases h; rfl

instance : AddCommGroup (SymEnd H) :=
  Function.Injective.addCommGroup toCLM toCLM_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℝ (SymEnd H) :=
  Function.Injective.module ℝ
    ({ toFun := toCLM, map_zero' := rfl, map_add' := fun _ _ => rfl } : SymEnd H →+ (H →L[ℝ] H))
    toCLM_injective (fun _ _ => rfl)

instance : NormedAddCommGroup (SymEnd H) :=
  NormedAddCommGroup.induced (SymEnd H) (H →L[ℝ] H)
    ({ toFun := toCLM, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      SymEnd H →+ (H →L[ℝ] H))
    toCLM_injective

@[simp] lemma norm_eq (x : SymEnd H) : ‖x‖ = ‖x.toCLM‖ := rfl

instance : NormedSpace ℝ (SymEnd H) where
  norm_smul_le c x := by
    change ‖(c • x).toCLM‖ ≤ ‖c‖ * ‖x.toCLM‖
    rw [toCLM_smul]
    exact norm_smul_le c x.toCLM

lemma isometry_toCLM : Isometry (toCLM : SymEnd H → (H →L[ℝ] H)) :=
  isometry_iff_dist_eq.mpr fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← toCLM_sub, norm_eq]

lemma continuous_toCLM : Continuous (toCLM : SymEnd H → (H →L[ℝ] H)) :=
  isometry_toCLM.continuous

end SymEnd


instance symEnd_nontrivial (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Nontrivial H] : Nontrivial (SymEnd H) := by
  obtain ⟨v, hv0⟩ := exists_ne (0 : H)
  let I_sym : SymEnd H := ⟨ContinuousLinearMap.id ℝ H, fun _ _ => rfl⟩
  refine ⟨I_sym, 0, fun h => ?_⟩
  have hv := congrArg (fun x : SymEnd H => x.toCLM v) h
  exact hv0 hv

/-- The closed convex proper cone `C⁺_BKM ⊂ SymEnd H` of positive-semidefinite
symmetric bounded endomorphisms (`∀ v, 0 ≤ ⟪v, S v⟫`). -/
def onsagerBKMProperCone (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    ProperCone ℝ (SymEnd H) where
  toSubmodule :=
    { carrier := { S : SymEnd H | ∀ v : H, 0 ≤ ⟪v, S.toCLM v⟫_ℝ }
      zero_mem' _ := by simp
      add_mem' {a b} ha hb v := by
        change 0 ≤ ⟪v, a.toCLM v + b.toCLM v⟫_ℝ
        rw [inner_add_right]
        exact add_nonneg (ha v) (hb v)
      smul_mem' c {S} hS v := by
        change 0 ≤ ⟪v, (c : ℝ) • S.toCLM v⟫_ℝ
        rw [real_inner_smul_right]
        exact mul_nonneg c.2 (hS v) }
  isClosed' := by
    have heq : { S : SymEnd H | ∀ v : H, 0 ≤ ⟪v, S.toCLM v⟫_ℝ } =
        ⋂ v : H, (fun S : SymEnd H => ⟪v, S.toCLM v⟫_ℝ) ⁻¹' Set.Ici 0 := by
      ext S
      simp
    rw [heq]
    refine isClosed_iInter fun v => ?_
    have hcont : Continuous (fun S : SymEnd H => ⟪v, S.toCLM v⟫_ℝ) :=
      continuous_const.inner
        ((ContinuousLinearMap.apply ℝ H v).continuous.comp SymEnd.continuous_toCLM)
    exact isClosed_Ici.preimage hcont

/-- Polarization salience: on symmetric endomorphisms `SymEnd H`,
`S ≥ 0` and `-S ≥ 0` forces `S = 0`, escaping the `T`-odd Casimir lineality obstruction. -/
theorem onsagerBKMProperCone_salient (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    (onsagerBKMProperCone H).toPointedCone.toConvexCone.Salient := by
  intro S hSpos hSne hSneg
  apply hSne
  have hdiag : ∀ x : H, ⟪x, S.toCLM x⟫_ℝ = 0 := fun x =>
    le_antisymm (neg_nonneg.mp (by simpa using hSneg x)) (hSpos x)
  have hbilin : ∀ u w : H, ⟪u, S.toCLM w⟫_ℝ = 0 := by
    intro u w
    have hpol : 4 * ⟪u, S.toCLM w⟫_ℝ = ⟪u + w, S.toCLM (u + w)⟫_ℝ - ⟪u - w, S.toCLM (u - w)⟫_ℝ := by
      have hsym : ⟪w, S.toCLM u⟫_ℝ = ⟪u, S.toCLM w⟫_ℝ := by
        calc
          ⟪w, S.toCLM u⟫_ℝ = ⟪S.toCLM w, u⟫_ℝ := S.symm w u
          _ = ⟪u, S.toCLM w⟫_ℝ := real_inner_comm _ _
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right, hsym]
      ring
    rw [hdiag (u + w), hdiag (u - w), sub_zero] at hpol
    linarith
  apply SymEnd.ext
  apply ContinuousLinearMap.ext
  intro w
  exact inner_self_eq_zero.mp (hbilin (S.toCLM w) w)

/-- Any uniformly coercive symmetric bounded endomorphism (`∀ v, m * ‖v‖² ≤ ⟪v, S v⟫`, `0 < m`)
lies in `interior (onsagerBKMProperCone H)`. -/
theorem mem_interior_onsagerBKMProperCone_of_coercive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : SymEnd H) {m : ℝ} (hm : 0 < m)
    (hcoerc : ∀ v : H, m * ‖v‖ ^ 2 ≤ ⟪v, S.toCLM v⟫_ℝ) :
    S ∈ interior (onsagerBKMProperCone H : Set (SymEnd H)) := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨m / 2, half_pos hm, fun S' hS' v => ?_⟩
  have hdist : ‖S.toCLM - S'.toCLM‖ < m / 2 := by
    have hd : dist S' S < m / 2 := Metric.mem_ball.mp hS'
    rwa [dist_comm, dist_eq_norm, SymEnd.norm_eq, SymEnd.toCLM_sub] at hd
  have hbound : |⟪v, (S.toCLM - S'.toCLM) v⟫_ℝ| ≤ ‖S.toCLM - S'.toCLM‖ * ‖v‖ ^ 2 := by
    calc
      |⟪v, (S.toCLM - S'.toCLM) v⟫_ℝ| ≤ ‖v‖ * ‖(S.toCLM - S'.toCLM) v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖S.toCLM - S'.toCLM‖ * ‖v‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ v) (norm_nonneg v)
      _ = ‖S.toCLM - S'.toCLM‖ * ‖v‖ ^ 2 := by ring
  have hdiff_le : ⟪v, S.toCLM v⟫_ℝ - ⟪v, S'.toCLM v⟫_ℝ ≤ ‖S.toCLM - S'.toCLM‖ * ‖v‖ ^ 2 := by
    have hsub : ⟪v, S.toCLM v⟫_ℝ - ⟪v, S'.toCLM v⟫_ℝ = ⟪v, (S.toCLM - S'.toCLM) v⟫_ℝ := by
      rw [← inner_sub_right]
      rfl
    rw [hsub]
    exact (le_abs_self _).trans hbound
  have hnorm_le : ‖S.toCLM - S'.toCLM‖ * ‖v‖ ^ 2 ≤ (m / 2) * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hdist.le (sq_nonneg _)
  have hpos_half : 0 ≤ (m / 2) * ‖v‖ ^ 2 := mul_nonneg (half_pos hm).le (sq_nonneg _)
  have hSv := hcoerc v
  linarith

/-- Coarse-graining / congruence map `S ↦ K* ∘ S ∘ K` on symmetric endomorphisms `SymEnd`. -/
def congruenceSymEnd {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (K : H₂ →L[ℝ] H₁) (Kadj : H₁ →L[ℝ] H₂)
    (hadj : ∀ x y, ⟪Kadj x, y⟫_ℝ = ⟪x, K y⟫_ℝ) :
    SymEnd H₁ →ₗ[ℝ] SymEnd H₂ where
  toFun S :=
    ⟨Kadj.comp (S.toCLM.comp K), fun u w => by
      change ⟪u, Kadj (S.toCLM (K w))⟫_ℝ = ⟪Kadj (S.toCLM (K u)), w⟫_ℝ
      calc
        ⟪u, Kadj (S.toCLM (K w))⟫_ℝ = ⟪Kadj (S.toCLM (K w)), u⟫_ℝ := real_inner_comm _ _
        _ = ⟪S.toCLM (K w), K u⟫_ℝ := hadj _ _
        _ = ⟪K u, S.toCLM (K w)⟫_ℝ := real_inner_comm _ _
        _ = ⟪S.toCLM (K u), K w⟫_ℝ := S.symm (K u) (K w)
        _ = ⟪Kadj (S.toCLM (K u)), w⟫_ℝ := (hadj _ _).symm⟩
  map_add' S₁ S₂ := by
    apply SymEnd.ext
    apply ContinuousLinearMap.ext
    intro w
    change Kadj (S₁.toCLM (K w) + S₂.toCLM (K w)) = Kadj (S₁.toCLM (K w)) + Kadj (S₂.toCLM (K w))
    exact map_add Kadj _ _
  map_smul' c S := by
    apply SymEnd.ext
    apply ContinuousLinearMap.ext
    intro w
    change Kadj (c • S.toCLM (K w)) = c • Kadj (S.toCLM (K w))
    exact map_smul Kadj c _

theorem congruenceSymEnd_mem_cone {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
    (K : H₂ →L[ℝ] H₁) (Kadj : H₁ →L[ℝ] H₂)
    (hadj : ∀ x y, ⟪Kadj x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    {S : SymEnd H₁} (hS : S ∈ onsagerBKMProperCone H₁) :
    congruenceSymEnd K Kadj hadj S ∈ onsagerBKMProperCone H₂ := fun w => by
  change 0 ≤ ⟪w, Kadj (S.toCLM (K w))⟫_ℝ
  rw [real_inner_comm, hadj, real_inner_comm]
  exact hS (K w)

/-- Symmetric endomorphism on `EuclideanSpace ℝ (Fin 2)` induced by a symmetric `2 × 2` real matrix. -/
def symEndOfMat2 (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.transpose = M) :
    SymEnd (EuclideanSpace ℝ (Fin 2)) where
  toCLM := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)
  symm u w := by
    change ⟪u, Matrix.toEuclideanLin M w⟫_ℝ = ⟪Matrix.toEuclideanLin M u, w⟫_ℝ
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    change (M *ᵥ w.ofLp) ⬝ᵥ u.ofLp = w.ofLp ⬝ᵥ (M *ᵥ u.ofLp)
    calc
      (M *ᵥ w.ofLp) ⬝ᵥ u.ofLp = u.ofLp ⬝ᵥ (M *ᵥ w.ofLp) := dotProduct_comm _ _
      _ = (u.ofLp ᵥ* M) ⬝ᵥ w.ofLp := dotProduct_mulVec u.ofLp M w.ofLp
      _ = (M.transpose *ᵥ u.ofLp) ⬝ᵥ w.ofLp := by rw [← mulVec_transpose]
      _ = w.ofLp ⬝ᵥ (M *ᵥ u.ofLp) := by rw [hM, dotProduct_comm]

@[simp] theorem symEndOfMat2_inner (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.transpose = M)
    (u w : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, (symEndOfMat2 M hM).toCLM w⟫_ℝ = u.ofLp ⬝ᵥ (M *ᵥ w.ofLp) := by
  change ⟪u, Matrix.toEuclideanLin M w⟫_ℝ = _
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp [Matrix.toEuclideanLin]

private def bkmSampleMat1 : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1]
private def bkmSampleMat2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]

private lemma bkmSampleMat1_symm : bkmSampleMat1.transpose = bkmSampleMat1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bkmSampleMat1]

private lemma bkmSampleMat2_symm : bkmSampleMat2.transpose = bkmSampleMat2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [bkmSampleMat2]

private lemma bkmSample_witness_interior :
    symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm ∈
        interior (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)) :
          Set (SymEnd (EuclideanSpace ℝ (Fin 2)))) ∧
      symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm ∈
        interior (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)) :
          Set (SymEnd (EuclideanSpace ℝ (Fin 2)))) ∧
      (¬ ∃ c : ℝ, 0 < c ∧
        symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm =
          c • symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm) := by
  have hW1 : symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm ∈
      interior (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)) :
        Set (SymEnd (EuclideanSpace ℝ (Fin 2)))) := by
    refine mem_interior_onsagerBKMProperCone_of_coercive _ one_pos fun v => ?_
    rw [symEndOfMat2_inner, EuclideanSpace.norm_sq_eq]
    simp only [bkmSampleMat1, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Real.norm_eq_abs,
      sq_abs, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hW2 : symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm ∈
      interior (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)) :
        Set (SymEnd (EuclideanSpace ℝ (Fin 2)))) := by
    refine mem_interior_onsagerBKMProperCone_of_coercive _ one_pos fun v => ?_
    rw [symEndOfMat2_inner, EuclideanSpace.norm_sq_eq]
    simp only [bkmSampleMat2, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Real.norm_eq_abs,
      sq_abs, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hWray : ¬ ∃ c : ℝ, 0 < c ∧
      symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm =
        c • symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm := by
    rintro ⟨c, _, heq⟩
    let u₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp (2 : ENNReal) ![1, 0]
    let u₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp (2 : ENNReal) ![0, 1]
    have e0 := congrArg (fun x : SymEnd (EuclideanSpace ℝ (Fin 2)) => ⟪u₀, x.toCLM u₀⟫_ℝ) heq
    have e1 := congrArg (fun x : SymEnd (EuclideanSpace ℝ (Fin 2)) => ⟪u₁, x.toCLM u₁⟫_ℝ) heq
    change ⟪u₀, (symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm).toCLM u₀⟫_ℝ =
        ⟪u₀, (c • symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm).toCLM u₀⟫_ℝ at e0
    change ⟪u₁, (symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm).toCLM u₁⟫_ℝ =
        ⟪u₁, (c • symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm).toCLM u₁⟫_ℝ at e1
    rw [SymEnd.toCLM_smul, _root_.smul_apply, real_inner_smul_right,
      symEndOfMat2_inner, symEndOfMat2_inner] at e0 e1
    simp only [u₀, u₁, bkmSampleMat1, bkmSampleMat2,
      dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] at e0 e1
    norm_num at e0 e1
    linarith
  exact ⟨hW1, hW2, hWray⟩

/-- **Bridge 3 (`BirkhoffHilbertChordSectorClosure` ↔ `OperatorFrechetForms` ↔ `OnsagerClosure`)**:
1. Combines Gibbs-BKM log-partition Hessian symmetry (`d_Fr² log Z = 0`) and
   `OnsagerCasimirSystem` `T`-even dissipative symmetry / non-negativity (`dissipative_nonneg`);
2. On any real inner-product space `[Nontrivial H₁]`, establishes unconditional two-ray
   frontier extraction, linear independence, and projective chord cross-ratio formula on
   `onsagerBKMProperCone H₁`, together with metric non-expansion under congruence coarse-graining
   `congruenceSymEnd K Kadj hadj`;
3. Supplies a concrete closed non-collinear coercive witness in
   `interior (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)))` matching `scalarCrossRatio`. -/
theorem gibbsBKM_onsager_birkhoffHilbert_chord_metric
    {nH : ℕ} (H A₀ B₀ : FiniteOperatorAlgebra nH)
    (hSlit : tracedExponential H ∈ Complex.slitPlane)
    {Op : Type*} [Ring Op] [Algebra ℝ Op] (S : OnsagerCasimirSystem Op) (opX opY : Op)
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [Nontrivial H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [Nontrivial H₂]
    (B₁ B₂ : SymEnd H₁)
    (hB₁ : B₁ ∈ interior (onsagerBKMProperCone H₁ : Set (SymEnd H₁)))
    (hB₂ : B₂ ∈ interior (onsagerBKMProperCone H₁ : Set (SymEnd H₁)))
    (hray : ¬ ∃ c : ℝ, 0 < c ∧ B₁ = c • B₂)
    (K : H₂ →L[ℝ] H₁) (Kadj : H₁ →L[ℝ] H₂) (hadj : ∀ x y, ⟪Kadj x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hKB₁ : congruenceSymEnd K Kadj hadj B₁ ∈ interior (onsagerBKMProperCone H₂ : Set (SymEnd H₂)))
    (hKB₂ : congruenceSymEnd K Kadj hadj B₂ ∈ interior (onsagerBKMProperCone H₂ : Set (SymEnd H₂))) :
    (secondFDerivLogPartitionReadout H A₀ B₀ = secondFDerivLogPartitionReadout H B₀ A₀ ∧
      S.dissipative opX opY = S.dissipative opY opX ∧
      0 ≤ S.dissipative opX opX ∧
      S.reversible opX opX = 0) ∧
    (extremalRayLeft (onsagerBKMProperCone H₁) B₁ B₂ ∈
        frontier (onsagerBKMProperCone H₁ : Set (SymEnd H₁)) ∧
      extremalRayRight (onsagerBKMProperCone H₁) B₁ B₂ ∈
        frontier (onsagerBKMProperCone H₁ : Set (SymEnd H₁)) ∧
      LinearIndependent ℝ ![extremalRayLeft (onsagerBKMProperCone H₁) B₁ B₂,
        extremalRayRight (onsagerBKMProperCone H₁) B₁ B₂] ∧
      birkhoffHilbertMetric (onsagerBKMProperCone H₁) B₁ B₂ =
        (1 / 2 : ℝ) * Real.log (scalarCrossRatio 0
          (1 / (upperGauge (onsagerBKMProperCone H₁) B₁ B₂ + 1))
          (upperGauge (onsagerBKMProperCone H₁) B₂ B₁ /
            (upperGauge (onsagerBKMProperCone H₁) B₂ B₁ + 1)) 1)) ∧
    birkhoffHilbertMetric (onsagerBKMProperCone H₂)
        (congruenceSymEnd K Kadj hadj B₁) (congruenceSymEnd K Kadj hadj B₂) ≤
      birkhoffHilbertMetric (onsagerBKMProperCone H₁) B₁ B₂ ∧
    (let W₁ := symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm
     let W₂ := symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm
     W₁ ∈ interior (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)) :
       Set (SymEnd (EuclideanSpace ℝ (Fin 2)))) ∧
     W₂ ∈ interior (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)) :
       Set (SymEnd (EuclideanSpace ℝ (Fin 2)))) ∧
     (¬ ∃ c : ℝ, 0 < c ∧ W₁ = c • W₂) ∧
     birkhoffHilbertMetric (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2))) W₁ W₂ =
       (1 / 2 : ℝ) * Real.log (scalarCrossRatio 0
         (1 / (upperGauge (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2))) W₁ W₂ + 1))
         (upperGauge (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2))) W₂ W₁ /
           (upperGauge (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2))) W₂ W₁ + 1)) 1)) := by
  have hsal1 := onsagerBKMProperCone_salient H₁
  have hsal2 := onsagerBKMProperCone_salient H₂
  have hchord := birkhoffHilbertMetric_arbitrary_endpoints_projective_chord
    (onsagerBKMProperCone H₁) hsal1 hB₁ hB₂ hray
  have hlin := extremalRays_linearIndependent (onsagerBKMProperCone H₁) hsal1 hB₁ hB₂ hray
  have hmap := birkhoffHilbertMetric_map_le
    (onsagerBKMProperCone H₁) (onsagerBKMProperCone H₂) hsal2
    (congruenceSymEnd K Kadj hadj)
    (fun _ hmem => congruenceSymEnd_mem_cone K Kadj hadj hmem)
    hB₁ hB₂ hKB₁ hKB₂
  have ⟨hW1, hW2, hWray⟩ := bkmSample_witness_interior
  have hWchord := birkhoffHilbertMetric_arbitrary_endpoints_projective_chord
    (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)))
    (onsagerBKMProperCone_salient (EuclideanSpace ℝ (Fin 2))) hW1 hW2 hWray
  refine ⟨⟨secondFDerivLogPartitionReadout_symm_of_extDeriv_sq_zero H A₀ B₀ hSlit,
    S.dissipative_symm opX opY, S.dissipative_nonneg opX, S.reversible_diag_zero opX⟩,
    ⟨hchord.1, hchord.2.1, hlin, hchord.2.2.2.2.2.2.2⟩,
    hmap,
    ⟨hW1, hW2, hWray, hWchord.2.2.2.2.2.2.2⟩⟩

end Bridge3_OnsagerBKMBirkhoffHilbert

/-! ## Bridge 4: Binary Icosahedral `2I ⊂ SU(2) ↪ spinGroup(q₃,₀)` & `2I`-Equivariant Clifford 1-Forms -/

section Bridge4_BinaryIcosahedralSpin30CliffordOneForms

/-- Positive-definite quadratic form `q₃,₀(v) = v₀² + v₁² + v₂²` on `Fin 3 → ℝ`. -/
def q30 : QuadraticForm ℝ (Fin 3 → ℝ) :=
  ∑ i : Fin 3, QuadraticMap.sq.comp (LinearMap.proj i)

@[simp] theorem q30_apply (v : Fin 3 → ℝ) :
    q30 v = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := by
  unfold q30
  rw [_root_.sum_apply]
  simp [Fin.sum_univ_three, QuadraticMap.sq_apply, add_assoc]

theorem q30_polar (u v : Fin 3 → ℝ) :
    QuadraticMap.polar q30 u v = 2 * (u ⬝ᵥ v) := by
  simp only [QuadraticMap.polar, q30_apply, Pi.add_apply, dotProduct, Fin.sum_univ_three]
  ring

private def e30_0 : Fin 3 → ℝ := ![1, 0, 0]
private def e30_1 : Fin 3 → ℝ := ![0, 1, 0]
private def e30_2 : Fin 3 → ℝ := ![0, 0, 1]

private def clE1 : CliffordAlgebra q30 := CliffordAlgebra.ι q30 e30_0
private def clE2 : CliffordAlgebra q30 := CliffordAlgebra.ι q30 e30_1
private def clE3 : CliffordAlgebra q30 := CliffordAlgebra.ι q30 e30_2

/-- Oriented quaternion units in `Cl⁰(3, 0)` using minus signs
`i ↦ -e₂ e₃`, `j ↦ -e₃ e₁`, `k ↦ -e₁ e₂` so `i * j = k` holds exactly. -/
def clQuatI : CliffordAlgebra q30 := -(clE2 * clE3)
def clQuatJ : CliffordAlgebra q30 := -(clE3 * clE1)
def clQuatK : CliffordAlgebra q30 := -(clE1 * clE2)

private lemma clE_sq :
    clE1 * clE1 = 1 ∧ clE2 * clE2 = 1 ∧ clE3 * clE3 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · change CliffordAlgebra.ι q30 e30_0 * CliffordAlgebra.ι q30 e30_0 = 1
    rw [CliffordAlgebra.ι_sq_scalar]
    have hq : q30 e30_0 = 1 := by simp [e30_0]
    rw [hq, map_one]
  · change CliffordAlgebra.ι q30 e30_1 * CliffordAlgebra.ι q30 e30_1 = 1
    rw [CliffordAlgebra.ι_sq_scalar]
    have hq : q30 e30_1 = 1 := by simp [e30_1]
    rw [hq, map_one]
  · change CliffordAlgebra.ι q30 e30_2 * CliffordAlgebra.ι q30 e30_2 = 1
    rw [CliffordAlgebra.ι_sq_scalar]
    have hq : q30 e30_2 = 1 := by simp [e30_2]
    rw [hq, map_one]

private lemma clE_anticomm :
    clE1 * clE2 = -(clE2 * clE1) ∧
      clE2 * clE3 = -(clE3 * clE2) ∧
      clE3 * clE1 = -(clE1 * clE3) := by
  have h12 : clE1 * clE2 + clE2 * clE1 = 0 := by
    change CliffordAlgebra.ι q30 e30_0 * CliffordAlgebra.ι q30 e30_1 +
        CliffordAlgebra.ι q30 e30_1 * CliffordAlgebra.ι q30 e30_0 = 0
    rw [CliffordAlgebra.ι_mul_ι_add_swap, q30_polar]
    have hd : e30_0 ⬝ᵥ e30_1 = 0 := by
      simp [e30_0, e30_1, dotProduct, Fin.sum_univ_three]
    rw [hd, mul_zero, map_zero]
  have h23 : clE2 * clE3 + clE3 * clE2 = 0 := by
    change CliffordAlgebra.ι q30 e30_1 * CliffordAlgebra.ι q30 e30_2 +
        CliffordAlgebra.ι q30 e30_2 * CliffordAlgebra.ι q30 e30_1 = 0
    rw [CliffordAlgebra.ι_mul_ι_add_swap, q30_polar]
    have hd : e30_1 ⬝ᵥ e30_2 = 0 := by
      simp [e30_1, e30_2, dotProduct, Fin.sum_univ_three]
    rw [hd, mul_zero, map_zero]
  have h31 : clE3 * clE1 + clE1 * clE3 = 0 := by
    change CliffordAlgebra.ι q30 e30_2 * CliffordAlgebra.ι q30 e30_0 +
        CliffordAlgebra.ι q30 e30_0 * CliffordAlgebra.ι q30 e30_2 = 0
    rw [CliffordAlgebra.ι_mul_ι_add_swap, q30_polar]
    have hd : e30_2 ⬝ᵥ e30_0 = 0 := by
      simp [e30_2, e30_0, dotProduct, Fin.sum_univ_three]
    rw [hd, mul_zero, map_zero]
  exact ⟨eq_neg_of_add_eq_zero_left h12, eq_neg_of_add_eq_zero_left h23,
    eq_neg_of_add_eq_zero_left h31⟩

private lemma clQuat_relations :
    clQuatI * clQuatI = -1 ∧ clQuatJ * clQuatJ = -1 ∧ clQuatK * clQuatK = -1 ∧
      clQuatI * clQuatJ = clQuatK ∧ clQuatJ * clQuatK = clQuatI ∧ clQuatK * clQuatI = clQuatJ ∧
      clQuatJ * clQuatI = -clQuatK ∧ clQuatK * clQuatJ = -clQuatI ∧ clQuatI * clQuatK = -clQuatJ := by
  have ⟨h11, h22, h33⟩ := clE_sq
  have ⟨h12, h23, h31⟩ := clE_anticomm
  have h21 : clE2 * clE1 = -(clE1 * clE2) := by rw [h12, neg_neg]
  have h32 : clE3 * clE2 = -(clE2 * clE3) := by rw [h23, neg_neg]
  have h13 : clE1 * clE3 = -(clE3 * clE1) := by rw [h31, neg_neg]
  have hii : clQuatI * clQuatI = -1 := by
    dsimp [clQuatI]
    calc
      (-(clE2 * clE3)) * (-(clE2 * clE3)) = clE2 * (clE3 * clE2) * clE3 := by noncomm_ring
      _ = clE2 * (-(clE2 * clE3)) * clE3 := by rw [h32]
      _ = -((clE2 * clE2) * (clE3 * clE3)) := by noncomm_ring
      _ = -1 := by rw [h22, h33, mul_one]
  have hjj : clQuatJ * clQuatJ = -1 := by
    dsimp [clQuatJ]
    calc
      (-(clE3 * clE1)) * (-(clE3 * clE1)) = clE3 * (clE1 * clE3) * clE1 := by noncomm_ring
      _ = clE3 * (-(clE3 * clE1)) * clE1 := by rw [h13]
      _ = -((clE3 * clE3) * (clE1 * clE1)) := by noncomm_ring
      _ = -1 := by rw [h33, h11, mul_one]
  have hkk : clQuatK * clQuatK = -1 := by
    dsimp [clQuatK]
    calc
      (-(clE1 * clE2)) * (-(clE1 * clE2)) = clE1 * (clE2 * clE1) * clE2 := by noncomm_ring
      _ = clE1 * (-(clE1 * clE2)) * clE2 := by rw [h21]
      _ = -((clE1 * clE1) * (clE2 * clE2)) := by noncomm_ring
      _ = -1 := by rw [h11, h22, mul_one]
  have hij : clQuatI * clQuatJ = clQuatK := by
    dsimp [clQuatI, clQuatJ, clQuatK]
    calc
      (-(clE2 * clE3)) * (-(clE3 * clE1)) = clE2 * (clE3 * clE3) * clE1 := by noncomm_ring
      _ = clE2 * clE1 := by rw [h33, mul_one]
      _ = -(clE1 * clE2) := h21
  have hjk : clQuatJ * clQuatK = clQuatI := by
    dsimp [clQuatI, clQuatJ, clQuatK]
    calc
      (-(clE3 * clE1)) * (-(clE1 * clE2)) = clE3 * (clE1 * clE1) * clE2 := by noncomm_ring
      _ = clE3 * clE2 := by rw [h11, mul_one]
      _ = -(clE2 * clE3) := h32
  have hki : clQuatK * clQuatI = clQuatJ := by
    dsimp [clQuatI, clQuatJ, clQuatK]
    calc
      (-(clE1 * clE2)) * (-(clE2 * clE3)) = clE1 * (clE2 * clE2) * clE3 := by noncomm_ring
      _ = clE1 * clE3 := by rw [h22, mul_one]
      _ = -(clE3 * clE1) := h13
  have hji : clQuatJ * clQuatI = -clQuatK := by
    calc
      clQuatJ * clQuatI = (clQuatK * clQuatI) * clQuatI := by rw [hki]
      _ = clQuatK * (clQuatI * clQuatI) := mul_assoc _ _ _
      _ = -clQuatK := by rw [hii]; noncomm_ring
  have hkj : clQuatK * clQuatJ = -clQuatI := by
    calc
      clQuatK * clQuatJ = (clQuatI * clQuatJ) * clQuatJ := by rw [hij]
      _ = clQuatI * (clQuatJ * clQuatJ) := mul_assoc _ _ _
      _ = -clQuatI := by rw [hjj]; noncomm_ring
  have hik : clQuatI * clQuatK = -clQuatJ := by
    calc
      clQuatI * clQuatK = (clQuatJ * clQuatK) * clQuatK := by rw [hjk]
      _ = clQuatJ * (clQuatK * clQuatK) := mul_assoc _ _ _
      _ = -clQuatJ := by rw [hkk]; noncomm_ring
  exact ⟨hii, hjj, hkk, hij, hjk, hki, hji, hkj, hik⟩

/-- Embed quaternion coordinates `(a, b, c, d)` into the oriented even subalgebra `Cl⁰(3, 0)`. -/
def quatToCl30 (a b c d : ℝ) : CliffordAlgebra q30 :=
  algebraMap ℝ _ a + b • clQuatI + c • clQuatJ + d • clQuatK

private lemma ι_q30_expand (v : Fin 3 → ℝ) :
    CliffordAlgebra.ι q30 v = v 0 • clE1 + v 1 • clE2 + v 2 • clE3 := by
  have hv : v = v 0 • e30_0 + v 1 • e30_1 + v 2 • e30_2 := by
    ext i
    fin_cases i <;> simp [e30_0, e30_1, e30_2]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, clE1, clE2, clE3]

private lemma ι_q30_mul_ι_q30 (u w : Fin 3 → ℝ) :
    CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w =
      quatToCl30 (u 0 * w 0 + u 1 * w 1 + u 2 * w 2)
        (u 2 * w 1 - u 1 * w 2)
        (u 0 * w 2 - u 2 * w 0)
        (u 1 * w 0 - u 0 * w 1) := by
  have ⟨h11, h22, h33⟩ := clE_sq
  have ⟨h12, h23, h31⟩ := clE_anticomm
  rw [ι_q30_expand u, ι_q30_expand w]
  simp only [quatToCl30, clQuatI, clQuatJ, clQuatK, Algebra.algebraMap_eq_smul_one]
  calc
    (u 0 • clE1 + u 1 • clE2 + u 2 • clE3) * (w 0 • clE1 + w 1 • clE2 + w 2 • clE3)
        = (u 0 * w 0) • (clE1 * clE1) + (u 1 * w 1) • (clE2 * clE2) + (u 2 * w 2) • (clE3 * clE3) +
            (u 0 * w 1) • (clE1 * clE2) + (u 1 * w 0) • (clE2 * clE1) +
            (u 1 * w 2) • (clE2 * clE3) + (u 2 * w 1) • (clE3 * clE2) +
            (u 2 * w 0) • (clE3 * clE1) + (u 0 * w 2) • (clE1 * clE3) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
          module
    _ = (u 0 * w 0) • 1 + (u 1 * w 1) • 1 + (u 2 * w 2) • 1 +
            (u 0 * w 1) • (clE1 * clE2) + (u 1 * w 0) • -(clE1 * clE2) +
            (u 1 * w 2) • (clE2 * clE3) + (u 2 * w 1) • -(clE2 * clE3) +
            (u 2 * w 0) • (clE3 * clE1) + (u 0 * w 2) • -(clE3 * clE1) := by
          rw [h11, h22, h33, h12, neg_neg, h23, neg_neg, h31, neg_neg]
    _ = (u 0 * w 0 + u 1 * w 1 + u 2 * w 2) • (1 : CliffordAlgebra q30) +
          (u 2 * w 1 - u 1 * w 2) • -(clE2 * clE3) +
          (u 0 * w 2 - u 2 * w 0) • -(clE3 * clE1) +
          (u 1 * w 0 - u 0 * w 1) • -(clE1 * clE2) := by
          simp only [smul_neg, sub_smul, add_smul]
          module

private lemma unit_vec_mul_mem_spinGroup_q30 {u w : Fin 3 → ℝ}
    (hu : q30 u = 1) (hw : q30 w = 1) :
    CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w ∈ spinGroup q30 := by
  have hu_sq : CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 u = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar, hu, map_one]
  have hw_sq : CliffordAlgebra.ι q30 w * CliffordAlgebra.ι q30 w = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar, hw, map_one]
  let uU : (CliffordAlgebra q30)ˣ := ⟨CliffordAlgebra.ι q30 u, CliffordAlgebra.ι q30 u, hu_sq, hu_sq⟩
  let wU : (CliffordAlgebra q30)ˣ := ⟨CliffordAlgebra.ι q30 w, CliffordAlgebra.ι q30 w, hw_sq, hw_sq⟩
  have hu_lip : uU ∈ lipschitzGroup q30 :=
    Subgroup.subset_closure ⟨u, rfl⟩
  have hw_lip : wU ∈ lipschitzGroup q30 :=
    Subgroup.subset_closure ⟨w, rfl⟩
  have hmul_lip :
      CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w ∈
        (lipschitzGroup q30).toSubmonoid.map
          (Units.coeHom (CliffordAlgebra q30)) :=
    ⟨uU * wU, Subgroup.mul_mem _ hu_lip hw_lip, rfl⟩
  have heven :
      CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w ∈ CliffordAlgebra.even q30 :=
    CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero q30 u w
  have hstar :
      star (CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w) =
        CliffordAlgebra.ι q30 w * CliffordAlgebra.ι q30 u := by
    rw [CliffordAlgebra.star_def, CliffordAlgebra.involute_eq_of_mem_even heven,
      CliffordAlgebra.reverse.map_mul, CliffordAlgebra.reverse_ι, CliffordAlgebra.reverse_ι]
  have hunit : CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w ∈ unitary (CliffordAlgebra q30) := by
    rw [Unitary.mem_iff, hstar]
    refine ⟨?_, ?_⟩
    · calc
        (CliffordAlgebra.ι q30 w * CliffordAlgebra.ι q30 u) *
            (CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w)
            = CliffordAlgebra.ι q30 w *
                (CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 u) *
                CliffordAlgebra.ι q30 w := by noncomm_ring
        _ = 1 := by rw [hu_sq, mul_one, hw_sq]
    · calc
        (CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w) *
            (CliffordAlgebra.ι q30 w * CliffordAlgebra.ι q30 u)
            = CliffordAlgebra.ι q30 u *
                (CliffordAlgebra.ι q30 w * CliffordAlgebra.ι q30 w) *
                CliffordAlgebra.ι q30 u := by noncomm_ring
        _ = 1 := by rw [hw_sq, mul_one, hu_sq]
  exact ⟨⟨hmul_lip, hunit⟩, heven⟩

private theorem quatToCl30_mem_spinGroup {a b c d : ℝ}
    (hnorm : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) :
    quatToCl30 a b c d ∈ spinGroup q30 := by
  by_cases hbc : b ^ 2 + c ^ 2 = 0
  · have hb0 : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    have hc0 : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    subst hb0; subst hc0
    let u : Fin 3 → ℝ := ![1, 0, 0]
    let w : Fin 3 → ℝ := ![a, -d, 0]
    have hu : q30 u = 1 := by simp [u]
    have hw : q30 w = 1 := by simp [w]; linarith
    have heq : CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w = quatToCl30 a 0 0 d := by
      rw [ι_q30_mul_ι_q30]
      simp [u, w]
    rw [← heq]
    exact unit_vec_mul_mem_spinGroup_q30 hu hw
  · have hbc_pos : 0 < b ^ 2 + c ^ 2 :=
      lt_of_le_of_ne (add_nonneg (sq_nonneg b) (sq_nonneg c)) (Ne.symm hbc)
    let r : ℝ := Real.sqrt (b ^ 2 + c ^ 2)
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hbc_pos
    have hr_sq : r ^ 2 = b ^ 2 + c ^ 2 := Real.sq_sqrt hbc_pos.le
    let u : Fin 3 → ℝ := ![c / r, -b / r, 0]
    let w : Fin 3 → ℝ := ![(a * c - b * d) / r, (-a * b - c * d) / r, r]
    have hu : q30 u = 1 := by
      simp only [q30_apply, u, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hr_pos.ne']
      rw [hr_sq]
      ring
    have hw : q30 w = 1 := by
      simp only [q30_apply, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hr_pos.ne']
      have hr4 : r ^ 4 = (b ^ 2 + c ^ 2) ^ 2 := by
        calc
          r ^ 4 = (r ^ 2) ^ 2 := by ring
          _ = (b ^ 2 + c ^ 2) ^ 2 := by rw [hr_sq]
      rw [hr4, hr_sq]
      nlinarith [hnorm]
    have ha : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 = a := by
      simp only [u, w, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      field_simp [hr_pos.ne']
      rw [hr_sq]
      ring
    have hb : u 2 * w 1 - u 1 * w 2 = b := by
      simp only [u, w, Matrix.cons_val]
      field_simp [hr_pos.ne']
      ring
    have hc : u 0 * w 2 - u 2 * w 0 = c := by
      simp only [u, w, Matrix.cons_val_zero, Matrix.cons_val]
      field_simp [hr_pos.ne']
      ring
    have hd : u 1 * w 0 - u 0 * w 1 = d := by
      simp only [u, w, Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp [hr_pos.ne']
      rw [hr_sq]
      ring
    have heq : CliffordAlgebra.ι q30 u * CliffordAlgebra.ι q30 w = quatToCl30 a b c d := by
      rw [ι_q30_mul_ι_q30, ha, hb, hc, hd]
    rw [← heq]
    exact unit_vec_mul_mem_spinGroup_q30 hu hw

private theorem quatToCl30_mul (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    quatToCl30 a₁ b₁ c₁ d₁ * quatToCl30 a₂ b₂ c₂ d₂ =
      quatToCl30
        (a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂)
        (a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂)
        (a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂)
        (a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂) := by
  have ⟨hii, hjj, hkk, hij, hjk, hki, hji, hkj, hik⟩ := clQuat_relations
  simp only [quatToCl30, Algebra.algebraMap_eq_smul_one]
  calc
    (a₁ • (1 : CliffordAlgebra q30) + b₁ • clQuatI + c₁ • clQuatJ + d₁ • clQuatK) *
        (a₂ • (1 : CliffordAlgebra q30) + b₂ • clQuatI + c₂ • clQuatJ + d₂ • clQuatK)
        = (a₁ * a₂) • 1 + (b₁ * b₂) • (clQuatI * clQuatI) +
            (c₁ * c₂) • (clQuatJ * clQuatJ) + (d₁ * d₂) • (clQuatK * clQuatK) +
            (a₁ * b₂ + b₁ * a₂) • clQuatI + (a₁ * c₂ + c₁ * a₂) • clQuatJ +
            (a₁ * d₂ + d₁ * a₂) • clQuatK +
            (b₁ * c₂) • (clQuatI * clQuatJ) + (c₁ * b₂) • (clQuatJ * clQuatI) +
            (c₁ * d₂) • (clQuatJ * clQuatK) + (d₁ * c₂) • (clQuatK * clQuatJ) +
            (d₁ * b₂) • (clQuatK * clQuatI) + (b₁ * d₂) • (clQuatI * clQuatK) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
          module
    _ = (a₁ * a₂) • 1 + (b₁ * b₂) • (-1) + (c₁ * c₂) • (-1) + (d₁ * d₂) • (-1) +
            (a₁ * b₂ + b₁ * a₂) • clQuatI + (a₁ * c₂ + c₁ * a₂) • clQuatJ +
            (a₁ * d₂ + d₁ * a₂) • clQuatK +
            (b₁ * c₂) • clQuatK + (c₁ * b₂) • (-clQuatK) +
            (c₁ * d₂) • clQuatI + (d₁ * c₂) • (-clQuatI) +
            (d₁ * b₂) • clQuatJ + (b₁ * d₂) • (-clQuatJ) := by
          rw [hii, hjj, hkk, hij, hji, hjk, hkj, hki, hik]
    _ = (a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂) • (1 : CliffordAlgebra q30) +
          (a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂) • clQuatI +
          (a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂) • clQuatJ +
          (a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂) • clQuatK := by
          simp only [smul_neg, sub_smul, add_smul]
          module

private lemma su2_eq_quatToMat (g : SU2) :
    let a := (g.1 0 0).re
    let b := (g.1 0 0).im
    let c := (g.1 0 1).re
    let d := (g.1 0 1).im
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 ∧ (g : Mat2C) = quatToMat a b c d := by
  intro a b c d
  have hmem := g.2
  rw [Matrix.mem_specialUnitaryGroup_iff] at hmem
  rcases hmem with ⟨hU, hdet⟩
  have hU_mul : g.1 * star g.1 = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  rw [Matrix.mem_unitaryGroup_iff'] at hU
  have hadj : star g.1 = Matrix.adjugate g.1 := by
    have hmul : g.1 * Matrix.adjugate g.1 = 1 := by
      rw [Matrix.mul_adjugate, hdet, one_smul]
    calc
      star g.1 = star g.1 * 1 := (Matrix.mul_one _).symm
      _ = star g.1 * (g.1 * Matrix.adjugate g.1) := by rw [hmul]
      _ = (star g.1 * g.1) * Matrix.adjugate g.1 := (Matrix.mul_assoc _ _ _).symm
      _ = 1 * Matrix.adjugate g.1 := by rw [hU]
      _ = Matrix.adjugate g.1 := Matrix.one_mul _
  have h11 : g.1 1 1 = star (g.1 0 0) := by
    have e00 : (star g.1) 0 0 = (Matrix.adjugate g.1) 0 0 := congrArg (fun M : Mat2C => M 0 0) hadj
    simpa [Matrix.star_apply, Matrix.adjugate_fin_two] using e00.symm
  have h10 : g.1 1 0 = -star (g.1 0 1) := by
    have e10 : (star g.1) 1 0 = (Matrix.adjugate g.1) 1 0 := congrArg (fun M : Mat2C => M 1 0) hadj
    have e10' : star (g.1 0 1) = -g.1 1 0 := by
      simpa [Matrix.star_apply, Matrix.adjugate_fin_two] using e10
    calc
      g.1 1 0 = - -g.1 1 0 := (neg_neg _).symm
      _ = -star (g.1 0 1) := by rw [← e10']
  have h00_one : (g.1 * star g.1) 0 0 = 1 := congrArg (fun M : Mat2C => M 0 0) hU_mul
  have hnorm_re := congrArg Complex.re h00_one
  simp only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two, RCLike.star_def,
    Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.mul_re, Complex.one_re] at hnorm_re
  have hnorm : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
    dsimp [a, b, c, d]
    linarith [hnorm_re]
  have hmat : (g : Mat2C) = quatToMat a b c d := by
    ext i j
    fin_cases i <;> fin_cases j
    · change g.1 0 0 = (a : ℂ) + b * Complex.I
      apply Complex.ext <;> simp [a, b]
    · change g.1 0 1 = (c : ℂ) + d * Complex.I
      apply Complex.ext <;> simp [c, d]
    · change g.1 1 0 = -(c : ℂ) + d * Complex.I
      rw [h10]
      apply Complex.ext <;> simp [c, d]
    · change g.1 1 1 = (a : ℂ) - b * Complex.I
      rw [h11]
      apply Complex.ext <;> simp [a, b]
  exact ⟨hnorm, hmat⟩

private lemma quatToMat_mul_re_im (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    ((quatToMat a₁ b₁ c₁ d₁ * quatToMat a₂ b₂ c₂ d₂) 0 0).re =
        a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂ ∧
      ((quatToMat a₁ b₁ c₁ d₁ * quatToMat a₂ b₂ c₂ d₂) 0 0).im =
        a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂ ∧
      ((quatToMat a₁ b₁ c₁ d₁ * quatToMat a₂ b₂ c₂ d₂) 0 1).re =
        a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂ ∧
      ((quatToMat a₁ b₁ c₁ d₁ * quatToMat a₂ b₂ c₂ d₂) 0 1).im =
        a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂ := by
  simp only [quatToMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- Injectively lift `g ∈ SU(2)` into `spinGroup q30 ⊂ Cl⁰(3, 0)` using the oriented
quaternion correspondence `(i, j, k) ↦ (-e₂e₃, -e₃e₁, -e₁e₂)`. -/
def su2ToSpin30Hom : SU2 →* spinGroup q30 where
  toFun g :=
    let a := (g.1 0 0).re
    let b := (g.1 0 0).im
    let c := (g.1 0 1).re
    let d := (g.1 0 1).im
    ⟨quatToCl30 a b c d, quatToCl30_mem_spinGroup (su2_eq_quatToMat g).1⟩
  map_one' := by
    apply Subtype.ext
    change quatToCl30 (((1 : Mat2C) 0 0).re) (((1 : Mat2C) 0 0).im)
      (((1 : Mat2C) 0 1).re) (((1 : Mat2C) 0 1).im) = 1
    simp [quatToCl30]
  map_mul' g₁ g₂ := by
    apply Subtype.ext
    have h1 := (su2_eq_quatToMat g₁).2
    have h2 := (su2_eq_quatToMat g₂).2
    let a₁ := (g₁.1 0 0).re; let b₁ := (g₁.1 0 0).im
    let c₁ := (g₁.1 0 1).re; let d₁ := (g₁.1 0 1).im
    let a₂ := (g₂.1 0 0).re; let b₂ := (g₂.1 0 0).im
    let c₂ := (g₂.1 0 1).re; let d₂ := (g₂.1 0 1).im
    have hm12 : ((g₁ * g₂ : SU2) : Mat2C) = quatToMat a₁ b₁ c₁ d₁ * quatToMat a₂ b₂ c₂ d₂ := by
      change (g₁ : Mat2C) * (g₂ : Mat2C) = _
      rw [h1, h2]
    have hri := quatToMat_mul_re_im a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂
    have ha0 : (((g₁ * g₂ : SU2) : Mat2C) 0 0).re = a₁ * a₂ - b₁ * b₂ - c₁ * c₂ - d₁ * d₂ := by
      rw [hm12]; exact hri.1
    have hb0 : (((g₁ * g₂ : SU2) : Mat2C) 0 0).im = a₁ * b₂ + b₁ * a₂ + c₁ * d₂ - d₁ * c₂ := by
      rw [hm12]; exact hri.2.1
    have hc0 : (((g₁ * g₂ : SU2) : Mat2C) 0 1).re = a₁ * c₂ - b₁ * d₂ + c₁ * a₂ + d₁ * b₂ := by
      rw [hm12]; exact hri.2.2.1
    have hd0 : (((g₁ * g₂ : SU2) : Mat2C) 0 1).im = a₁ * d₂ + b₁ * c₂ - c₁ * b₂ + d₁ * a₂ := by
      rw [hm12]; exact hri.2.2.2
    change quatToCl30 (((g₁ * g₂ : SU2) : Mat2C) 0 0).re (((g₁ * g₂ : SU2) : Mat2C) 0 0).im
        (((g₁ * g₂ : SU2) : Mat2C) 0 1).re (((g₁ * g₂ : SU2) : Mat2C) 0 1).im =
      quatToCl30 a₁ b₁ c₁ d₁ * quatToCl30 a₂ b₂ c₂ d₂
    rw [ha0, hb0, hc0, hd0, ← quatToCl30_mul]

private def pauliX : Mat2C := !![(0 : ℂ), 1; 1, 0]
private def pauliY : Mat2C := !![(0 : ℂ), -Complex.I; Complex.I, 0]
private def pauliZ : Mat2C := !![(1 : ℂ), 0; 0, -1]

private def pauliVecLin : (Fin 3 → ℝ) →ₗ[ℝ] Mat2C where
  toFun v := (v 0 : ℂ) • pauliZ + (v 1 : ℂ) • pauliY + (v 2 : ℂ) • pauliX
  map_add' u v := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [pauliZ, pauliY, pauliX]
      try ring
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [pauliZ, pauliY, pauliX]
      try ring

private lemma pauliVecLin_apply (v : Fin 3 → ℝ) :
    pauliVecLin v =
      !![(v 0 : ℂ), (v 2 : ℂ) - (v 1 : ℂ) * Complex.I;
         (v 2 : ℂ) + (v 1 : ℂ) * Complex.I, -(v 0 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [pauliVecLin, pauliZ, pauliY, pauliX]
    try ring

private lemma pauliVecLin_sq (v : Fin 3 → ℝ) :
    pauliVecLin v * pauliVecLin v = algebraMap ℝ Mat2C (q30 v) := by
  rw [pauliVecLin_apply v]
  let M : Mat2C :=
    !![(v 0 : ℂ), (v 2 : ℂ) - (v 1 : ℂ) * Complex.I;
       (v 2 : ℂ) + (v 1 : ℂ) * Complex.I, -(v 0 : ℂ)]
  change M * M = algebraMap ℝ Mat2C (q30 v)
  have h00 : (M * M) 0 0 = algebraMap ℝ Mat2C (q30 v) 0 0 := by
    simp [M, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one,
      Complex.real_smul, q30_apply]
    linear_combination -((v 1 : ℂ) ^ 2) * Complex.I_mul_I
  have h01 : (M * M) 0 1 = algebraMap ℝ Mat2C (q30 v) 0 1 := by
    simp [M, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one]
    ring
  have h10 : (M * M) 1 0 = algebraMap ℝ Mat2C (q30 v) 1 0 := by
    simp [M, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one]
    ring
  have h11 : (M * M) 1 1 = algebraMap ℝ Mat2C (q30 v) 1 1 := by
    simp [M, Matrix.mul_apply, Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one,
      Complex.real_smul, q30_apply]
    linear_combination -((v 1 : ℂ) ^ 2) * Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- Faithful Pauli `ℝ`-algebra homomorphism `Cl(q₃,₀) →ₐ[ℝ] M₂(ℂ)` sending
`(e₁, e₂, e₃) ↦ (σ_z, σ_y, σ_x)` so `quatToCl30 a b c d ↦ quatToMat a b c d`. -/
def cl30ToMat2C : CliffordAlgebra q30 →ₐ[ℝ] Mat2C :=
  CliffordAlgebra.lift q30 ⟨pauliVecLin, pauliVecLin_sq⟩

private lemma cl30ToMat2C_generators :
    cl30ToMat2C clE1 = pauliZ ∧ cl30ToMat2C clE2 = pauliY ∧ cl30ToMat2C clE3 = pauliX := by
  refine ⟨?_, ?_, ?_⟩
  · change cl30ToMat2C (CliffordAlgebra.ι q30 e30_0) = pauliZ
    rw [cl30ToMat2C, CliffordAlgebra.lift_ι_apply]
    simp [pauliVecLin, e30_0]
  · change cl30ToMat2C (CliffordAlgebra.ι q30 e30_1) = pauliY
    rw [cl30ToMat2C, CliffordAlgebra.lift_ι_apply]
    simp [pauliVecLin, e30_1]
  · change cl30ToMat2C (CliffordAlgebra.ι q30 e30_2) = pauliX
    rw [cl30ToMat2C, CliffordAlgebra.lift_ι_apply]
    simp [pauliVecLin, e30_2]

private lemma cl30ToMat2C_quatToCl30 (a b c d : ℝ) :
    cl30ToMat2C (quatToCl30 a b c d) = quatToMat a b c d := by
  have ⟨he1, he2, he3⟩ := cl30ToMat2C_generators
  have hI : cl30ToMat2C clQuatI = quatToMat 0 1 0 0 := by
    dsimp [clQuatI]
    rw [map_neg, map_mul, he2, he3]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY, pauliX, quatToMat]
  have hJ : cl30ToMat2C clQuatJ = quatToMat 0 0 1 0 := by
    dsimp [clQuatJ]
    rw [map_neg, map_mul, he3, he1]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliZ, quatToMat]
  have hK : cl30ToMat2C clQuatK = quatToMat 0 0 0 1 := by
    dsimp [clQuatK]
    rw [map_neg, map_mul, he1, he2]
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, pauliY, quatToMat]
  rw [quatToCl30, map_add, map_add, map_add, cl30ToMat2C.commutes,
    map_smul, map_smul, map_smul, hI, hJ, hK]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [quatToMat, Algebra.algebraMap_eq_smul_one]
    try ring

theorem cl30ToMat2C_su2ToSpin30Hom (g : SU2) :
    cl30ToMat2C (su2ToSpin30Hom g : CliffordAlgebra q30) = (g : Mat2C) := by
  change cl30ToMat2C (quatToCl30 (g.1 0 0).re (g.1 0 0).im (g.1 0 1).re (g.1 0 1).im) = (g : Mat2C)
  rw [cl30ToMat2C_quatToCl30, ← (su2_eq_quatToMat g).2]

theorem su2ToSpin30Hom_injective : Function.Injective su2ToSpin30Hom := by
  intro g₁ g₂ heq
  apply Subtype.ext
  have h1 := congrArg (fun s : spinGroup q30 => cl30ToMat2C (s : CliffordAlgebra q30)) heq
  rw [cl30ToMat2C_su2ToSpin30Hom, cl30ToMat2C_su2ToSpin30Hom] at h1
  exact h1

private lemma su2ToSpin30Hom_negOne :
    (su2ToSpin30Hom negOneSU2 : CliffordAlgebra q30) = -1 := by
  have hcoe : (negOneSU2 : Mat2C) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [negOneSU2, quatToMat]
  change quatToCl30 ((negOneSU2 : Mat2C) 0 0).re ((negOneSU2 : Mat2C) 0 0).im
    ((negOneSU2 : Mat2C) 0 1).re ((negOneSU2 : Mat2C) 0 1).im = -1
  rw [hcoe]
  simp [quatToCl30]

theorem su2ToSpin30Hom_ker_isometryHom :
    ((spinGroupToIsometryHom q30).comp su2ToSpin30Hom).ker = su2SignSet := by
  ext g
  constructor
  · intro hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hg
    have hcent : ∀ v : Fin 3 → ℝ,
        (su2ToSpin30Hom g : CliffordAlgebra q30) * CliffordAlgebra.ι q30 v =
          CliffordAlgebra.ι q30 v * (su2ToSpin30Hom g : CliffordAlgebra q30) := by
      intro v
      have hiso := congrArg (fun f : q30.IsometryEquiv q30 => f v) hg
      have hι := congrArg (CliffordAlgebra.ι q30) hiso
      rw [spinGroupToIsometryHom, MonoidHom.coe_mk, OneHom.coe_mk, ι_spinGroupIsometryEquiv] at hι
      change (su2ToSpin30Hom g : CliffordAlgebra q30) * CliffordAlgebra.ι q30 v *
          CliffordAlgebra.reverse (su2ToSpin30Hom g : CliffordAlgebra q30) =
        CliffordAlgebra.ι q30 v at hι
      have hrev_star :
          CliffordAlgebra.reverse (su2ToSpin30Hom g : CliffordAlgebra q30) =
            star (su2ToSpin30Hom g : CliffordAlgebra q30) := by
        rw [CliffordAlgebra.star_def,
          CliffordAlgebra.involute_eq_of_mem_even (su2ToSpin30Hom g).prop.2]
      have hrev_mul :
          CliffordAlgebra.reverse (su2ToSpin30Hom g : CliffordAlgebra q30) *
            (su2ToSpin30Hom g : CliffordAlgebra q30) = 1 := by
        rw [hrev_star]
        exact (su2ToSpin30Hom g).prop.1.2.1
      calc
        (su2ToSpin30Hom g : CliffordAlgebra q30) * CliffordAlgebra.ι q30 v
            = ((su2ToSpin30Hom g : CliffordAlgebra q30) * CliffordAlgebra.ι q30 v) * 1 :=
              (mul_one _).symm
        _ = ((su2ToSpin30Hom g : CliffordAlgebra q30) * CliffordAlgebra.ι q30 v) *
              (CliffordAlgebra.reverse (su2ToSpin30Hom g : CliffordAlgebra q30) *
                (su2ToSpin30Hom g : CliffordAlgebra q30)) := by rw [hrev_mul]
        _ = ((su2ToSpin30Hom g : CliffordAlgebra q30) * CliffordAlgebra.ι q30 v *
              CliffordAlgebra.reverse (su2ToSpin30Hom g : CliffordAlgebra q30)) *
              (su2ToSpin30Hom g : CliffordAlgebra q30) := by noncomm_ring
        _ = CliffordAlgebra.ι q30 v * (su2ToSpin30Hom g : CliffordAlgebra q30) := by rw [hι]
    have ⟨he1, _, he3⟩ := cl30ToMat2C_generators
    have hZ := congrArg cl30ToMat2C (hcent e30_0)
    have hX := congrArg cl30ToMat2C (hcent e30_2)
    rw [map_mul, map_mul, cl30ToMat2C_su2ToSpin30Hom,
      show cl30ToMat2C (CliffordAlgebra.ι q30 e30_0) = cl30ToMat2C clE1 from rfl, he1] at hZ
    rw [map_mul, map_mul, cl30ToMat2C_su2ToSpin30Hom,
      show cl30ToMat2C (CliffordAlgebra.ι q30 e30_2) = cl30ToMat2C clE3 from rfl, he3] at hX
    have hgmat := su2_eq_quatToMat g
    set a := (g.1 0 0).re
    set b := (g.1 0 0).im
    set c := (g.1 0 1).re
    set d := (g.1 0 1).im
    have hcZ := congrArg (fun M : Mat2C => M 0 1) hZ
    have hbX := congrArg (fun M : Mat2C => M 0 1) hX
    rw [hgmat.2] at hcZ hbX
    simp only [quatToMat, pauliZ, pauliX, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hcZ hbX
    have hc0 : c = 0 := by
      have hre := congrArg Complex.re hcZ
      simp at hre
      linarith
    have hd0 : d = 0 := by
      have him := congrArg Complex.im hcZ
      simp at him
      linarith
    have hb0 : b = 0 := by
      have him := congrArg Complex.im hbX
      simp at him
      linarith
    have ha_sq : a ^ 2 = 1 := by
      have hn := hgmat.1
      rw [hb0, hc0, hd0] at hn
      linarith
    have ha_cases : a = 1 ∨ a = -1 := sq_eq_one_iff.mp ha_sq
    rcases ha_cases with ha1 | ha1
    · left
      apply Subtype.ext
      rw [hgmat.2, ha1, hb0, hc0, hd0]
      ext i j; fin_cases i <;> fin_cases j <;> simp [quatToMat]
    · right
      apply Subtype.ext
      rw [hgmat.2, ha1, hb0, hc0, hd0]
      ext i j; fin_cases i <;> fin_cases j <;> simp [negOneSU2, quatToMat]
  · intro hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    rcases hg with rfl | rfl
    · simp
    · apply DFunLike.ext
      intro v
      apply clifford_ι_injective q30
      change CliffordAlgebra.ι q30 (spinGroupIsometryEquiv q30 (su2ToSpin30Hom negOneSU2) v) =
        CliffordAlgebra.ι q30 v
      rw [ι_spinGroupIsometryEquiv, su2ToSpin30Hom_negOne]
      simp

/-- **Bridge 4 (`KleinIcosahedralHauptmodulAndGaloisResolvent` ↔ R3 `spinGroup` & Universal 1-Forms)**:
Embeds the binary icosahedral spin group `2I ⊂ SU(2)` injectively into `spinGroup q30`,
identifies its double-cover kernel `{±1} = su2SignSet` onto `SO(3) ⊂ q30.IsometryEquiv q30`,
equips universal noncommutative 1-forms `d_u : Cl(q₃,₀) → Ω¹_univ(Cl(q₃,₀))` with strict
`2I`-equivariance under Hestenes rotor sandwiching, and pairs this with invariance of
Klein's aligned icosahedral forms `(F, H, T)`. -/
theorem binaryIcosahedral_spinGroup_cliffordOneForms_erlangen20 :
    Function.Injective su2ToSpin30Hom ∧
      Nonempty (binaryIcosahedralGroup ≃* binaryIcosahedralGroup.map su2ToSpin30Hom) ∧
      ((spinGroupToIsometryHom q30).comp su2ToSpin30Hom).ker = su2SignSet ∧
      negOneSU2 ∈ binaryIcosahedralGroup ∧
      (∀ (γ : SU2), γ ∈ binaryIcosahedralGroup →
        ∀ a : CliffordAlgebra q30,
          cliffordOneFormsEquiv q30 (spinGroupToIsometryHom q30 (su2ToSpin30Hom γ))
              (differential (CliffordAlgebra q30) a) =
            differential (CliffordAlgebra q30)
              ((su2ToSpin30Hom γ : CliffordAlgebra q30) * a *
                CliffordAlgebra.reverse (su2ToSpin30Hom γ : CliffordAlgebra q30))) ∧
      (∀ (γ : SU2), γ ∈ binaryIcosahedralGroup → ∀ z₁ z₂ : ℂ,
        let w := kleinBinaryAction γ z₁ z₂
        kleinAlignedVertexF w.1 w.2 = kleinAlignedVertexF z₁ z₂ ∧
          kleinAlignedFaceH w.1 w.2 = kleinAlignedFaceH z₁ z₂ ∧
          kleinAlignedEdgeT w.1 w.2 = kleinAlignedEdgeT z₁ z₂) := by
  have hBmem : icosianGenB ∈ binaryIcosahedralGroup :=
    Subgroup.subset_closure (Or.inr rfl)
  have hneg : negOneSU2 ∈ binaryIcosahedralGroup := by
    rw [← icosianGenB_sq]
    exact Subgroup.pow_mem _ hBmem 2
  refine ⟨su2ToSpin30Hom_injective,
    ⟨Subgroup.equivMapOfInjective binaryIcosahedralGroup su2ToSpin30Hom su2ToSpin30Hom_injective⟩,
    su2ToSpin30Hom_ker_isometryHom, hneg, ?_, ?_⟩
  · intro γ _ a
    exact spinGroup_cliffordOneForms_naturality q30 (su2ToSpin30Hom γ) a
  · intro γ hγ z₁ z₂
    exact binaryIcosahedralGroup_invariant_alignedForms hγ z₁ z₂

end Bridge4_BinaryIcosahedralSpin30CliffordOneForms

/-! ## Master Cross-Spine Synthesis (`Six-Pillar Spine II` × `R1–R2–R3 Spine I`) -/

section MasterCrossSpineSynthesis

/-- **Six-Pillar × R1–R2–R3 Master Synthesis**:
Jointly bundles non-commutativity witnesses (`M₂(ℝ)`, `M₂(ℂ)`), contravariant Čech
Maurer–Cartan patching (Bridge 1), elliptic biquaternion Peirce/Krein Walsh polarization
(Bridge 2), `T`-even Gibbs-BKM / Onsager Birkhoff–Hilbert cross-ratio distance with
`T`-odd Casimir lineality obstruction (Bridge 3), and `2I ↪ spinGroup q30` equivariant
universal Clifford 1-forms (Bridge 4). -/
theorem sixPillar_R1R2R3_crossSpine_master_synthesis
    {R A : Type*} [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    (K : InfoGeometry.Algebra.LieActionLane R A) (hK : IsLeibnizAction K)
    (g₁₂ g₂₃ : Aˣ) (Γ : ActionOperatorForm K 1)
    (d m : Fin 3 → ℝ)
    {nH : ℕ} (H A₀ B₀ : FiniteOperatorAlgebra nH)
    (hSlit : tracedExponential H ∈ Complex.slitPlane)
    {Op : Type*} [Ring Op] [Algebra ℝ Op] (S : OnsagerCasimirSystem Op) (opX opY : Op) :
    (∃ M₁ M₂ : Matrix (Fin 2) (Fin 2) ℝ, M₁ * M₂ ≠ M₂ * M₁) ∧
      (∃ C₁ C₂ : Matrix (Fin 2) (Fin 2) ℂ, C₁ * C₂ ≠ C₂ * C₁) ∧
      gaugeTransformL K (g₁₂ * g₂₃) Γ = gaugeTransformL K g₂₃ (gaugeTransformL K g₁₂ Γ) ∧
      actionCurvature K (gaugeTransformL K g₁₂ Γ) =
        actionConjugateForm K g₁₂⁻¹ (actionCurvature K Γ) ∧
      (peirce11 biquatIdempPlus (biquatBivector ℝ d m * biquatBivector ℝ d m) =
          -(((d + m) ⬝ᵥ (d + m)) • biquatIdempPlus) ∧
        (1 / 2 : ℝ) *
            KreinSpace.kreinInner (walshPluckerSplitDoubledEquiv (d, m))
              (walshPluckerSplitDoubledEquiv (d, m)) =
          (directionMomentEquiv.symm (d, m)).kleinQ) ∧
      (casimirSkewMat2.transpose = -casimirSkewMat2 ∧
        secondFDerivLogPartitionReadout H A₀ B₀ = secondFDerivLogPartitionReadout H B₀ A₀ ∧
        S.dissipative opX opY = S.dissipative opY opX ∧
        0 ≤ S.dissipative opX opX ∧
        birkhoffHilbertMetric (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)))
            (symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm)
            (symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm) =
          (1 / 2 : ℝ) * Real.log (scalarCrossRatio 0
            (1 / (upperGauge (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)))
              (symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm)
              (symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm) + 1))
            (upperGauge (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)))
              (symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm)
              (symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm) /
              (upperGauge (onsagerBKMProperCone (EuclideanSpace ℝ (Fin 2)))
                (symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm)
                (symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm) + 1)) 1)) ∧
      (Function.Injective su2ToSpin30Hom ∧
        ((spinGroupToIsometryHom q30).comp su2ToSpin30Hom).ker = su2SignSet) := by
  have hb1 := gaugeTransformL_cocycle K hK g₁₂ g₂₃ Γ
  have hb2 := biquatBivector_peirce_grace_krein_polarization d m
  have ⟨hW1, hW2, hWray⟩ := bkmSample_witness_interior
  have hb3 := gibbsBKM_onsager_birkhoffHilbert_chord_metric H A₀ B₀ hSlit S opX opY
    (symEndOfMat2 bkmSampleMat1 bkmSampleMat1_symm)
    (symEndOfMat2 bkmSampleMat2 bkmSampleMat2_symm)
    hW1 hW2 hWray
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
    (fun _ _ => rfl) hW1 hW2
  have hb4 := binaryIcosahedral_spinGroup_cliffordOneForms_erlangen20
  exact ⟨crossSpine_mat2R_noncomm_exists, crossSpine_mat2C_noncomm_exists,
    hb1.1, hb1.2.2.2.1, ⟨hb2.2.2.1, hb2.2.2.2.2.2.2.2⟩,
    ⟨casimir_skewSymm_violates_cone_salience.1,
      hb3.1.1, hb3.1.2.1, hb3.1.2.2.1, hb3.2.2.2.2.2.2⟩,
    ⟨hb4.1, hb4.2.2.1⟩⟩

end MasterCrossSpineSynthesis

end InfoGeometry.Canonical.SixPillarR1R2R3CrossSpineSynthesis
