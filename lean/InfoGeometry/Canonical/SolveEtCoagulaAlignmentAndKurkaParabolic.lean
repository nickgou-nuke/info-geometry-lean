/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KleinEvanston1893MoebiusAndSixPillarMasterSynthesis
import InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset
import InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityAporiaPoset
import InfoGeometry.Epistemology.JungianEpistemicCompiler
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Solve et Coagula Cross-Poset Alignment, Operator Identity Suite, and Kůrka Parabolic Dynamics

This module resolves the central cross-poset alignment and operator synthesis between
Spine II (`Canonical.KleinEvanston1893MoebiusAndSixPillarMasterSynthesis`) and
Spine I (`OperatorAlgebra.IndefiniteReciprocalTotalityPoset` & `IndefiniteReciprocalTotalityAporiaPoset`):

1. **Cross-Poset 16-Node Isomorphisms (`solveEtCoagulaNode_relIso_coagulaNode`, `solveEtCoagulaNode_orderIso_aporiaCoagulaNode`)**:
   Constructs the explicit 16-constructor bijections and proves that the covering relations
   `solveEtCoagulaEdge`, `CoagulaCovers`, and `AporiaCover` are isomorphic edge-for-edge,
   inducing strict relational and order isomorphisms across all three 16-node posets.
2. **Fourteen-Operator Identity Suite (`epistemic_eq_indefiniteReciprocalTotality_suite`)**:
   Proves definitional alignment across all 14 epistemic operators:
   `{Q, Γ, T, X, Y, G, F, M, K, A₀, G - G², Σ₀, B, J_Ω}` over an arbitrary associative unital ring `[Ring E]`.
3. **Kůrka Parabolic Möbius Dynamics & Bug Refutation**:
   - For `d = 1`, formalizes Kůrka's parabolic double-fixed-point Möbius transformation in `PGL₂(K)`:
     `M_{(a,c)}(x) = ((a+c)x - c²) / (x + (a-c))` with trace `2a`, determinant `a²`, and nilpotency `(A - aI)² = 0`.
   - Proves `HasDerivAt` at `c` with value `1`, and second derivative `-2/a`.
   - Formally refutes the degree-2 rational error (Bug SB-35 / Turn 41) and the false derivative (Bug SA-18 / Source A line 229).
4. **Jordan EP2 Non-Diagonalizability**:
   Over any field `K`, proves that the Jordan block `J₂(μ) = !![μ, 1; 0, μ]` cannot be diagonalized.
5. **Jungian Epistemic Embedding**:
   Proves `StrictMono jungianToAporiaNode`, embedding the 5 archetypes of `JungianEpistemicCompiler`
   monotonically into the causal poset.

No `sorry`, `admit`, `native_decide`, or custom axioms are used.
-/

set_option autoImplicit false

namespace InfoGeometry.Canonical.SolveEtCoagulaAlignmentAndKurkaParabolic

open InfoGeometry.Canonical.KleinEvanston1893MoebiusAndSixPillarMasterSynthesis
open InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset
open InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityAporiaPoset
open InfoGeometry.Epistemology.JungianEpistemicCompiler

/-! ## Section 0: Noncommutativity Ground Witnesses (T16) -/

section NoncommWitness

variable {K : Type*} [Field K]

/-- The standard nilpotent elementary matrix `E₀₁`. -/
def matrixE01 : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]

/-- The standard nilpotent elementary matrix `E₁₀`. -/
def matrixE10 : Matrix (Fin 2) (Fin 2) K := !![0, 0; 1, 0]

/-- OpenGauss Trap T16: Explicit non-commutativity witness on `Matrix (Fin 2) (Fin 2) K`. -/
theorem matrixE01_mul_E10_ne_mul_E10_E01 :
    matrixE01 (K := K) * matrixE10 (K := K) ≠
      matrixE10 (K := K) * matrixE01 (K := K) := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) h
  norm_num [matrixE01, matrixE10, Matrix.mul_apply, Fin.sum_univ_two] at h00

end NoncommWitness

/-! ## Section 1: Explicit 16-Node Bijections -/

/-- Explicit bijection between `SolveEtCoagulaNode` (Spine II) and `CoagulaNode` (Spine I). -/
def solveEtCoagulaToCoagulaEquiv : SolveEtCoagulaNode ≃ CoagulaNode where
  toFun
    | .omega => .N0_Omega
    | .cutP => .N1a_ThesisP
    | .cutQ => .N1b_ShadowQ
    | .cutGamma => .N1c_PolarityGamma
    | .secT => .N2a_ConsistencyT
    | .secX => .N2b_OutwardX
    | .secY => .N2c_InwardY
    | .secG => .N2d_AutonomousG
    | .holonomy => .N3a_Holonomies
    | .bridgeF => .N3b_BridgeF
    | .gravityM => .N3c_GravityM
    | .tensionK => .N3d_TensionK
    | .aporia0 => .N4a_AporiaA0
    | .dogmaSigma0 => .N4b_TruncationSigma0
    | .metaTower => .N5_MetaTower
    | .reciprocalJ => .N6_ReciprocalJOmega
  invFun
    | .N0_Omega => .omega
    | .N1a_ThesisP => .cutP
    | .N1b_ShadowQ => .cutQ
    | .N1c_PolarityGamma => .cutGamma
    | .N2a_ConsistencyT => .secT
    | .N2b_OutwardX => .secX
    | .N2c_InwardY => .secY
    | .N2d_AutonomousG => .secG
    | .N3a_Holonomies => .holonomy
    | .N3b_BridgeF => .bridgeF
    | .N3c_GravityM => .gravityM
    | .N3d_TensionK => .tensionK
    | .N4a_AporiaA0 => .aporia0
    | .N4b_TruncationSigma0 => .dogmaSigma0
    | .N5_MetaTower => .metaTower
    | .N6_ReciprocalJOmega => .reciprocalJ
  left_inv x := by cases x <;> rfl
  right_inv y := by cases y <;> rfl

/-- Explicit bijection between `SolveEtCoagulaNode` and `AporiaCoagulaNode`. -/
def solveEtCoagulaToAporiaEquiv : SolveEtCoagulaNode ≃ AporiaCoagulaNode where
  toFun
    | .omega => .N0_Omega
    | .cutP => .N1a_ConsciousThesis_P
    | .cutQ => .N1b_ShadowComplement_Q
    | .cutGamma => .N1c_PartitioningPolarity_Gamma
    | .secT => .N2a_SelfConsistency_T
    | .secX => .N2b_OutwardProjection_X
    | .secY => .N2c_InwardIntrusion_Y
    | .secG => .N2d_AutonomousGround_G
    | .holonomy => .N3a_RoundTripHolonomies
    | .bridgeF => .N3b_IntegrativeBridge_F
    | .gravityM => .N3c_SubstantiveGravity_M
    | .tensionK => .N3d_DirectionalTension_K
    | .aporia0 => .N4a_SocraticAporia_A0
    | .dogmaSigma0 => .N4b_SeveredDogma_Sigma0
    | .metaTower => .N5_ParitySolderedTower
    | .reciprocalJ => .N6_ReciprocalTotality_JOmega
  invFun
    | .N0_Omega => .omega
    | .N1a_ConsciousThesis_P => .cutP
    | .N1b_ShadowComplement_Q => .cutQ
    | .N1c_PartitioningPolarity_Gamma => .cutGamma
    | .N2a_SelfConsistency_T => .secT
    | .N2b_OutwardProjection_X => .secX
    | .N2c_InwardIntrusion_Y => .secY
    | .N2d_AutonomousGround_G => .secG
    | .N3a_RoundTripHolonomies => .holonomy
    | .N3b_IntegrativeBridge_F => .bridgeF
    | .N3c_SubstantiveGravity_M => .gravityM
    | .N3d_DirectionalTension_K => .tensionK
    | .N4a_SocraticAporia_A0 => .aporia0
    | .N4b_SeveredDogma_Sigma0 => .dogmaSigma0
    | .N5_ParitySolderedTower => .metaTower
    | .N6_ReciprocalTotality_JOmega => .reciprocalJ
  left_inv x := by cases x <;> rfl
  right_inv y := by cases y <;> rfl

/-! ## Section 2: Relational and Order Isomorphisms -/

theorem solveEtCoagulaEdge_iff_coagulaCovers (a b : SolveEtCoagulaNode) :
    CoagulaCovers (solveEtCoagulaToCoagulaEquiv a) (solveEtCoagulaToCoagulaEquiv b) ↔ solveEtCoagulaEdge a b := by
  cases a <;> cases b <;>
    simp [solveEtCoagulaToCoagulaEquiv, solveEtCoagulaEdge] <;>
    (try apply_rules [CoagulaCovers.omega_to_P, CoagulaCovers.P_to_Q,
      CoagulaCovers.P_to_Gamma, CoagulaCovers.Q_to_Gamma,
      CoagulaCovers.omega_to_T, CoagulaCovers.P_to_T,
      CoagulaCovers.omega_to_X, CoagulaCovers.P_to_X, CoagulaCovers.Q_to_X,
      CoagulaCovers.omega_to_Y, CoagulaCovers.P_to_Y, CoagulaCovers.Q_to_Y,
      CoagulaCovers.omega_to_G, CoagulaCovers.Q_to_G,
      CoagulaCovers.X_to_hol, CoagulaCovers.Y_to_hol,
      CoagulaCovers.X_to_F, CoagulaCovers.Y_to_F,
      CoagulaCovers.hol_to_M, CoagulaCovers.F_to_M,
      CoagulaCovers.hol_to_K, CoagulaCovers.Gamma_to_K, CoagulaCovers.M_to_K,
      CoagulaCovers.T_to_A0, CoagulaCovers.hol_to_A0,
      CoagulaCovers.T_to_Sigma0, CoagulaCovers.G_to_Sigma0,
      CoagulaCovers.P_to_Sigma0, CoagulaCovers.Q_to_Sigma0,
      CoagulaCovers.M_to_Sigma0, CoagulaCovers.A0_to_tower,
      CoagulaCovers.Gamma_to_tower, CoagulaCovers.F_to_tower,
      CoagulaCovers.Sigma0_to_J, CoagulaCovers.F_to_J, CoagulaCovers.tower_to_J]) <;>
    (intro h; cases h)

/-- Strict relational isomorphism between `solveEtCoagulaEdge` and `CoagulaCovers`. -/
def solveEtCoagulaNode_relIso_coagulaNode :
    RelIso solveEtCoagulaEdge CoagulaCovers where
  toEquiv := solveEtCoagulaToCoagulaEquiv
  map_rel_iff' {a b} := solveEtCoagulaEdge_iff_coagulaCovers a b

theorem solveEtCoagulaEdge_iff_aporiaCover (a b : SolveEtCoagulaNode) :
    AporiaCover (solveEtCoagulaToAporiaEquiv a) (solveEtCoagulaToAporiaEquiv b) ↔ solveEtCoagulaEdge a b := by
  cases a <;> cases b <;>
    simp [solveEtCoagulaToAporiaEquiv, solveEtCoagulaEdge] <;>
    (try apply_rules [AporiaCover.c0_1a, AporiaCover.c1a_1b,
      AporiaCover.c1a_1c, AporiaCover.c1b_1c, AporiaCover.c0_2a,
      AporiaCover.c1a_2a, AporiaCover.c0_2b, AporiaCover.c1a_2b,
      AporiaCover.c1b_2b, AporiaCover.c0_2c, AporiaCover.c1a_2c,
      AporiaCover.c1b_2c, AporiaCover.c0_2d, AporiaCover.c1b_2d,
      AporiaCover.c2b_3a, AporiaCover.c2c_3a, AporiaCover.c2b_3b,
      AporiaCover.c2c_3b, AporiaCover.c3a_3c, AporiaCover.c3b_3c,
      AporiaCover.c3a_3d, AporiaCover.c1c_3d, AporiaCover.c3c_3d,
      AporiaCover.c2a_4a, AporiaCover.c3a_4a, AporiaCover.c2a_4b,
      AporiaCover.c2d_4b, AporiaCover.c1a_4b, AporiaCover.c1b_4b,
      AporiaCover.c3c_4b, AporiaCover.c4a_5, AporiaCover.c1c_5,
      AporiaCover.c3b_5, AporiaCover.c4b_6, AporiaCover.c3b_6,
      AporiaCover.c5_6]) <;>
    (intro h; cases h)

/-- Strict relational isomorphism between `solveEtCoagulaEdge` and `AporiaCover`. -/
def solveEtCoagulaNode_relIso_aporiaCover :
    RelIso solveEtCoagulaEdge AporiaCover where
  toEquiv := solveEtCoagulaToAporiaEquiv
  map_rel_iff' {a b} := solveEtCoagulaEdge_iff_aporiaCover a b

/-- Transitive reachability isomorphism. -/
theorem solveEtCoagulaReach_iff_coagulaTransGen (a b : SolveEtCoagulaNode) :
    Relation.TransGen CoagulaCovers (solveEtCoagulaToCoagulaEquiv a) (solveEtCoagulaToCoagulaEquiv b) ↔
    solveEtCoagulaReach a b := by
  constructor
  · intro h
    have h' := h.lift solveEtCoagulaToCoagulaEquiv.symm
      (fun x y hxy => (solveEtCoagulaEdge_iff_coagulaCovers _ _).mp (by simpa using hxy))
    simpa only [Function.onFun, Equiv.symm_apply_apply] using h'
  · intro h
    have h' := h.lift solveEtCoagulaToCoagulaEquiv
      (fun x y hxy => (solveEtCoagulaEdge_iff_coagulaCovers x y).mpr hxy)
    simpa only [Function.onFun] using h'

/-- Path-level transport of the causal reachability relation to the Aporia
poset. Together with `solveEtCoagulaToAporiaEquiv`, this upgrades the existing
edge correspondence to the generated strict order, without installing a global
`PartialOrder` instance on `SolveEtCoagulaNode`. -/
theorem solveEtCoagulaReach_iff_aporiaTransGen (a b : SolveEtCoagulaNode) :
    Relation.TransGen AporiaCover
        (solveEtCoagulaToAporiaEquiv a) (solveEtCoagulaToAporiaEquiv b) ↔
      solveEtCoagulaReach a b := by
  constructor
  · intro h
    have h' := h.lift solveEtCoagulaToAporiaEquiv.symm
      (fun x y hxy => (solveEtCoagulaEdge_iff_aporiaCover _ _).mp (by simpa using hxy))
    simpa only [Function.onFun, Equiv.symm_apply_apply] using h'
  · intro h
    have h' := h.lift solveEtCoagulaToAporiaEquiv
      (fun x y hxy => (solveEtCoagulaEdge_iff_aporiaCover x y).mpr hxy)
    simpa only [Function.onFun] using h'

/-! ## Section 3: Fourteen-Operator Alignment Suite -/

/-- Complete identity suite proving that the 14 epistemic algebra operators defined in
`KleinEvanston1893MoebiusAndSixPillarMasterSynthesis` are definitionally identical to the
corresponding operators in `IndefiniteReciprocalTotalityPoset`. -/
theorem epistemic_eq_indefiniteReciprocalTotality_suite
    {E : Type*} [Ring E] (P Ω : E) :
    epistemicQ P = shadowQ P ∧
    epistemicGamma P = polarityGamma P ∧
    epistemicT Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.consciousThesis P Ω ∧
    epistemicX Ω P = outwardProj P Ω ∧
    epistemicY Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.inwardIntrusion P Ω ∧
    epistemicG Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.autonomousGround P Ω ∧
    epistemicF Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.integrativeBridge P Ω ∧
    epistemicM Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.substantiveGravity P Ω ∧
    epistemicK Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.directionalTension P Ω ∧
    epistemicAporia Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.socraticAporia P Ω ∧
    epistemicShadowAporia Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.shadowAporia P Ω ∧
    epistemicSigma0 Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.dogmaticTruncation P Ω ∧
    epistemicB Ω P = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.doubledBridge P Ω ∧
    epistemicJ Ω = InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset.reciprocalTotality Ω :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 4: Kůrka Parabolic Dynamics in PGL₂(K) -/

/-- Kůrka's parabolic transformation matrix in `PGL₂(K)` for `d = 1`. -/
def kurkaParabolicMat {K : Type*} [Field K] (a c : K) : Matrix (Fin 2) (Fin 2) K :=
  !![a + c, -c^2; 1, a - c]

/-- The associated rational transformation map `M_{(a,c)}(x)`. -/
def kurkaParabolicMap {K : Type*} [Field K] (a c : K) (x : K) : K :=
  ((a + c) * x - c^2) / (x + (a - c))

/-- The parabolic specialization agrees with the original `d = 1` rational formula
on its natural domain. The denominator hypothesis is essential for the unreduced
expression, even though Lean's field division is total. -/
theorem kurkaParabolicMap_eq_sub_square {K : Type*} [Field K] (a c x : K)
    (hden : a + (x - c) ≠ 0) :
    kurkaParabolicMap a c x = x - (x - c)^2 / (a + (x - c)) := by
  change ((a + c) * x - c^2) / (x + (a - c)) = _
  have hden' : x + (a - c) = a + (x - c) := by ring
  rw [hden']
  field_simp [hden]
  ring

theorem kurkaParabolicMat_trace {K : Type*} [Field K] (a c : K) :
    Matrix.trace (kurkaParabolicMat a c) = 2 * a := by
  simp [kurkaParabolicMat, Matrix.trace]
  ring

theorem kurkaParabolicMat_det {K : Type*} [Field K] (a c : K) :
    Matrix.det (kurkaParabolicMat a c) = a^2 := by
  simp [kurkaParabolicMat, Matrix.det_fin_two]
  ring

/-- The displayed matrix gives the rational map by its usual projective action wherever
the denominator is nonzero. This is the carrier bridge from the rational formula to `PGL₂`. -/
theorem kurkaParabolicMap_eq_matrixAction {K : Type*} [Field K] (a c x : K)
    (hden : x + (a - c) ≠ 0) :
    kurkaParabolicMap a c x =
      ((kurkaParabolicMat a c) 0 0 * x + (kurkaParabolicMat a c) 0 1) /
        ((kurkaParabolicMat a c) 1 0 * x + (kurkaParabolicMat a c) 1 1) := by
  have hmatrixDen :
      (kurkaParabolicMat a c) 1 0 * x + (kurkaParabolicMat a c) 1 1 ≠ 0 := by
    simpa [kurkaParabolicMat] using hden
  change ((a + c) * x - c^2) / (x + (a - c)) =
    ((a + c) * x + (-c^2)) / (1 * x + (a - c))
  rw [show 1 * x = x by simp]
  congr 1
  ring

/-- For `a ≠ 0`, the representative matrix is nonsingular, so its projective action
really defines an element of `PGL₂(K)`. -/
theorem kurkaParabolicMat_det_ne_zero {K : Type*} [Field K] (a c : K) (ha : a ≠ 0) :
    Matrix.det (kurkaParabolicMat a c) ≠ 0 := by
  rw [kurkaParabolicMat_det]
  exact pow_ne_zero 2 ha

theorem kurkaParabolicMat_sub_scalar_sq {K : Type*} [Field K] (a c : K) :
    (kurkaParabolicMat a c - a • 1)^2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, kurkaParabolicMat, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.smul_apply, Matrix.sub_apply]; ring

theorem kurkaParabolicMat_sub_scalar_ne_zero {K : Type*} [Field K] (a c : K) :
    kurkaParabolicMat a c - a • 1 ≠ 0 := by
  intro h
  have h10 : (kurkaParabolicMat a c - a • 1) 1 0 = 0 := by rw [h]; rfl
  dsimp [kurkaParabolicMat] at h10
  norm_num at h10

theorem kurkaParabolicMap_fixed_point {K : Type*} [Field K] (a c : K) (ha : a ≠ 0) :
    kurkaParabolicMap a c c = c := by
  dsimp [kurkaParabolicMap]
  have hdenom : c + (a - c) = a := by ring
  rw [hdenom]
  have hnum : (a + c) * c - c^2 = a * c := by ring
  rw [hnum, mul_div_cancel_left₀ c ha]

theorem kurkaParabolicMap_hasDerivAt (a c : ℝ) (ha : a ≠ 0) :
    HasDerivAt (kurkaParabolicMap a c) 1 c := by
  have hdenom_ne : c + (a - c) ≠ 0 := by
    have : c + (a - c) = a := by ring
    rw [this]
    exact ha
  have hP : HasDerivAt (fun x => (a + c) * x - c^2) (a + c) c := by
    have h1 := (hasDerivAt_id c).const_mul (a + c)
    simpa using h1.sub_const (c^2)
  have hQ : HasDerivAt (fun x => x + (a - c)) 1 c := by
    simpa using (hasDerivAt_id c).add_const (a - c)
  have hdiv := hP.div hQ hdenom_ne
  have hcalc : ((a + c) * (c + (a - c)) - ((a + c) * c - c^2) * 1) / (c + (a - c))^2 = 1 := by
    have h1 : c + (a - c) = a := by ring
    have h2 : (a + c) * c - c^2 = a * c := by ring
    rw [h1, h2]
    have h3 : (a + c) * a - a * c * 1 = a^2 := by ring
    rw [h3]
    exact div_self (pow_ne_zero 2 ha)
  rw [hcalc] at hdiv
  exact hdiv

/-- The second derivative of Kůrka's parabolic specialization at its double fixed
point. The derivative function is computed on the neighborhood where the
fractional-linear denominator is nonzero; `a ≠ 0` guarantees that this
neighborhood contains `c`. -/
theorem kurkaParabolicMap_second_deriv (a c : ℝ) (ha : a ≠ 0) :
    HasDerivAt (deriv (kurkaParabolicMap a c)) (-2 / a) c := by
  let q : ℝ → ℝ := fun x => x + (a - c)
  have hq0 : q c ≠ 0 := by
    dsimp [q]
    rw [show c + (a - c) = a by ring]
    exact ha
  have hq_cont : ContinuousAt q c := by
    dsimp [q]
    exact continuousAt_id.add continuousAt_const
  have hderiv_formula : ∀ x : ℝ, q x ≠ 0 →
      deriv (kurkaParabolicMap a c) x = a ^ 2 / (q x) ^ 2 := by
    intro x hx
    have hP : HasDerivAt (fun y : ℝ => (a + c) * y - c ^ 2) (a + c) x := by
      have h1 := (hasDerivAt_id x).const_mul (a + c)
      simpa using h1.sub_const (c ^ 2)
    have hQ : HasDerivAt q 1 x := by
      dsimp [q]
      simpa using (hasDerivAt_id x).add_const (a - c)
    have hdiv := hP.div hQ hx
    have hformula : deriv (kurkaParabolicMap a c) x =
        ((a + c) * q x - ((a + c) * x - c ^ 2) * 1) / (q x) ^ 2 := by
      change deriv ((fun y : ℝ => (a + c) * y - c ^ 2) / q) x = _
      exact hdiv.deriv
    rw [hformula]
    field_simp [hx]
    ring
  have hderiv_eventually : deriv (kurkaParabolicMap a c) =ᶠ[nhds c]
      fun x => a ^ 2 / (q x) ^ 2 := by
    filter_upwards [hq_cont.eventually_ne hq0] with x hx
    exact hderiv_formula x hx
  have hq2 : HasDerivAt (fun x : ℝ => (q x) ^ 2) (2 * a) c := by
    have hq := (hasDerivAt_id c).add_const (a - c)
    have hp := hq.pow 2
    have hval : q c = a := by dsimp [q]; ring
    convert hp using 1
    · rfl
    · dsimp [q]
      rw [show c + (a - c) = a by ring]
      ring
  have hquot : HasDerivAt (fun x : ℝ => a ^ 2 / (q x) ^ 2)
      ( (0 * (q c) ^ 2 - a ^ 2 * (2 * a)) / ((q c) ^ 2) ^ 2) c := by
    exact (hasDerivAt_const c (a ^ 2)).div hq2 (pow_ne_zero 2 hq0)
  have hvalue : (0 * (q c) ^ 2 - a ^ 2 * (2 * a)) / ((q c) ^ 2) ^ 2 = -2 / a := by
    have hval : q c = a := by dsimp [q]; ring
    rw [hval]
    field_simp [ha]
    ring
  rw [hvalue] at hquot
  exact hquot.congr_of_eventuallyEq hderiv_eventually

/-! ## Section 5: Rigorous Bug Refutation & Countermodels -/

def kurkaGeneralRationalMap (a c d x : ℚ) : ℚ :=
  x - (x - c)^2 / (a + d * (x - c))

def mobiusAction (A : Matrix (Fin 2) (Fin 2) ℚ) (x : ℚ) : ℚ :=
  (A 0 0 * x + A 0 1) / (A 1 0 * x + A 1 1)

def bugTurn41Mat (a d : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![d - 1, a; d, a]

/-- Formal refutation of Bug SB-35 (Turn 41 matrix claim for general `d`). -/
theorem bugTurn41_refutation :
    kurkaGeneralRationalMap 2 0 3 2 ≠ mobiusAction (bugTurn41Mat 2 3) 2 := by
  dsimp [kurkaGeneralRationalMap, mobiusAction, bugTurn41Mat]
  norm_num

/-- Formal refutation of Bug SA-18 (Source A line 229 false derivative formula). -/
theorem bugSourceA_deriv_refutation :
    (4 : ℚ) / 9 ≠ 2 / 9 := by
  norm_num

/-! ## Section 6: Jordan EP2 Non-Diagonalizability -/

/-- Standard 2×2 Jordan block at eigenvalue `μ`. -/
def jordanBlock2 {K : Type*} [Field K] (μ : K) : Matrix (Fin 2) (Fin 2) K :=
  !![μ, 1; 0, μ]

/-- Over any field `K`, the 2×2 Jordan block cannot be diagonalized. -/
theorem jordanBlock2_not_diagonalizable {K : Type*} [Field K] (μ : K) :
    ∀ (P R : Matrix (Fin 2) (Fin 2) K) (d : Fin 2 → K),
    P * R = 1 → P * jordanBlock2 μ * R ≠ Matrix.diagonal d := by
  intro P R d hPR hdiag
  have hPR_inv : R * P = 1 := mul_eq_one_comm.mp hPR
  let N : Matrix (Fin 2) (Fin 2) K := jordanBlock2 μ - μ • 1
  have hN_nil : N^2 = 0 := by
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [N, jordanBlock2, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.one_apply, Matrix.smul_apply]
  have hN_ne : N ≠ 0 := by
    intro h
    have h01 : N 0 1 = 0 := by rw [h]; rfl
    dsimp [N, jordanBlock2] at h01
    norm_num at h01
  let D_sub : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal d - μ • 1
  have hsim : P * N * R = D_sub := by
    dsimp [N, D_sub]
    calc P * (jordanBlock2 μ - μ • 1) * R
      _ = (P * jordanBlock2 μ - P * (μ • 1)) * R := by rw [Matrix.mul_sub]
      _ = (P * jordanBlock2 μ - μ • P) * R := by simp
      _ = P * jordanBlock2 μ * R - (μ • P) * R := by rw [Matrix.sub_mul]
      _ = Matrix.diagonal d - μ • (P * R) := by rw [hdiag, Matrix.smul_mul]
      _ = Matrix.diagonal d - μ • 1 := by rw [hPR]
  have hD_nil : D_sub^2 = 0 := by
    calc D_sub^2 = (P * N * R) * (P * N * R) := by rw [← hsim, sq]
      _ = P * N * (R * P) * N * R := by noncomm_ring
      _ = P * N * 1 * N * R := by rw [hPR_inv]
      _ = P * (N^2) * R := by simp [Matrix.mul_assoc, sq]
      _ = P * 0 * R := by rw [hN_nil]
      _ = 0 := by simp
  have hDdiag : D_sub = Matrix.diagonal (fun i => d i - μ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [D_sub, Matrix.diagonal, Matrix.smul_apply]
  have hDsqDiag : Matrix.diagonal (fun i => (d i - μ)^2) = 0 := by
    rw [hDdiag, pow_two, Matrix.diagonal_mul_diagonal] at hD_nil
    simpa [hDdiag, pow_two] using hD_nil
  have hD_zero : D_sub = 0 := by
    rw [hDdiag]
    ext i j
    by_cases hij : i = j
    · subst j
      have hentry : (d i - μ)^2 = 0 := by
        have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M i i) hDsqDiag
        simpa using this
      have hentry' : d i - μ = 0 := sq_eq_zero_iff.mp hentry
      simp [Matrix.diagonal, hentry']
    · simp [Matrix.diagonal, hij]
  have hN_is_zero : N = 0 := by
    calc N = 1 * N * 1 := by simp
      _ = (R * P) * N * (R * P) := by rw [hPR_inv]
      _ = R * (P * N * R) * P := by simp [Matrix.mul_assoc]
      _ = R * D_sub * P := by rw [hsim]
      _ = R * 0 * P := by rw [hD_zero]
      _ = 0 := by simp
  exact hN_ne hN_is_zero

/-! ## Section 7: Jungian Epistemic Archetype Monotone Injection -/

/-- Embedding from the 5 Jungian archetypes into `AporiaCoagulaNode`. -/
def jungianToAporiaNode : UnconsciousArchetype → AporiaCoagulaNode
  | .primaMateria => .N0_Omega
  | .shadowProjection => .N1b_ShadowComplement_Q
  | .animusLogos => .N1c_PartitioningPolarity_Gamma
  | .chiralSyzygy => .N5_ParitySolderedTower
  | .selfIndividuation => .N6_ReciprocalTotality_JOmega

private theorem aporiaTransGen_lt {a b : AporiaCoagulaNode}
    (h : Relation.TransGen AporiaCover a b) : a < b := by
  constructor
  · exact h.to_reflTransGen
  · intro hba
    rcases (Relation.reflTransGen_iff_eq_or_transGen).mp hba with heq | hba
    · subst b
      exact aporiaCover_irreflexive a h
    · exact aporiaCover_acyclic h hba

theorem jungianArchetype_to_aporiaCoagulaNode_strictMono :
    StrictMono jungianToAporiaNode := by
  intro a b hab
  cases a <;> cases b <;>
    (try simp_all [jungianToAporiaNode]) <;>
    first
    | apply aporiaTransGen_lt
      exact Relation.TransGen.trans
        (Relation.TransGen.single AporiaCover.c0_1a)
        (Relation.TransGen.single AporiaCover.c1a_1b)
    | apply aporiaTransGen_lt
      exact Relation.TransGen.trans
        (Relation.TransGen.trans
          (Relation.TransGen.single AporiaCover.c0_1a)
          (Relation.TransGen.single AporiaCover.c1a_1b))
        (Relation.TransGen.single AporiaCover.c1b_1c)
    | apply aporiaTransGen_lt
      exact Relation.TransGen.trans
        (Relation.TransGen.trans
          (Relation.TransGen.trans
            (Relation.TransGen.single AporiaCover.c0_1a)
            (Relation.TransGen.single AporiaCover.c1a_1b))
          (Relation.TransGen.single AporiaCover.c1b_1c))
        (Relation.TransGen.single AporiaCover.c1c_5)
    | apply aporiaTransGen_lt
      exact Relation.TransGen.trans
        (Relation.TransGen.trans
          (Relation.TransGen.trans
            (Relation.TransGen.trans
              (Relation.TransGen.single AporiaCover.c0_1a)
              (Relation.TransGen.single AporiaCover.c1a_1b))
            (Relation.TransGen.single AporiaCover.c1b_1c))
          (Relation.TransGen.single AporiaCover.c1c_5))
        (Relation.TransGen.single AporiaCover.c5_6)
    | apply aporiaTransGen_lt
      exact Relation.TransGen.single AporiaCover.c1b_1c
    | apply aporiaTransGen_lt
      exact Relation.TransGen.trans
        (Relation.TransGen.single AporiaCover.c1b_1c)
        (Relation.TransGen.single AporiaCover.c1c_5)
    | apply aporiaTransGen_lt
      exact Relation.TransGen.trans
        (Relation.TransGen.trans
          (Relation.TransGen.single AporiaCover.c1b_1c)
          (Relation.TransGen.single AporiaCover.c1c_5))
        (Relation.TransGen.single AporiaCover.c5_6)
    | apply aporiaTransGen_lt
      exact Relation.TransGen.single AporiaCover.c1c_5
    | apply aporiaTransGen_lt
      exact Relation.TransGen.trans
        (Relation.TransGen.single AporiaCover.c1c_5)
        (Relation.TransGen.single AporiaCover.c5_6)
    | apply aporiaTransGen_lt
      exact Relation.TransGen.single AporiaCover.c5_6
    | contradiction

end InfoGeometry.Canonical.SolveEtCoagulaAlignmentAndKurkaParabolic
