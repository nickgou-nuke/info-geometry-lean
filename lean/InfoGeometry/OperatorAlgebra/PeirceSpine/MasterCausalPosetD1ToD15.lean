/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys
import InfoGeometry.OperatorAlgebra.PeirceSpine.DefectTower
import InfoGeometry.OperatorAlgebra.PeirceSpine.Homogenized
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.PhaseConjugateSteinberg
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.Orientation
import InfoGeometry.OperatorAlgebra.PeirceSpine.TransferDefect
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors
import InfoGeometry.OperatorAlgebra.PeirceSpine.EndomorphismCharge
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConeSheetBraiding
import InfoGeometry.OperatorAlgebra.PeirceSpine.BoundaryDependence
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdealChartPairing
import InfoGeometry.OperatorAlgebra.PeirceSpine.DirectedFlowMagneticResolvent
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset

/-!
# 15-Stage Master Causal Poset of Non-Commutative Operator Archetypes (`D₁ → D₁₅`)

This file proves the 15-stage algebraic synthesis of non-commutative
associative and star-ring operator archetypes in native Mathlib. It also indexes
stages `D₁`–`D₁₆` by rank and records a separate directed acyclic edge relation;
those edges are not claimed to generate a partial order or to be cover relations:

* `D₁`: Dual Lie–Jordan Leibniz identity and dyadic defect factorization
  (`dualDefect X * idempotencyDefect X = idempotencyDefect (X * X)`).
* `D₂`: Peirce–Cartan `ℤ₂`-grading, `S² = 1`, `ad_P³ = ad_P`, and odd-product
  even closure `[P, [P, A][P, C]] = 0`.
* `D₃`: Nilpotent Peirce cones `N₊² = N₋² = 0` and the `Cl₁,₁` tetraktys
  `(Φ, J, V, Σ)` with `Φ² = V`, `J² = -V`, `J Φ = -Φ J = Σ = S V`.
* `D₄`: Cross/same-cone sandwich complementarity and double-derivation trinity
  `derivSqPhi ± derivSqJ`.
* `D₅`: Off-shell homogenized `ℤ₂ × ℤ₂` projectors (`hProjV`, `hProjPhi`,
  `hProjJ`, `hProjSig`) with operator-valued weight `8 V²`.
* `D₆`: Operator-valued `S₃` cyclotomic braiding and reflection channels
  (`cubeRootOp`, `cubeRootOpConj`, `s3Refl0`, `s3Refl1`, `s3Refl2`).
* `D₇`: Unipotent conjugation group and palindromic Steinberg braiding
  (`steinbergBraid`, `steinbergBraidDual`, `parityConj_steinbergBraid`).
* `D₈`: Bergman operator `B(1) = 1 - (P_A - P_C)² = 1 - V` and operator
  cross-ratio on the projective line.
* `D₉`: Graded Hodge star `⋆ X = S X` and codifferential conjugacy
  `d̄ = -⋆ d ⋆`.
* `D₁₀`: Chiral Euler factorizations (`(1 - N₊)(1 - N₋) = 1 - Φ + Q₊`) and
  cyclotomic polynomial evaluations (`Φ₆(P + J) = 1 - V`).
* `D₁₁`: 5-graded Kantor / endomorphism charge polynomial annihilator
  `Δ_P⁵ - 5 Δ_P³ + 4 Δ_P = 0` on `Module.End ℤ B`.
* `D₁₂`: `ℕ × ℕ` iterated defect tower splitting and chiral braiding
  (`genV_defect_iterates_cycle_split`, `qgt_defect_iterates_orthogonal`).
* `D₁₃`: Boundary-only dependence of `Φ, J, V, Σ` under arbitrary even-grade
  shifts `A ↦ A + E_P(X)`.
* `D₁₄`: Grading-twisted star anti-involution and principal-ideal chart pairing
  (`grading_star_involutive`, `twisted_ideal_pairing`).
* `D₁₅`: Directed adjacency symmetric/skew-adjoint decomposition (`symAdj`,
  `skewAdj`), grading-twisted self-adjoint Laplacian (`gradingTwistedAdj`,
  `gradingTwistedLaplacian`), ranked 3-layer DAG path resolvent
  (`twoStepResolvent`, `RankedDAGResolvent.finiteGreen`), and block-lower
  triangular subalgebra closure with orthogonal idempotent compression.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

/-!
### 1. The 18-Stage Causal DAG (`D₁ → D₁₈`)

The rank and edge relation index all 18 stages. The master algebraic synthesis
theorem below covers `D₁`–`D₁₅`; `D₁₆`–`D₁₈` (`S₁ → S₁₅`) have their complete
sheaf-inspired operator synthesis theorems in `CellularSheafOperatorPoset.lean`.
-/

/-- Archetype stage labels `D₁` through `D₁₈`, ordered separately by their rank. -/
inductive ArchetypeStage : Type
  | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8
  | D9 | D10 | D11 | D12 | D13 | D14 | D15 | D16 | D17 | D18
  deriving DecidableEq, Repr

namespace ArchetypeStage

/-- Integer topological rank (1 through 18) of each archetype stage. -/
def rank : ArchetypeStage → ℕ
  | D1 => 1
  | D2 => 2
  | D3 => 3
  | D4 => 4
  | D5 => 5
  | D6 => 6
  | D7 => 7
  | D8 => 8
  | D9 => 9
  | D10 => 10
  | D11 => 11
  | D12 => 12
  | D13 => 13
  | D14 => 14
  | D15 => 15
  | D16 => 16
  | D17 => 17
  | D18 => 18

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder ArchetypeStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed edges of the 18-stage causal DAG (`D₁ → D₁₈`). -/
def causalEdge : ArchetypeStage → ArchetypeStage → Prop
  | D1, D2 => True
  | D1, D3 => True
  | D2, D4 => True
  | D3, D4 => True
  | D3, D5 => True
  | D4, D6 => True
  | D5, D6 => True
  | D5, D7 => True
  | D6, D8 => True
  | D7, D8 => True
  | D7, D9 => True
  | D8, D10 => True
  | D9, D10 => True
  | D9, D11 => True
  | D10, D12 => True
  | D11, D12 => True
  | D11, D13 => True
  | D12, D14 => True
  | D13, D14 => True
  | D13, D15 => True
  | D14, D15 => True
  | D14, D16 => True
  | D15, D16 => True
  | D16, D17 => True
  | D16, D18 => True
  | D17, D18 => True
  | _, _ => False

/-- Every direct edge in the 16-stage causal DAG strictly increases topological rank. -/
theorem causalEdge_strict_rank_mono {s t : ArchetypeStage} (h : causalEdge s t) :
    rank s < rank t := by
  cases s <;> cases t <;> simp_all [causalEdge, rank]

/-- The 16-stage causal DAG has no self-loops. -/
theorem causalEdge_irrefl (s : ArchetypeStage) : ¬ causalEdge s s := by
  intro h
  exact Nat.lt_irrefl (rank s) (causalEdge_strict_rank_mono h)

end ArchetypeStage

/-! ### 2. Master 15-Stage Non-Commutative Synthesis Theorem (`D₁ → D₁₅`) -/

/-- **15-Stage Master Causal Poset Synthesis (`D₁ → D₁₅`)**:
In any associative star-ring `B` equipped with a self-adjoint idempotent `P`,
an orthogonal idempotent `Q`, and a mutually orthogonal 3-layer idempotent pair
`(P₁, P₂)`, all 15 non-commutative operator-algebraic stages hold simultaneously:
1. `D₁`: Dual Lie–Jordan Leibniz law `[H, U V] = {H, U} V - U {H, V}` and dyadic
   defect tower `dualDefect X * idempotencyDefect X = idempotencyDefect (X * X)`;
2. `D₂`: Grading involution `S² = 1`, tripotent derivation `ad_P³ = ad_P`, and
   odd-product closure `[P, [P, A][P, C]] = 0`;
3. `D₃`: Nilpotent cones `N₊² = N₋² = 0` and `Cl₁,₁` relations `Φ² = V`, `J² = -V`,
   `J Φ = Σ = S V`;
4. `D₄`: Sandwich complementarity `sandwichCross + sandwichSame = Φ X Φ` and
   focusing split `derivSqPhi - derivSqJ = 4 • sandwichSame`;
5. `D₅`: Off-shell homogenized `ℤ₂ × ℤ₂` projector partition of `8 V² X`;
6. `D₆`: Operator `S₃` cyclotomic braiding `Φ ω_J = ω̄_J Φ` and `1 + ω_J + ω̄_J = 0`;
7. `D₇`: Palindromic Steinberg braiding `B₊ B₊⁻¹ = 1`, `B₊ - B₋ = (1 - V) Φ`, and
   `S B₊ S = B₊⁻¹`;
8. `D₈`: Bergman operator identity `B(1) = 1 - (P_A - P_C)² = 1 - V`;
9. `D₉`: Graded Hodge star and codifferential conjugacy `d̄ = -⋆ d ⋆`;
10. `D₁₀`: Chiral Euler factorization `(1 - N₊)(1 - N₋) = 1 - Φ + Q₊` and
    `Φ₆(P + J) = 1 - V`;
11. `D₁₁`: 5-graded endomorphism charge annihilator `Δ_P⁵ - 5 Δ_P³ + 4 Δ_P = 0`;
12. `D₁₂`: Iterated defect tower cycle split `δ^[n](V) = δ^[n](Q₊) + δ^[n](Q₋)`
    and corner orthogonality `δ^[n](Q₊) δ^[n](Q₋) = 0`;
13. `D₁₃`: Invariance of `(N₊, N₋, Φ, J, V, Σ)` under even-grade shifts `A + E_P(X)`;
14. `D₁₄`: Involutive grading-twisted star `S (S X⋆ S)⋆ S = X` and twisted ideal pairing;
15. `D₁₅`: Directed adjacency symmetric/skew-adjoint decomposition, grading-twisted
    self-adjoint Laplacian, ranked 3-layer DAG path resolvent, and block-lower
    triangular subalgebra closure with orthogonal idempotent compression. -/
theorem master_causal_poset_D1_to_D15
    {B : Type*} [Ring B] [StarRing B]
    {P Q P₁ P₂ : B} (hP : P * P = P) (hPs : star P = P)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (H U V X Y W A C Deg F₁ L₁ D₁ F₂ L₂ D₂ : B)
    (K : Module.End ℤ B) (n : ℕ) :
    -- D₁: Dual Lie–Jordan Leibniz & Dyadic Defect Tower
    (comm H (U * V) = anticomm H U * V - U * anticomm H V ∧
     (X * X + X) * idempotencyDefect X = idempotencyDefect (X * X)) ∧
    -- D₂: Peirce–Cartan Grading & ad_P³ = ad_P
    (invS P * invS P = 1 ∧
     comm P (comm P (comm P A)) = comm P A ∧
     comm P (comm P A * comm P C) = 0) ∧
    -- D₃: Nilpotent Cones & Cl_{1,1} Tetraktys
    (conePlus P A * conePlus P A = 0 ∧
     coneMinus P C * coneMinus P C = 0 ∧
     genPhi P A C * genPhi P A C = genV P A C ∧
     genJ P A C * genJ P A C = -genV P A C ∧
     genJ P A C * genPhi P A C = genSig P A C ∧
     genSig P A C = invS P * genV P A C) ∧
    -- D₄: Sandwich Complementarity & Double-Derivation Trinity
    (sandwichCross P A C X + sandwichSame P A C X = genPhi P A C * X * genPhi P A C ∧
     derivSqPhi P A C X - derivSqJ P A C X = (4 : ℤ) • sandwichSame P A C X) ∧
    -- D₅: Homogenized ℤ₂ × ℤ₂ Projectors
    (hProjV P A C X + hProjPhi P A C X + hProjJ P A C X + hProjSig P A C X =
      (8 : ℤ) • ((genV P A C * genV P A C) * X)) ∧
    -- D₆: Operator S₃ Cyclotomic Braiding
    (1 + cubeRootOp P A C + cubeRootOpConj P A C = 0 ∧
     genPhi P A C * cubeRootOp P A C = cubeRootOpConj P A C * genPhi P A C) ∧
    -- D₇: Unipotent BCH & Palindromic Steinberg Braiding
    (steinbergBraid P A C * steinbergBraidInv P A C = 1 ∧
     steinbergBraid P A C - steinbergBraidDual P A C = (1 - genV P A C) * genPhi P A C ∧
     parityConj P (steinbergBraid P A C) = steinbergBraidInv P A C) ∧
    -- D₈: Bergman Operator & Cross-Ratio
    (bergmanOp P A C 1 = 1 - genV P A C ∧
     bergmanOp P A C (genV P A C) = (1 - genV P A C) * genV P A C) ∧
    -- D₉: Hodge–De Rham Complex & d̄ = -⋆ d ⋆
    (hodgeStar P (hodgeStar P X) = X ∧
     superDerivPlusBar P A X = -hodgeStar P (superDerivPlus P A (hodgeStar P X)) ∧
     hodgeLaplacianPhi P A C X = (2 : ℤ) • (genV P A C * X + X * genV P A C)) ∧
    -- D₁₀: Chiral Euler Factors & Cyclotomic Evaluation
    ((1 - qgtPlus P A C) * (1 - qgtMinus P A C) = zetaFactor P A C ∧
     cyclotomicSix (peirceTransferJ P A C) = 1 - genV P A C) ∧
    -- D₁₁: 5-Graded Endomorphism Charge Annihilator
    ((endomorphismCharge P ^ 5) K - (5 : ℤ) • (endomorphismCharge P ^ 3) K +
      (4 : ℤ) • endomorphismCharge P K = 0) ∧
    -- D₁₂: Iterated Defect Tower Split & Orthogonality
    (idempotencyDefect^[n] (genV P A C) =
      idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C) ∧
     idempotencyDefect^[n] (qgtPlus P A C) * idempotencyDefect^[n] (qgtMinus P A C) = 0) ∧
    -- D₁₃: Boundary Dependence / Even-Grade Shift Invariance
    (genV P (A + evenGrade P X) (C + evenGrade P Y) = genV P A C ∧
     genPhi P (A + evenGrade P X) (C + evenGrade P Y) = genPhi P A C) ∧
    -- D₁₄: Grading-Twisted Star & Principal-Ideal Pairing
    (invS P * star (invS P * star X * invS P) * invS P = X ∧
     invS P * star (Y * P) * invS P * (X * P) =
      peirce11 P (star Y) * peirce11 P X - conePlus P (star Y) * coneMinus P X) ∧
    -- D₁₅: Directed Flow-Imbalance, Magnetic Laplacian, DAG Resolvent & Block Intervention
    (symAdj W + skewAdj W = (2 : ℤ) • W ∧
     gradingTwistedAdj P A = genPhi P A (star A) ∧
     gradingTwistedAdj P A * gradingTwistedAdj P A = genV P A (star A) ∧
     (star Deg = Deg →
       star (gradingTwistedLaplacian P Deg A) = gradingTwistedLaplacian P Deg A) ∧
     (1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 ∧
     twoStepResolvent P₁ P₂ A C * (1 - twoStepUpper P₁ P₂ A C) = 1 ∧
     P * blockLower P F₁ L₁ D₁ * (1 - P) = 0 ∧
     blockLower P F₁ L₁ D₁ * blockLower P F₂ L₂ D₂ =
       blockLower P (F₁ * P * F₂) (L₁ * P * F₂ + D₁ * (1 - P) * L₂) (D₁ * (1 - P) * D₂) ∧
     peirce11 P (idempotentCompression Q (blockLower P F₁ L₁ D₁)) = peirce11 P F₁) := by
  have hDyadic : (X * X + X) * idempotencyDefect X = idempotencyDefect (X * X) := by
    simp only [idempotencyDefect]
    noncomm_ring
  rcases archetype_A1_dual_leibniz_and_jacobi H U V with ⟨_, hA1_leib, _, _, _, _⟩
  rcases archetype_A2_peirce_cartan_grading_and_tangent_closure hP A C with
    ⟨hA2_s, _, _, hA2_ad3, _, hA2_even, _⟩
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table hP A C with
    ⟨hA3_np, hA3_nm, hA3_phi2, hA3_j2, _, hA3_jphi, _, _, hA3_sig, _, _, _, _, _, _⟩
  rcases archetype_A4_sandwich_complementarity_and_trinity hP A C X with
    ⟨hA4_sum, _, _, _, hA4_diff, _, _, _, _, _, _, _, _⟩
  rcases archetype_A13_homogenized_projectors hP A C X with
    ⟨hA13_part, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases archetype_A59_s3_operator_cyclotomic_braiding_and_reflections hP A C with
    ⟨hA59_sum, _, _, _, _, hA59_braid, _, _, _, _, _, _, _, _⟩
  rcases steinbergBraid_dual_expansion_and_difference hP A C with
    ⟨_, hSt_diff, _, _⟩
  rcases archetype_A23_bergman_operator hP A C with
    ⟨hBerg1, _, _, _, hBerg2, _, _⟩
  rcases archetype_A33_hodge_star_and_half_twists hP A C X with
    ⟨hHodge_inv, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases archetype_A34_hodge_conjugate_codifferentials hP A C X with
    ⟨hCodiff, _, _, _, _, _⟩
  rcases chiralEuler_factorizations hP A C with ⟨hEuler, _, _, _⟩
  rcases archetype_A58_operator_cyclotomic_roots_and_discriminants hP A C with
    ⟨_, _, _, hCyc6, _, _, _, _, _, _, _, _, _⟩
  rcases tetraktys_evenGrade_shift hP A C X Y with
    ⟨hShiftPhi, _, hShiftV, _⟩
  exact ⟨⟨hA1_leib, hDyadic⟩,
    ⟨hA2_s, hA2_ad3, hA2_even⟩,
    ⟨hA3_np, hA3_nm, hA3_phi2, hA3_j2, hA3_jphi, hA3_sig⟩,
    ⟨hA4_sum, hA4_diff⟩,
    hA13_part,
    ⟨hA59_sum, hA59_braid⟩,
    ⟨(steinbergBraid_mul_inv hP A C).1, hSt_diff, parityConj_steinbergBraid hP A C⟩,
    ⟨hBerg1, hBerg2⟩,
    ⟨hHodge_inv, hCodiff, hodgeLaplacianPhi_eq hP A C X⟩,
    ⟨hEuler, hCyc6⟩,
    endomorphismCharge_fifth hP K,
    ⟨genV_defect_iterates_cycle_split hP A C n,
     (qgt_defect_iterates_orthogonal hP A C n).1⟩,
    ⟨hShiftV, hShiftPhi⟩,
    ⟨grading_star_involutive hPs hP X, twisted_ideal_pairing hP hPs X Y⟩,
    ⟨symAdj_add_skewAdj W,
     gradingTwistedAdj_eq_genPhi hPs hP A,
     gradingTwistedAdj_sq hPs hP A,
     fun hDs => star_gradingTwistedLaplacian hPs hDs A,
     twoStepResolvent_left_inv h1 h2 h12 h21 A C,
     twoStepResolvent_right_inv h1 h2 h12 h21 A C,
     blockLower_upper_right hP F₁ L₁ D₁,
     blockLower_mul hP F₁ L₁ D₁ F₂ L₂ D₂,
     idempotentCompression_blockLower_peirce11 hP hPQ hQP F₁ L₁ D₁⟩⟩

/-! A selected joint consequence of the `D₁₅` directed-flow/DAG identities
and the independently proved `D₁₆` sheaf-inspired operator identities. The
full `D₁`–`D₁₅` theorem remains `master_causal_poset_D1_to_D15`; this theorem
does not repackage every earlier conjunct. -/
/-- Selected joint `D₁₅` and `D₁₆` operator identities. -/
theorem selected_D15_D16_operator_synthesis
    {B : Type*} [Ring B] [StarRing B]
    {P Q P₁ P₂ R_u R_v U_gauge d₀ d₁ : B}
    (hP : P * P = P) (hPs : star P = P)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (hU : star U_gauge * U_gauge = 1) (hd : d₁ * d₀ = 0)
    (X W A C F₁ L₁ D₁ : B) :
    (symAdj W + skewAdj W = (2 : ℤ) • W ∧
     gradingTwistedAdj P A = genPhi P A (star A) ∧
     (1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 ∧
     peirce11 P (idempotentCompression Q (blockLower P F₁ L₁ D₁)) = peirce11 P F₁) ∧
    (star (sheafLaplacian0 P R_u R_v) = sheafLaplacian0 P R_u R_v ∧
     sheafLaplacian0 P R_u R_v =
       sheafBlock11 P R_u + sheafBlock10 P R_u R_v +
       sheafBlock01 P R_u R_v + sheafBlock00 P R_v ∧
     sheafDirichletForm P R_u R_v X =
       star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X) ∧
     sheafLaplacian0 P (U_gauge * R_u) (U_gauge * R_v) = sheafLaplacian0 P R_u R_v ∧
     sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
       sheafHodgeDown d₀ * sheafHodgeDown d₀ + sheafHodgeUp d₁ * sheafHodgeUp d₁ ∧
     sheafCoboundary0 P (coneMinus P C) (conePlus P A) = -genJ P A C ∧
     sheafCoboundary0 P (coneMinus P C) (-conePlus P A) = genPhi P A C ∧
     sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A)) := by
  rcases stage_D16_cellular_sheaf_operator_master_synthesis
    (R_u := R_u) (R_v := R_v) (X := X) (A := A) (C := C) hP hPs hU hd with
    ⟨hS1, hS2, hS3, _, _, hS6, _, _, _, _, hS11, hS12, hS13, hS14⟩
  exact ⟨⟨symAdj_add_skewAdj W,
          gradingTwistedAdj_eq_genPhi hPs hP A,
          twoStepResolvent_left_inv h1 h2 h12 h21 A C,
          idempotentCompression_blockLower_peirce11 hP hPQ hQP F₁ L₁ D₁⟩,
         ⟨hS1, hS2, hS3, hS6, hS11, hS12, hS13, hS14⟩⟩

/-- Selected joint synthesis of `D₁₅` directed-flow/DAG identities with the full
`D₁₆`–`D₁₈` (`S₁ → S₁₅`) cellular sheaf, horizon normality, curved Weitzenböck/Bianchi,
and fractal Hodge sheet filtering identities. -/
theorem selected_D15_to_D18_operator_synthesis
    {B : Type*} [Ring B] [StarRing B]
    {P Q P₁ P₂ R_u R_v U_gauge d₀ d₁ d₂ : B}
    (hP : P * P = P) (hPs : star P = P)
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0)
    (hU : star U_gauge * U_gauge = 1) (hd : d₁ * d₀ = 0)
    (X W A C F₁ L₁ D₁ : B) (n : ℕ) :
    -- D₁₅ + D₁₆ joint synthesis:
    ((symAdj W + skewAdj W = (2 : ℤ) • W ∧
      gradingTwistedAdj P A = genPhi P A (star A) ∧
      (1 - twoStepUpper P₁ P₂ A C) * twoStepResolvent P₁ P₂ A C = 1 ∧
      peirce11 P (idempotentCompression Q (blockLower P F₁ L₁ D₁)) = peirce11 P F₁) ∧
     (star (sheafLaplacian0 P R_u R_v) = sheafLaplacian0 P R_u R_v ∧
      sheafLaplacian0 P R_u R_v =
        sheafBlock11 P R_u + sheafBlock10 P R_u R_v +
        sheafBlock01 P R_u R_v + sheafBlock00 P R_v ∧
      sheafDirichletForm P R_u R_v X =
        star (sheafCoboundary0 P R_u R_v * X) * (sheafCoboundary0 P R_u R_v * X) ∧
      sheafLaplacian0 P (U_gauge * R_u) (U_gauge * R_v) = sheafLaplacian0 P R_u R_v ∧
      sheafHodgeLaplacian d₀ d₁ * sheafHodgeLaplacian d₀ d₁ =
        sheafHodgeDown d₀ * sheafHodgeDown d₀ + sheafHodgeUp d₁ * sheafHodgeUp d₁ ∧
      sheafCoboundary0 P (coneMinus P C) (conePlus P A) = -genJ P A C ∧
      sheafCoboundary0 P (coneMinus P C) (-conePlus P A) = genPhi P A C ∧
      sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) = genV P A (star A))) ∧
    -- D₁₇ (S₈ → S₁₁) split-complex separation, edge Laplacian, horizon normality & QGT Hodge:
    (sheafCoboundary0 P R_u R_v * invS P = sheafCoboundary0Sym P R_u R_v ∧
     sheafEdgeLaplacian1 P R_u R_v = R_u * P * star R_u + R_v * (1 - P) * star R_v ∧
     comm (star (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)))
          (sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A)) = 0 ∧
     star (sheafCoboundary0Sym P (coneMinus P (star A)) (conePlus P A)) *
       sheafCoboundary0 P (coneMinus P (star A)) (conePlus P A) = genSig P A (star A) ∧
     sheafHodgeDown (conePlus P A) = qgtPlus P A (star A) ∧
     sheafHodgeUp (conePlus P A) = qgtMinus P A (star A)) ∧
    -- D₁₈ (S₁₂ → S₁₅) curved Weitzenböck, Bianchi & fractal Hodge sheet filtering:
    (d₂ * sheafCurvature2 d₀ d₁ = sheafCurvature2 d₁ d₂ * d₀ ∧
     sheafHodgeUp (conePlus P A) * mandelbrotTower n (qgtPlus P A (star A)) = 0 ∧
     sheafHodgeDown (conePlus P A) * mandelbrotTower n (qgtMinus P A (star A)) = 0 ∧
     sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
       mandelbrotTower n (qgtPlus P A (star A)) =
       qgtPlus P A (star A) * mandelbrotTower n (qgtPlus P A (star A)) ∧
     sheafHodgeLaplacian (conePlus P A) (conePlus P A) *
       mandelbrotTower n (qgtMinus P A (star A)) =
       qgtMinus P A (star A) * mandelbrotTower n (qgtMinus P A (star A))) := by
  have h1516 :=
    selected_D15_D16_operator_synthesis (R_u := R_u) (R_v := R_v)
      hP hPs hPQ hQP h1 h2 h12 h21 hU hd X W A C F₁ L₁ D₁
  rcases stage_D17_extended_cellular_sheaf_hodge_and_tetraktys_synthesis
    (R_u := R_u) (R_v := R_v) (U := U_gauge) (A := A) hP hPs with
    ⟨hSC1, _, _, _, hEd1, _, _, _, hNorm, hSig1, _, hC2, hC3, _, _⟩
  rcases stage_D18_curved_sheaf_bianchi_and_fractal_hodge_cohomology
    (d₀ := d₀) (d₁ := d₁) (d₂ := d₂) (A := A) hP hPs n with
    ⟨_, hBianchi1, _, hUpX, hDownY, hLapX, hLapY⟩
  exact ⟨h1516, ⟨hSC1, hEd1, hNorm, hSig1, hC2, hC3⟩, ⟨hBianchi1, hUpX, hDownY, hLapX, hLapY⟩⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
