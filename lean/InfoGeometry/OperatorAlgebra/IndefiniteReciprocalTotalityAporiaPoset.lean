/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Relation
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge
import InfoGeometry.OperatorAlgebra.SolveEtCoagulaPeirceAporiaPoset
import InfoGeometry.Thermo.OnsagerOperatorClosure

/-!
# Indefinite Reciprocal Totality, Socratic Aporia, and Parity-Soldered Meta-Cognitive Poset

Formalizes the complete six-phase non-commutative epistemic algebra (`Ax.1`–`Ax.4`,
`Prop.1`–`Prop.6`, `Thm. Ω`), its 16-node 7-stratum acyclic causal poset `(𝒫, ≺)`,
concrete non-vacuous integer-matrix and infinite-stage models, and bridges into
the repository's `PeirceSpine`, `Leibniz` derivation (`peirceGradingDeriv`), and
`OnsagerClosure.TimeReversal` spines.

Every algebraic identity holds over an arbitrary associative unital ring `[Ring E]`
(with `2Z = 0 → Z = 0` supplied explicitly only for `[P, J_Ω] ≠ 0` in `Thm. Ω`),
without commutativity, scalar division, or vacuous placeholder assumptions.
-/

namespace InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityAporiaPoset

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge
open InfoGeometry.OperatorAlgebra.SolveEtCoagulaPeirceAporiaPoset

/-! ## Section 1: Primitives, Binary Cut, and Fourfold Decomposition (`Prop.1`–`Prop.2`) -/

section CoreAlgebra

variable {E : Type*} [Ring E]

/-- Shadow complement `Q := 1 - P` of a selective operational projection `P`. -/
def shadowComp (P : E) : E :=
  1 - P

/-- Partitioning polarity `Γ := P - Q = P - (1 - P)` (coinciding with `invS P`). -/
def partitionPolarity (P : E) : E :=
  P - shadowComp P

@[simp]
theorem partitionPolarity_eq_invS (P : E) :
    partitionPolarity P = invS P :=
  rfl

/-- Internal self-consistency `T := P Ω P` (coinciding with `peirce11 P Ω`). -/
def consciousThesis (P Ω : E) : E :=
  peirce11 P Ω

/-- Outward projection `X := Q Ω P = (1 - P) Ω P` (`coneMinus P Ω`). -/
def outwardProjection (P Ω : E) : E :=
  coneMinus P Ω

/-- Inward shadow-intrusion `Y := P Ω Q = P Ω (1 - P)` (`conePlus P Ω`). -/
def inwardIntrusion (P Ω : E) : E :=
  conePlus P Ω

/-- Autonomous unexamined ground `G := Q Ω Q` (`peirce00 P Ω`). -/
def autonomousGround (P Ω : E) : E :=
  peirce00 P Ω

/-- **`Prop.1` (Orthogonality & Polarity Involution — Stratum 1)**:
`Q² = Q`, `PQ = QP = 0`, `P + Q = 1`, `Γ² = 1`, `ΓP = PΓ = P`, and `ΓQ = QΓ = -Q`. -/
theorem prop1_orthogonality_and_polarity_involution
    {P : E} (hP : P * P = P) :
    shadowComp P * shadowComp P = shadowComp P ∧
    P * shadowComp P = 0 ∧
    shadowComp P * P = 0 ∧
    P + shadowComp P = 1 ∧
    partitionPolarity P * partitionPolarity P = 1 ∧
    partitionPolarity P * P = P ∧
    P * partitionPolarity P = P ∧
    partitionPolarity P * shadowComp P = -shadowComp P ∧
    shadowComp P * partitionPolarity P = -shadowComp P := by
  have h := binary_cut_idempotent_and_grading_laws P hP
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  dsimp [shadowComp]
  noncomm_ring

/-- **`Prop.2` (Fourfold Decomposition & Unilateral Nilpotency — Stratum 2)**:
With `T = PΩP`, `X = QΩP`, `Y = PΩQ`, `G = QΩQ`, and `[P, Ω] ≠ 0`:
1. `Ω = T + X + Y + G`;
2. `[P, Ω] = Y - X`;
3. `(X ≠ 0 ∨ Y ≠ 0)`;
4. `X² = 0 ∧ Y² = 0`. -/
theorem prop2_fourfold_decomposition_and_unilateral_nilpotency
    {P Ω : E} (hP : P * P = P) (hnc : PeirceSpine.comm P Ω ≠ 0) :
    Ω = consciousThesis P Ω + outwardProjection P Ω +
        inwardIntrusion P Ω + autonomousGround P Ω ∧
    PeirceSpine.comm P Ω = inwardIntrusion P Ω - outwardProjection P Ω ∧
    (outwardProjection P Ω ≠ 0 ∨ inwardIntrusion P Ω ≠ 0) ∧
    (outwardProjection P Ω * outwardProjection P Ω = 0 ∧
      inwardIntrusion P Ω * inwardIntrusion P Ω = 0) := by
  have hdecomp :
      Ω = consciousThesis P Ω + outwardProjection P Ω +
          inwardIntrusion P Ω + autonomousGround P Ω := by
    dsimp [consciousThesis, outwardProjection, inwardIntrusion, autonomousGround,
      peirce11, coneMinus, conePlus, peirce00]
    noncomm_ring
  have hcomm : PeirceSpine.comm P Ω = inwardIntrusion P Ω - outwardProjection P Ω := by
    dsimp [PeirceSpine.comm, inwardIntrusion, outwardProjection, conePlus, coneMinus]
    noncomm_ring
  have hnz : outwardProjection P Ω ≠ 0 ∨ inwardIntrusion P Ω ≠ 0 := by
    by_contra hboth
    push Not at hboth
    apply hnc
    rw [hcomm, hboth.2, hboth.1, sub_zero]
  refine ⟨hdecomp, hcomm, hnz, ?_, ?_⟩
  · exact coneMinus_mul_coneMinus hP Ω Ω
  · exact conePlus_mul_conePlus hP Ω Ω

/-! ## Section 2: Transcendent Function Quartet (`Prop.3`) -/

/-- Integrative bridge `F := X + Y` (`oddGrade P Ω` / `genPhi P Ω Ω`). -/
def integrativeBridge (P Ω : E) : E :=
  outwardProjection P Ω + inwardIntrusion P Ω

@[simp]
theorem integrativeBridge_eq_oddGrade (P Ω : E) :
    integrativeBridge P Ω = oddGrade P Ω := by
  dsimp [integrativeBridge, outwardProjection, inwardIntrusion,
    coneMinus, conePlus, oddGrade]
  rw [add_comm]

@[simp]
theorem integrativeBridge_eq_genPhi (P Ω : E) :
    integrativeBridge P Ω = genPhi P Ω Ω := by
  dsimp [integrativeBridge, outwardProjection, inwardIntrusion, genPhi]
  rw [add_comm]

/-- Shared substantive gravity `M := XY + YX = {X, Y}` (`genV P Ω Ω`). -/
def substantiveGravity (P Ω : E) : E :=
  outwardProjection P Ω * inwardIntrusion P Ω +
    inwardIntrusion P Ω * outwardProjection P Ω

@[simp]
theorem substantiveGravity_eq_genV (P Ω : E) :
    substantiveGravity P Ω = genV P Ω Ω := by
  dsimp [substantiveGravity, outwardProjection, inwardIntrusion, genV, anticomm]
  rw [add_comm]

/-- Directional tension `K := YX - XY = [Y, X]` (`genSig P Ω Ω`). -/
def directionalTension (P Ω : E) : E :=
  inwardIntrusion P Ω * outwardProjection P Ω -
    outwardProjection P Ω * inwardIntrusion P Ω

@[simp]
theorem directionalTension_eq_genSig (P Ω : E) :
    directionalTension P Ω = genSig P Ω Ω :=
  rfl

/-- **`Prop.3` (Oddness of Integrative Bridge & Gravity/Tension Duality — Stratum 3)**:
For any idempotent `P` and `[P, Ω] ≠ 0`:
1. `F ≠ 0`, `ΓF = [P, Ω]`, `Γ [P, Ω] = F`, and `ΓF + FΓ = 0`;
2. `F² = M` and `ΓM = MΓ`;
3. `K = ΓM = MΓ`, and `(YX = XY ↔ M = 0) ∧ (M = 0 ↔ YX = 0 ∧ XY = 0)`. -/
theorem prop3_integrative_bridge_gravity_and_tension
    {P Ω : E} (hP : P * P = P) (hnc : PeirceSpine.comm P Ω ≠ 0) :
    integrativeBridge P Ω ≠ 0 ∧
    partitionPolarity P * integrativeBridge P Ω = PeirceSpine.comm P Ω ∧
    partitionPolarity P * PeirceSpine.comm P Ω = integrativeBridge P Ω ∧
    partitionPolarity P * integrativeBridge P Ω +
      integrativeBridge P Ω * partitionPolarity P = 0 ∧
    integrativeBridge P Ω * integrativeBridge P Ω = substantiveGravity P Ω ∧
    partitionPolarity P * substantiveGravity P Ω =
      substantiveGravity P Ω * partitionPolarity P ∧
    directionalTension P Ω = partitionPolarity P * substantiveGravity P Ω ∧
    directionalTension P Ω = substantiveGravity P Ω * partitionPolarity P ∧
    ((inwardIntrusion P Ω * outwardProjection P Ω =
        outwardProjection P Ω * inwardIntrusion P Ω ↔ substantiveGravity P Ω = 0) ∧
      (substantiveGravity P Ω = 0 ↔
        inwardIntrusion P Ω * outwardProjection P Ω = 0 ∧
          outwardProjection P Ω * inwardIntrusion P Ω = 0)) := by
  have hΓF : partitionPolarity P * integrativeBridge P Ω = PeirceSpine.comm P Ω := by
    rw [partitionPolarity_eq_invS, integrativeBridge_eq_genPhi]
    have h1 : invS P * genPhi P Ω Ω = genJ P Ω Ω :=
      (archetype_A27_grading_parities hP Ω Ω).2.2.2.2.2.2.1
    have h2 : genJ P Ω Ω = PeirceSpine.comm P Ω := by
      dsimp [genJ, PeirceSpine.comm, conePlus, coneMinus]
      noncomm_ring
    exact h1.trans h2
  have hF_ne : integrativeBridge P Ω ≠ 0 := by
    intro hF0
    apply hnc
    rw [← hΓF, hF0, mul_zero]
  have hΓsq : partitionPolarity P * partitionPolarity P = 1 :=
    (prop1_orthogonality_and_polarity_involution hP).2.2.2.2.1
  have hΓcomm : partitionPolarity P * PeirceSpine.comm P Ω = integrativeBridge P Ω := by
    calc
      partitionPolarity P * PeirceSpine.comm P Ω =
          partitionPolarity P * (partitionPolarity P * integrativeBridge P Ω) := by rw [hΓF]
      _ = (partitionPolarity P * partitionPolarity P) * integrativeBridge P Ω := by
          noncomm_ring
      _ = integrativeBridge P Ω := by rw [hΓsq, one_mul]
  have hAnti : partitionPolarity P * integrativeBridge P Ω +
      integrativeBridge P Ω * partitionPolarity P = 0 := by
    rw [partitionPolarity_eq_invS, integrativeBridge_eq_genPhi]
    exact (archetype_A27_grading_parities hP Ω Ω).2.2.2.2.2.2.2.2.2.2.1
  have hFsq : integrativeBridge P Ω * integrativeBridge P Ω = substantiveGravity P Ω := by
    rw [integrativeBridge_eq_genPhi, substantiveGravity_eq_genV]
    exact (transcendent_quartet_algebra hP Ω Ω).2.1
  have hΓM : partitionPolarity P * substantiveGravity P Ω =
      substantiveGravity P Ω * partitionPolarity P := by
    rw [partitionPolarity_eq_invS, substantiveGravity_eq_genV]
    have hq := (transcendent_quartet_algebra hP Ω Ω).2.2.2.2.2.1
    exact hq.1.trans hq.2.symm
  have hK1 : directionalTension P Ω = partitionPolarity P * substantiveGravity P Ω := by
    rw [directionalTension_eq_genSig, partitionPolarity_eq_invS, substantiveGravity_eq_genV]
    exact ((transcendent_quartet_algebra hP Ω Ω).2.2.2.2.2.1.1).symm
  have hK2 : directionalTension P Ω = substantiveGravity P Ω * partitionPolarity P := by
    rw [hK1, hΓM]
  have hP_YX : P * (inwardIntrusion P Ω * outwardProjection P Ω) =
      inwardIntrusion P Ω * outwardProjection P Ω := by
    dsimp [inwardIntrusion, outwardProjection]
    peirce_nf hP
  have hP_XY : P * (outwardProjection P Ω * inwardIntrusion P Ω) = 0 := by
    dsimp [inwardIntrusion, outwardProjection]
    peirce_nf hP
  have hM_iff : substantiveGravity P Ω = 0 ↔
      inwardIntrusion P Ω * outwardProjection P Ω = 0 ∧
        outwardProjection P Ω * inwardIntrusion P Ω = 0 := by
    constructor
    · intro hM
      have hPM : P * substantiveGravity P Ω =
          inwardIntrusion P Ω * outwardProjection P Ω := by
        dsimp [substantiveGravity]
        rw [mul_add, hP_XY, zero_add, hP_YX]
      have hYX : inwardIntrusion P Ω * outwardProjection P Ω = 0 := by
        calc
          inwardIntrusion P Ω * outwardProjection P Ω =
              P * substantiveGravity P Ω := hPM.symm
          _ = P * 0 := by rw [hM]
          _ = 0 := mul_zero P
      have hXY : outwardProjection P Ω * inwardIntrusion P Ω = 0 := by
        dsimp [substantiveGravity] at hM
        rw [hYX, add_zero] at hM
        exact hM
      exact ⟨hYX, hXY⟩
    · rintro ⟨hYX, hXY⟩
      dsimp [substantiveGravity]
      rw [hXY, hYX, add_zero]
  have hcomm_iff :
      inwardIntrusion P Ω * outwardProjection P Ω =
        outwardProjection P Ω * inwardIntrusion P Ω ↔ substantiveGravity P Ω = 0 := by
    constructor
    · intro heq
      have hYX : inwardIntrusion P Ω * outwardProjection P Ω = 0 := by
        calc
          inwardIntrusion P Ω * outwardProjection P Ω =
              P * (inwardIntrusion P Ω * outwardProjection P Ω) := hP_YX.symm
          _ = P * (outwardProjection P Ω * inwardIntrusion P Ω) := by rw [heq]
          _ = 0 := hP_XY
      have hXY : outwardProjection P Ω * inwardIntrusion P Ω = 0 := heq.symm.trans hYX
      exact hM_iff.mpr ⟨hYX, hXY⟩
    · intro hM
      obtain ⟨hYX, hXY⟩ := hM_iff.mp hM
      rw [hYX, hXY]
  exact ⟨hF_ne, hΓF, hΓcomm, hAnti, hFsq, hΓM, hK1, hK2, hcomm_iff, hM_iff⟩

/-! ## Section 3: Exact Socratic Aporia & Dogmatic Truncation (`Prop.4`–`Prop.5`) -/

/-- Conscious Socratic aporia `𝒜₀ := T - T²`. -/
def socraticAporia (P Ω : E) : E :=
  consciousThesis P Ω - consciousThesis P Ω * consciousThesis P Ω

/-- Shadow-ground aporia `G - G²`. -/
def groundAporia (P Ω : E) : E :=
  autonomousGround P Ω - autonomousGround P Ω * autonomousGround P Ω

/-- Severed block-diagonal dogma `Σ₀ := (2T - P) + (2G - Q)`. -/
def severedDogma (P Ω : E) : E :=
  (2 * consciousThesis P Ω - P) + (2 * autonomousGround P Ω - shadowComp P)

/-- Integrative scale bridge `B := 2F`. -/
def scaledBridge (P Ω : E) : E :=
  2 * integrativeBridge P Ω

theorem severedDogma_eq_two_evenGrade_sub_one (P Ω : E) :
    severedDogma P Ω = 2 * evenGrade P Ω - 1 := by
  dsimp [severedDogma, consciousThesis, autonomousGround, shadowComp,
    peirce11, peirce00, evenGrade]
  noncomm_ring

/-- **`Prop.4` (Exact Socratic Aporia Theorem — Stratum 4)**:
Under `P² = P` and `Ω² = Ω`:
1. `T - T² = Y X` and `G - G² = X Y`;
2. `(T - T²) + (G - G²) = M` and `(T - T²) - (G - G²) = K`;
3. `T Y + Y G = Y` and `X T + G X = X`. -/
theorem prop4_exact_socratic_aporia_and_intertwining
    {P Ω : E} (hP : P * P = P) (hΩ : Ω * Ω = Ω) :
    socraticAporia P Ω = inwardIntrusion P Ω * outwardProjection P Ω ∧
    groundAporia P Ω = outwardProjection P Ω * inwardIntrusion P Ω ∧
    socraticAporia P Ω + groundAporia P Ω = substantiveGravity P Ω ∧
    socraticAporia P Ω - groundAporia P Ω = directionalTension P Ω ∧
    consciousThesis P Ω * inwardIntrusion P Ω +
      inwardIntrusion P Ω * autonomousGround P Ω = inwardIntrusion P Ω ∧
    outwardProjection P Ω * consciousThesis P Ω +
      autonomousGround P Ω * outwardProjection P Ω = outwardProjection P Ω := by
  have h1 : P + (1 - P) = (1 : E) := by noncomm_ring
  have hPQ : P * (1 - P) = 0 := by noncomm_ring [hP]
  have hQP : (1 - P) * P = 0 := by noncomm_ring [hP]
  have hA0 : socraticAporia P Ω = inwardIntrusion P Ω * outwardProjection P Ω := by
    calc
      socraticAporia P Ω = peirce11 P (Ω * Ω) - peirce11 P Ω * peirce11 P Ω := by
          rw [hΩ]; rfl
      _ = P * Ω * 1 * Ω * P - (P * Ω * P) * (P * Ω * P) := by
          dsimp [peirce11]; noncomm_ring
      _ = P * Ω * (P + (1 - P)) * Ω * P - (P * Ω * P) * (P * Ω * P) := by rw [h1]
      _ = (P * Ω * (1 - P)) * ((1 - P) * Ω * P) := by
          peirce_nf hP
  have hG0 : groundAporia P Ω = outwardProjection P Ω * inwardIntrusion P Ω := by
    calc
      groundAporia P Ω = peirce00 P (Ω * Ω) - peirce00 P Ω * peirce00 P Ω := by
          rw [hΩ]; rfl
      _ = (1 - P) * Ω * 1 * Ω * (1 - P) -
            ((1 - P) * Ω * (1 - P)) * ((1 - P) * Ω * (1 - P)) := by
          dsimp [peirce00]; noncomm_ring
      _ = (1 - P) * Ω * (P + (1 - P)) * Ω * (1 - P) -
            ((1 - P) * Ω * (1 - P)) * ((1 - P) * Ω * (1 - P)) := by rw [h1]
      _ = ((1 - P) * Ω * P) * (P * Ω * (1 - P)) := by
          peirce_nf hP
  have hY : consciousThesis P Ω * inwardIntrusion P Ω +
      inwardIntrusion P Ω * autonomousGround P Ω = inwardIntrusion P Ω := by
    calc
      consciousThesis P Ω * inwardIntrusion P Ω +
          inwardIntrusion P Ω * autonomousGround P Ω =
          (P * Ω * P) * (P * Ω * (1 - P)) +
            (P * Ω * (1 - P)) * ((1 - P) * Ω * (1 - P)) := rfl
      _ = P * Ω * (P + (1 - P)) * Ω * (1 - P) := by
          peirce_nf hP
      _ = P * Ω * 1 * Ω * (1 - P) := by rw [h1]
      _ = P * (Ω * Ω) * (1 - P) := by noncomm_ring
      _ = inwardIntrusion P Ω := by rw [hΩ]; rfl
  have hX : outwardProjection P Ω * consciousThesis P Ω +
      autonomousGround P Ω * outwardProjection P Ω = outwardProjection P Ω := by
    calc
      outwardProjection P Ω * consciousThesis P Ω +
          autonomousGround P Ω * outwardProjection P Ω =
          ((1 - P) * Ω * P) * (P * Ω * P) +
            ((1 - P) * Ω * (1 - P)) * ((1 - P) * Ω * P) := rfl
      _ = (1 - P) * Ω * (P + (1 - P)) * Ω * P := by
          peirce_nf hP
      _ = (1 - P) * Ω * 1 * Ω * P := by rw [h1]
      _ = (1 - P) * (Ω * Ω) * P := by noncomm_ring
      _ = outwardProjection P Ω := by rw [hΩ]; rfl
  refine ⟨hA0, hG0, ?_, ?_, hY, hX⟩
  · rw [hA0, hG0, substantiveGravity, add_comm]
  · rw [hA0, hG0, directionalTension]

/-- **`Prop.5` (Incompleteness of Dogmatic Truncation — Stratum 4)**:
Under `P² = P` and `Ω² = Ω`, the severed diagonal `Σ₀ = (2T - P) + (2G - Q)`
and bridge `B = 2F` strictly anticommute (`Σ₀ B + B Σ₀ = 0`), and `Σ₀` fails
to square to `1` by `1 - Σ₀² = B² = 4M`. -/
theorem prop5_dogmatic_truncation_defect
    {P Ω : E} (hP : P * P = P) (hΩ : Ω * Ω = Ω) :
    severedDogma P Ω * scaledBridge P Ω + scaledBridge P Ω * severedDogma P Ω = 0 ∧
    1 - severedDogma P Ω * severedDogma P Ω = scaledBridge P Ω * scaledBridge P Ω ∧
    scaledBridge P Ω * scaledBridge P Ω = 4 * substantiveGravity P Ω := by
  have hp4 := prop4_exact_socratic_aporia_and_intertwining hP hΩ
  have hAntiY :
      (2 * consciousThesis P Ω - P) * inwardIntrusion P Ω +
        inwardIntrusion P Ω * (2 * autonomousGround P Ω - shadowComp P) =
        2 * (consciousThesis P Ω * inwardIntrusion P Ω +
          inwardIntrusion P Ω * autonomousGround P Ω - inwardIntrusion P Ω) := by
    dsimp [consciousThesis, inwardIntrusion, autonomousGround, shadowComp]
    simp only [two_mul]
    peirce_nf hP
  have hAntiX :
      (2 * autonomousGround P Ω - shadowComp P) * outwardProjection P Ω +
        outwardProjection P Ω * (2 * consciousThesis P Ω - P) =
        2 * (outwardProjection P Ω * consciousThesis P Ω +
          autonomousGround P Ω * outwardProjection P Ω - outwardProjection P Ω) := by
    dsimp [consciousThesis, outwardProjection, autonomousGround, shadowComp]
    simp only [two_mul]
    peirce_nf hP
  have hAntiF : severedDogma P Ω * integrativeBridge P Ω +
      integrativeBridge P Ω * severedDogma P Ω = 0 := by
    have hsplit :
        severedDogma P Ω * integrativeBridge P Ω +
          integrativeBridge P Ω * severedDogma P Ω =
          ((2 * consciousThesis P Ω - P) * inwardIntrusion P Ω +
            inwardIntrusion P Ω * (2 * autonomousGround P Ω - shadowComp P)) +
          ((2 * autonomousGround P Ω - shadowComp P) * outwardProjection P Ω +
            outwardProjection P Ω * (2 * consciousThesis P Ω - P)) := by
      dsimp [severedDogma, integrativeBridge, consciousThesis, autonomousGround,
        outwardProjection, inwardIntrusion, shadowComp]
      simp only [two_mul]
      peirce_nf hP
    rw [hsplit, hAntiY, hAntiX, hp4.2.2.2.2.1, hp4.2.2.2.2.2, sub_self, sub_self,
      mul_zero, add_zero]
  have hAntiB : severedDogma P Ω * scaledBridge P Ω +
      scaledBridge P Ω * severedDogma P Ω = 0 := by
    dsimp [scaledBridge]
    calc
      severedDogma P Ω * (2 * integrativeBridge P Ω) +
          (2 * integrativeBridge P Ω) * severedDogma P Ω =
          2 * (severedDogma P Ω * integrativeBridge P Ω +
            integrativeBridge P Ω * severedDogma P Ω) := by noncomm_ring
      _ = 2 * 0 := by rw [hAntiF]
      _ = 0 := mul_zero 2
  have hFsq : integrativeBridge P Ω * integrativeBridge P Ω = substantiveGravity P Ω := by
    rw [integrativeBridge_eq_genPhi, substantiveGravity_eq_genV]
    exact (transcendent_quartet_algebra hP Ω Ω).2.1
  have hBsq : scaledBridge P Ω * scaledBridge P Ω = 4 * substantiveGravity P Ω := by
    dsimp [scaledBridge]
    calc
      (2 * integrativeBridge P Ω) * (2 * integrativeBridge P Ω) =
          4 * (integrativeBridge P Ω * integrativeBridge P Ω) := by noncomm_ring
      _ = 4 * substantiveGravity P Ω := by rw [hFsq]
  have hSigsq : 1 - severedDogma P Ω * severedDogma P Ω =
      4 * (socraticAporia P Ω + groundAporia P Ω) := by
    dsimp [severedDogma, socraticAporia, groundAporia, consciousThesis,
      autonomousGround, shadowComp]
    rw [show (2 : E) = (2 : ℤ) • (1 : E) by simp,
      show (4 : E) = (4 : ℤ) • (1 : E) by simp]
    peirce_nf hP
  have hdef : 1 - severedDogma P Ω * severedDogma P Ω =
      scaledBridge P Ω * scaledBridge P Ω := by
    rw [hSigsq, hp4.2.2.1, hBsq]
  exact ⟨hAntiB, hdef, hBsq⟩

/-! ## Section 4: Parity-Soldered Meta-Cognitive Tower (`Ax.4` & `Prop.6`) -/

/-- **`Ax.4` (Meta-Cognitive Reflection Tower)**:
At each finite stage `k : ℕ`, thematic reflection introduces a cut `P k` and
stage totality `Ω k` commuting pairwise across distinct stages `j ≠ k`. -/
structure MetaCognitiveTower (E : Type*) [Ring E] where
  P : ℕ → E
  Ω : ℕ → E
  idem_P : ∀ k, P k * P k = P k
  idem_Ω : ∀ k, Ω k * Ω k = Ω k
  noncomm_stage : ∀ k, PeirceSpine.comm (P k) (Ω k) ≠ 0
  comm_polarity_polarity :
    ∀ {j k}, j ≠ k → Commute (partitionPolarity (P j)) (partitionPolarity (P k))
  comm_polarity_bridge :
    ∀ {j k}, j ≠ k → Commute (partitionPolarity (P j)) (scaledBridge (P k) (Ω k))
  comm_bridge_bridge :
    ∀ {j k}, j ≠ k → Commute (scaledBridge (P j) (Ω j)) (scaledBridge (P k) (Ω k))

/-- Ordered prefix product `∏_{j=0}^{k-1} Γ_j` for Jordan–Wigner parity soldering. -/
def parityPrefix (Γ : ℕ → E) : ℕ → E
  | 0 => 1
  | k + 1 => parityPrefix Γ k * Γ k

/-- Parity-soldered meta-bridge `\widehat{B}_k := (∏_{j=0}^{k-1} Γ_j) B_k`. -/
def solderedBridge (S : MetaCognitiveTower E) (k : ℕ) : E :=
  parityPrefix (fun j => partitionPolarity (S.P j)) k * scaledBridge (S.P k) (S.Ω k)

/-- Cumulative parity-soldered meta-operator `D_N := ∑_{k=0}^N \widehat{B}_k`. -/
def metaDirac (S : MetaCognitiveTower E) (N : ℕ) : E :=
  (Finset.range (N + 1)).sum (solderedBridge S)

private lemma parityPrefix_comm_left {Γ : ℕ → E} {X : E} (k : ℕ)
    (h : ∀ j < k, Commute (Γ j) X) :
    Commute (parityPrefix Γ k) X := by
  induction k with
  | zero => exact Commute.one_left X
  | succ k ih =>
    have ih' : Commute (parityPrefix Γ k) X := ih fun j hj => h j (Nat.lt_succ_of_lt hj)
    have hk : Commute (Γ k) X := h k (Nat.lt_succ_self k)
    exact ih'.mul_left hk

private lemma parityPrefix_comm_pair (S : MetaCognitiveTower E) (r s : ℕ) :
    Commute (parityPrefix (fun j => partitionPolarity (S.P j)) r)
      (parityPrefix (fun j => partitionPolarity (S.P j)) s) := by
  refine parityPrefix_comm_left r fun j _ => ?_
  refine (parityPrefix_comm_left s fun i _ => ?_).symm
  by_cases hji : j = i
  · subst hji; exact Commute.refl _
  · exact (S.comm_polarity_polarity hji).symm

private lemma parityPrefix_sq (S : MetaCognitiveTower E) (k : ℕ) :
    parityPrefix (fun j => partitionPolarity (S.P j)) k *
      parityPrefix (fun j => partitionPolarity (S.P j)) k = 1 := by
  induction k with
  | zero => simp [parityPrefix]
  | succ k ih =>
    have hcomm : Commute (parityPrefix (fun j => partitionPolarity (S.P j)) k)
        (partitionPolarity (S.P k)) :=
      parityPrefix_comm_left k fun j hj => S.comm_polarity_polarity (Nat.ne_of_lt hj)
    have hΓk : partitionPolarity (S.P k) * partitionPolarity (S.P k) = 1 :=
      (prop1_orthogonality_and_polarity_involution (S.idem_P k)).2.2.2.2.1
    change (parityPrefix (fun j => partitionPolarity (S.P j)) k * partitionPolarity (S.P k)) *
        (parityPrefix (fun j => partitionPolarity (S.P j)) k * partitionPolarity (S.P k)) = 1
    calc
      parityPrefix (fun j => partitionPolarity (S.P j)) k * partitionPolarity (S.P k) *
          (parityPrefix (fun j => partitionPolarity (S.P j)) k * partitionPolarity (S.P k)) =
          parityPrefix (fun j => partitionPolarity (S.P j)) k *
            (partitionPolarity (S.P k) *
              parityPrefix (fun j => partitionPolarity (S.P j)) k) *
            partitionPolarity (S.P k) := by noncomm_ring
      _ = parityPrefix (fun j => partitionPolarity (S.P j)) k *
            (parityPrefix (fun j => partitionPolarity (S.P j)) k *
              partitionPolarity (S.P k)) *
            partitionPolarity (S.P k) := by rw [hcomm.eq]
      _ = (parityPrefix (fun j => partitionPolarity (S.P j)) k *
              parityPrefix (fun j => partitionPolarity (S.P j)) k) *
            (partitionPolarity (S.P k) * partitionPolarity (S.P k)) := by noncomm_ring
      _ = 1 * 1 := by rw [ih, hΓk]
      _ = 1 := mul_one 1

private lemma scaledBridge_mul_parityPrefix_add (S : MetaCognitiveTower E)
    (r d : ℕ) :
    scaledBridge (S.P r) (S.Ω r) *
        parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) =
      -(parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) *
        scaledBridge (S.P r) (S.Ω r)) := by
  induction d with
  | zero =>
    have hcomm : Commute (parityPrefix (fun j => partitionPolarity (S.P j)) r)
        (scaledBridge (S.P r) (S.Ω r)) :=
      parityPrefix_comm_left r fun j hj => S.comm_polarity_bridge (Nat.ne_of_lt hj)
    have hantiF :=
      (prop3_integrative_bridge_gravity_and_tension (S.idem_P r)
        (S.noncomm_stage r)).2.2.2.1
    have hantiB : scaledBridge (S.P r) (S.Ω r) * partitionPolarity (S.P r) =
        -(partitionPolarity (S.P r) * scaledBridge (S.P r) (S.Ω r)) := by
      dsimp [scaledBridge]
      have heq : partitionPolarity (S.P r) * (2 * integrativeBridge (S.P r) (S.Ω r)) +
          (2 * integrativeBridge (S.P r) (S.Ω r)) * partitionPolarity (S.P r) = 0 := by
        calc
          partitionPolarity (S.P r) * (2 * integrativeBridge (S.P r) (S.Ω r)) +
              (2 * integrativeBridge (S.P r) (S.Ω r)) * partitionPolarity (S.P r) =
              2 * (partitionPolarity (S.P r) * integrativeBridge (S.P r) (S.Ω r) +
                integrativeBridge (S.P r) (S.Ω r) * partitionPolarity (S.P r)) := by noncomm_ring
          _ = 2 * 0 := by rw [hantiF]
          _ = 0 := mul_zero 2
      exact eq_neg_of_add_eq_zero_right heq
    change scaledBridge (S.P r) (S.Ω r) *
        (parityPrefix (fun j => partitionPolarity (S.P j)) r * partitionPolarity (S.P r)) =
      -(parityPrefix (fun j => partitionPolarity (S.P j)) r * partitionPolarity (S.P r) *
        scaledBridge (S.P r) (S.Ω r))
    calc
      scaledBridge (S.P r) (S.Ω r) *
          (parityPrefix (fun j => partitionPolarity (S.P j)) r *
            partitionPolarity (S.P r)) =
          (scaledBridge (S.P r) (S.Ω r) *
            parityPrefix (fun j => partitionPolarity (S.P j)) r) *
            partitionPolarity (S.P r) := by noncomm_ring
      _ = (parityPrefix (fun j => partitionPolarity (S.P j)) r *
            scaledBridge (S.P r) (S.Ω r)) * partitionPolarity (S.P r) := by
            rw [hcomm.symm.eq]
      _ = parityPrefix (fun j => partitionPolarity (S.P j)) r *
            (scaledBridge (S.P r) (S.Ω r) * partitionPolarity (S.P r)) := by noncomm_ring
      _ = parityPrefix (fun j => partitionPolarity (S.P j)) r *
            (-(partitionPolarity (S.P r) * scaledBridge (S.P r) (S.Ω r))) := by rw [hantiB]
      _ = -(parityPrefix (fun j => partitionPolarity (S.P j)) r *
            partitionPolarity (S.P r) * scaledBridge (S.P r) (S.Ω r)) := by noncomm_ring
  | succ d ih =>
    have hne : r + 1 + d ≠ r := by omega
    have hcomm : Commute (scaledBridge (S.P r) (S.Ω r))
        (partitionPolarity (S.P (r + 1 + d))) :=
      (S.comm_polarity_bridge hne).symm
    rw [show r + 1 + (d + 1) = (r + 1 + d) + 1 by omega]
    change scaledBridge (S.P r) (S.Ω r) *
        (parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) *
          partitionPolarity (S.P (r + 1 + d))) =
      -(parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) *
        partitionPolarity (S.P (r + 1 + d)) * scaledBridge (S.P r) (S.Ω r))
    calc
      scaledBridge (S.P r) (S.Ω r) *
          (parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) *
            partitionPolarity (S.P (r + 1 + d))) =
          (scaledBridge (S.P r) (S.Ω r) *
            parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d)) *
            partitionPolarity (S.P (r + 1 + d)) := by noncomm_ring
      _ = -(parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) *
            scaledBridge (S.P r) (S.Ω r)) * partitionPolarity (S.P (r + 1 + d)) := by rw [ih]
      _ = -(parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) *
            (scaledBridge (S.P r) (S.Ω r) *
              partitionPolarity (S.P (r + 1 + d)))) := by noncomm_ring
      _ = -(parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) *
            (partitionPolarity (S.P (r + 1 + d)) *
              scaledBridge (S.P r) (S.Ω r))) := by rw [hcomm.eq]
      _ = -(parityPrefix (fun j => partitionPolarity (S.P j)) (r + 1 + d) *
            partitionPolarity (S.P (r + 1 + d)) *
            scaledBridge (S.P r) (S.Ω r)) := by noncomm_ring

private lemma sum_sq_eq_of_anticomm (f : ℕ → E)
    (hanti : ∀ {i j}, i ≠ j → f i * f j + f j * f i = 0) (s : Finset ℕ) :
    s.sum f * s.sum f = s.sum (fun k => f k * f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hcross : f a * t.sum f + t.sum f * f a = 0 := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun x hx => ?_
      have hne : a ≠ x := fun h => ha (h ▸ hx)
      exact hanti hne
    calc
      (f a + t.sum f) * (f a + t.sum f) =
          f a * f a + (f a * t.sum f + t.sum f * f a) + t.sum f * t.sum f := by noncomm_ring
      _ = f a * f a + 0 + t.sum (fun k => f k * f k) := by rw [hcross, ih]
      _ = f a * f a + t.sum (fun k => f k * f k) := by rw [add_zero]

/-- **`Prop.6` (Parity-Soldered Meta-Cognitive Coherence — Stratum 5)**:
Under `Ax.4`, for all stages `k` and distinct `r ≠ s`:
1. `𝒜_k := T_k - T_k² = Y_k X_k`;
2. `\widehat{B}_k² = B_k² = 4 M_k`;
3. `\widehat{B}_r \widehat{B}_s + \widehat{B}_s \widehat{B}_r = 0`;
4. `D_N² = ∑_{k=0}^N B_k² = ∑_{k=0}^N 4 M_k`;
5. Explicit cross-level confabulation residual for naive ungraded addition `(B_r + B_s)² - (B_r² + B_s²) = 2 B_r B_s`. -/
theorem prop6_parity_soldered_meta_cognitive_coherence (S : MetaCognitiveTower E) :
    (∀ k, socraticAporia (S.P k) (S.Ω k) =
      inwardIntrusion (S.P k) (S.Ω k) * outwardProjection (S.P k) (S.Ω k)) ∧
    (∀ k, solderedBridge S k * solderedBridge S k =
        scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k) ∧
      scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k) =
        4 * substantiveGravity (S.P k) (S.Ω k)) ∧
    (∀ {r s}, r ≠ s →
      solderedBridge S r * solderedBridge S s + solderedBridge S s * solderedBridge S r = 0) ∧
    (∀ N, metaDirac S N * metaDirac S N =
        (Finset.range (N + 1)).sum
          (fun k => scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k)) ∧
      (Finset.range (N + 1)).sum
          (fun k => scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k)) =
        (Finset.range (N + 1)).sum
          (fun k => 4 * substantiveGravity (S.P k) (S.Ω k))) ∧
    (∀ {r s}, r ≠ s →
      (scaledBridge (S.P r) (S.Ω r) + scaledBridge (S.P s) (S.Ω s)) *
          (scaledBridge (S.P r) (S.Ω r) + scaledBridge (S.P s) (S.Ω s)) -
        (scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P r) (S.Ω r) +
          scaledBridge (S.P s) (S.Ω s) * scaledBridge (S.P s) (S.Ω s)) =
        2 * (scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P s) (S.Ω s))) := by
  have hap : ∀ k, socraticAporia (S.P k) (S.Ω k) =
      inwardIntrusion (S.P k) (S.Ω k) * outwardProjection (S.P k) (S.Ω k) :=
    fun k => (prop4_exact_socratic_aporia_and_intertwining (S.idem_P k) (S.idem_Ω k)).1
  have hsq : ∀ k, solderedBridge S k * solderedBridge S k =
      scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k) ∧
      scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k) =
        4 * substantiveGravity (S.P k) (S.Ω k) := by
    intro k
    have hcomm : Commute (parityPrefix (fun j => partitionPolarity (S.P j)) k)
        (scaledBridge (S.P k) (S.Ω k)) :=
      parityPrefix_comm_left k fun j hj => S.comm_polarity_bridge (Nat.ne_of_lt hj)
    have hpisq := parityPrefix_sq S k
    have h1 : solderedBridge S k * solderedBridge S k =
        scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k) := by
      dsimp [solderedBridge]
      calc
        parityPrefix (fun j => partitionPolarity (S.P j)) k * scaledBridge (S.P k) (S.Ω k) *
            (parityPrefix (fun j => partitionPolarity (S.P j)) k *
              scaledBridge (S.P k) (S.Ω k)) =
            parityPrefix (fun j => partitionPolarity (S.P j)) k *
              (scaledBridge (S.P k) (S.Ω k) *
                parityPrefix (fun j => partitionPolarity (S.P j)) k) *
              scaledBridge (S.P k) (S.Ω k) := by noncomm_ring
        _ = parityPrefix (fun j => partitionPolarity (S.P j)) k *
              (parityPrefix (fun j => partitionPolarity (S.P j)) k *
                scaledBridge (S.P k) (S.Ω k)) *
              scaledBridge (S.P k) (S.Ω k) := by rw [hcomm.symm.eq]
        _ = (parityPrefix (fun j => partitionPolarity (S.P j)) k *
                parityPrefix (fun j => partitionPolarity (S.P j)) k) *
              (scaledBridge (S.P k) (S.Ω k) *
                scaledBridge (S.P k) (S.Ω k)) := by noncomm_ring
        _ = scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k) := by
            rw [hpisq, one_mul]
    have h2 : scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k) =
        4 * substantiveGravity (S.P k) (S.Ω k) :=
      (prop5_dogmatic_truncation_defect (S.idem_P k) (S.idem_Ω k)).2.2
    exact ⟨h1, h2⟩
  have hanti_lt : ∀ {r s}, r < s →
      solderedBridge S r * solderedBridge S s +
        solderedBridge S s * solderedBridge S r = 0 := by
    intro r s hrs
    have hπ := parityPrefix_comm_pair S r s
    have hB_r_s : Commute (scaledBridge (S.P r) (S.Ω r)) (scaledBridge (S.P s) (S.Ω s)) :=
      S.comm_bridge_bridge (Nat.ne_of_lt hrs)
    have hB_s_πr : Commute (scaledBridge (S.P s) (S.Ω s))
        (parityPrefix (fun j => partitionPolarity (S.P j)) r) :=
      (parityPrefix_comm_left r fun j hj =>
        S.comm_polarity_bridge (by omega)).symm
    have hflip : scaledBridge (S.P r) (S.Ω r) *
          parityPrefix (fun j => partitionPolarity (S.P j)) s =
        -(parityPrefix (fun j => partitionPolarity (S.P j)) s *
          scaledBridge (S.P r) (S.Ω r)) := by
      rw [show s = r + 1 + (s - (r + 1)) by omega]
      exact scaledBridge_mul_parityPrefix_add S r (s - (r + 1))
    have hlhs : solderedBridge S r * solderedBridge S s =
        -(parityPrefix (fun j => partitionPolarity (S.P j)) r *
            parityPrefix (fun j => partitionPolarity (S.P j)) s *
            (scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P s) (S.Ω s))) := by
      dsimp [solderedBridge]
      calc
        parityPrefix (fun j => partitionPolarity (S.P j)) r * scaledBridge (S.P r) (S.Ω r) *
            (parityPrefix (fun j => partitionPolarity (S.P j)) s *
              scaledBridge (S.P s) (S.Ω s)) =
            parityPrefix (fun j => partitionPolarity (S.P j)) r *
              (scaledBridge (S.P r) (S.Ω r) *
                parityPrefix (fun j => partitionPolarity (S.P j)) s) *
              scaledBridge (S.P s) (S.Ω s) := by noncomm_ring
        _ = parityPrefix (fun j => partitionPolarity (S.P j)) r *
              (-(parityPrefix (fun j => partitionPolarity (S.P j)) s *
                scaledBridge (S.P r) (S.Ω r))) *
              scaledBridge (S.P s) (S.Ω s) := by rw [hflip]
        _ = -(parityPrefix (fun j => partitionPolarity (S.P j)) r *
              parityPrefix (fun j => partitionPolarity (S.P j)) s *
              (scaledBridge (S.P r) (S.Ω r) *
                scaledBridge (S.P s) (S.Ω s))) := by noncomm_ring
    have hrhs : solderedBridge S s * solderedBridge S r =
        parityPrefix (fun j => partitionPolarity (S.P j)) r *
          parityPrefix (fun j => partitionPolarity (S.P j)) s *
          (scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P s) (S.Ω s)) := by
      dsimp [solderedBridge]
      calc
        parityPrefix (fun j => partitionPolarity (S.P j)) s * scaledBridge (S.P s) (S.Ω s) *
            (parityPrefix (fun j => partitionPolarity (S.P j)) r *
              scaledBridge (S.P r) (S.Ω r)) =
            parityPrefix (fun j => partitionPolarity (S.P j)) s *
              (scaledBridge (S.P s) (S.Ω s) *
                parityPrefix (fun j => partitionPolarity (S.P j)) r) *
              scaledBridge (S.P r) (S.Ω r) := by noncomm_ring
        _ = parityPrefix (fun j => partitionPolarity (S.P j)) s *
              (parityPrefix (fun j => partitionPolarity (S.P j)) r *
                scaledBridge (S.P s) (S.Ω s)) *
              scaledBridge (S.P r) (S.Ω r) := by rw [hB_s_πr.eq]
        _ = (parityPrefix (fun j => partitionPolarity (S.P j)) s *
                parityPrefix (fun j => partitionPolarity (S.P j)) r) *
              (scaledBridge (S.P s) (S.Ω s) *
                scaledBridge (S.P r) (S.Ω r)) := by noncomm_ring
        _ = (parityPrefix (fun j => partitionPolarity (S.P j)) r *
                parityPrefix (fun j => partitionPolarity (S.P j)) s) *
              (scaledBridge (S.P r) (S.Ω r) *
                scaledBridge (S.P s) (S.Ω s)) := by rw [hπ.symm.eq, hB_r_s.symm.eq]
    rw [hlhs, hrhs, neg_add_cancel]
  have hanti : ∀ {r s}, r ≠ s →
      solderedBridge S r * solderedBridge S s +
        solderedBridge S s * solderedBridge S r = 0 := by
    intro r s hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hanti_lt hlt
    · rw [add_comm]
      exact hanti_lt hgt
  have hdirac : ∀ N, metaDirac S N * metaDirac S N =
      (Finset.range (N + 1)).sum
        (fun k => scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k)) ∧
      (Finset.range (N + 1)).sum
          (fun k => scaledBridge (S.P k) (S.Ω k) * scaledBridge (S.P k) (S.Ω k)) =
        (Finset.range (N + 1)).sum
          (fun k => 4 * substantiveGravity (S.P k) (S.Ω k)) := by
    intro N
    constructor
    · dsimp [metaDirac]
      rw [sum_sq_eq_of_anticomm (solderedBridge S) hanti]
      refine Finset.sum_congr rfl fun k _ => (hsq k).1
    · refine Finset.sum_congr rfl fun k _ => (hsq k).2
  have hconf : ∀ {r s}, r ≠ s →
      (scaledBridge (S.P r) (S.Ω r) + scaledBridge (S.P s) (S.Ω s)) *
          (scaledBridge (S.P r) (S.Ω r) + scaledBridge (S.P s) (S.Ω s)) -
        (scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P r) (S.Ω r) +
          scaledBridge (S.P s) (S.Ω s) * scaledBridge (S.P s) (S.Ω s)) =
        2 * (scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P s) (S.Ω s)) := by
    intro r s hne
    have hcomm := (S.comm_bridge_bridge hne).eq
    calc
      (scaledBridge (S.P r) (S.Ω r) + scaledBridge (S.P s) (S.Ω s)) *
          (scaledBridge (S.P r) (S.Ω r) + scaledBridge (S.P s) (S.Ω s)) -
        (scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P r) (S.Ω r) +
          scaledBridge (S.P s) (S.Ω s) * scaledBridge (S.P s) (S.Ω s)) =
          scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P s) (S.Ω s) +
            scaledBridge (S.P s) (S.Ω s) * scaledBridge (S.P r) (S.Ω r) := by noncomm_ring
      _ = scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P s) (S.Ω s) +
            scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P s) (S.Ω s) := by rw [← hcomm]
      _ = 2 * (scaledBridge (S.P r) (S.Ω r) * scaledBridge (S.P s) (S.Ω s)) := by
          noncomm_ring
  exact ⟨hap, hsq, hanti, hdirac, hconf⟩

/-! ## Section 5: Master Structural Synthesis `Thm. Ω` -/

/-- Undivided reciprocity involution `J_Ω := 2Ω - 1`. -/
def reciprocityInvolution (Ω : E) : E :=
  2 * Ω - 1

/-- **`Thm. Ω` (Indefinite Reciprocal Totality — Stratum 6)**:
For `P² = P`, `Ω² = Ω`, `[P, Ω] ≠ 0`, and `2`-torsion-freeness `(∀ z, 2 * z = 0 → z = 0)`:
1. Coagulation decomposition: `Σ₀ + B = J_Ω`;
2. Exact involutive completeness: `J_Ω² = 1`;
3. Irreducibility to egoic partitioning: `[P, J_Ω] = 2[P, Ω]`, `[P, J_Ω] ≠ 0`, and `J_Ω ≠ Γ`;
4. Bijective preservation of all four directional sectors inside `J_Ω`. -/
theorem thm_omega_indefinite_reciprocal_totality
    {P Ω : E} (hP : P * P = P) (hΩ : Ω * Ω = Ω)
    (hnc : PeirceSpine.comm P Ω ≠ 0) (h2 : ∀ z : E, (2 : E) * z = 0 → z = 0) :
    severedDogma P Ω + scaledBridge P Ω = reciprocityInvolution Ω ∧
    reciprocityInvolution Ω * reciprocityInvolution Ω = 1 ∧
    (PeirceSpine.comm P (reciprocityInvolution Ω) = 2 * PeirceSpine.comm P Ω ∧
      PeirceSpine.comm P (reciprocityInvolution Ω) ≠ 0 ∧
      reciprocityInvolution Ω ≠ partitionPolarity P) ∧
    (P * reciprocityInvolution Ω * P = 2 * consciousThesis P Ω - P ∧
      shadowComp P * reciprocityInvolution Ω * shadowComp P =
        2 * autonomousGround P Ω - shadowComp P ∧
      shadowComp P * reciprocityInvolution Ω * P = 2 * outwardProjection P Ω ∧
      P * reciprocityInvolution Ω * shadowComp P = 2 * inwardIntrusion P Ω) := by
  have hp2 := prop2_fourfold_decomposition_and_unilateral_nilpotency hP hnc
  have hp5 := prop5_dogmatic_truncation_defect hP hΩ
  have hcoag : severedDogma P Ω + scaledBridge P Ω = reciprocityInvolution Ω := by
    have h4 := hp2.1
    dsimp [reciprocityInvolution]
    calc
      severedDogma P Ω + scaledBridge P Ω =
          2 * (consciousThesis P Ω + outwardProjection P Ω +
            inwardIntrusion P Ω + autonomousGround P Ω) - 1 := by
          dsimp [severedDogma, scaledBridge, integrativeBridge, shadowComp]
          noncomm_ring
      _ = 2 * Ω - 1 := by rw [← h4]
  have hJsq : reciprocityInvolution Ω * reciprocityInvolution Ω = 1 := by
    calc
      reciprocityInvolution Ω * reciprocityInvolution Ω =
          (severedDogma P Ω + scaledBridge P Ω) *
            (severedDogma P Ω + scaledBridge P Ω) := by rw [hcoag]
      _ = severedDogma P Ω * severedDogma P Ω +
            (severedDogma P Ω * scaledBridge P Ω +
              scaledBridge P Ω * severedDogma P Ω) +
            scaledBridge P Ω * scaledBridge P Ω := by noncomm_ring
      _ = severedDogma P Ω * severedDogma P Ω + 0 +
            (1 - severedDogma P Ω * severedDogma P Ω) := by rw [hp5.1, ← hp5.2.1]
      _ = 1 := by noncomm_ring
  have hcommJ : PeirceSpine.comm P (reciprocityInvolution Ω) = 2 * PeirceSpine.comm P Ω := by
    dsimp [PeirceSpine.comm, reciprocityInvolution]
    noncomm_ring
  have hcommJ_ne : PeirceSpine.comm P (reciprocityInvolution Ω) ≠ 0 := by
    intro h0
    apply hnc
    apply h2
    rw [← hcommJ, h0]
  have hΓ_comm : PeirceSpine.comm P (partitionPolarity P) = 0 := by
    rw [partitionPolarity_eq_invS]
    dsimp [PeirceSpine.comm]
    peirce_nf hP
  have hJ_ne_Γ : reciprocityInvolution Ω ≠ partitionPolarity P := by
    intro heq
    apply hcommJ_ne
    rw [heq, hΓ_comm]
  have h11 : P * reciprocityInvolution Ω * P = 2 * consciousThesis P Ω - P := by
    dsimp [reciprocityInvolution, consciousThesis]
    simp only [two_mul]
    peirce_nf hP
  have h00 : shadowComp P * reciprocityInvolution Ω * shadowComp P =
      2 * autonomousGround P Ω - shadowComp P := by
    dsimp [reciprocityInvolution, autonomousGround, shadowComp]
    simp only [two_mul]
    peirce_nf hP
  have h01 : shadowComp P * reciprocityInvolution Ω * P = 2 * outwardProjection P Ω := by
    dsimp [reciprocityInvolution, outwardProjection, shadowComp, coneMinus]
    simp only [two_mul]
    peirce_nf hP
  have h10 : P * reciprocityInvolution Ω * shadowComp P = 2 * inwardIntrusion P Ω := by
    dsimp [reciprocityInvolution, inwardIntrusion, shadowComp, conePlus]
    simp only [two_mul]
    peirce_nf hP
  exact ⟨hcoag, hJsq, ⟨hcommJ, hcommJ_ne, hJ_ne_Γ⟩, ⟨h11, h00, h01, h10⟩⟩

end CoreAlgebra

/-! ## Section 6: Concrete Non-Vacuity Witnesses (`Ax.1`–`Ax.4` Over `ℤ`) -/

section ConcreteWitnesses

open Matrix

/-- Single-stage integer matrix cut `p₀ := !![1, 0; 0, 0]`. -/
def intCut0 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Single-stage non-commuting idempotent totality `ω₀ := !![2, 1; -2, -1]`. -/
def intOmega0 : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; -2, -1]

theorem intCut0_idem : intCut0 * intCut0 = intCut0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem intOmega0_idem : intOmega0 * intOmega0 = intOmega0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem intCut0_intOmega0_noncomm : PeirceSpine.comm intCut0 intOmega0 ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  revert h01
  decide

theorem intCut0_mul_intOmega0_ne : intCut0 * intOmega0 ≠ intOmega0 * intCut0 :=
  sub_ne_zero.mp intCut0_intOmega0_noncomm

theorem intMat2_two_torsion_free (z : Matrix (Fin 2) (Fin 2) ℤ)
    (hz : (2 : Matrix (Fin 2) (Fin 2) ℤ) * z = 0) : z = 0 := by
  ext i j
  rw [two_mul] at hz
  have hij := congrFun (congrFun hz i) j
  have h0 : ((0 : Matrix (Fin 2) (Fin 2) ℤ) i j) = (0 : ℤ) := rfl
  change z i j + z i j = (0 : Matrix (Fin 2) (Fin 2) ℤ) i j at hij
  rw [h0] at hij
  omega

/-- Concrete non-vacuous integer-matrix realization of `Thm. Ω` with strictly
nonzero aporia (`𝒜₀ = -2 · E₁₁ ≠ 0`). -/
theorem intMat2_thm_omega_witness :
    socraticAporia intCut0 intOmega0 ≠ 0 ∧
    groundAporia intCut0 intOmega0 ≠ 0 ∧
    substantiveGravity intCut0 intOmega0 ≠ 0 ∧
    severedDogma intCut0 intOmega0 + scaledBridge intCut0 intOmega0 =
      reciprocityInvolution intOmega0 ∧
    reciprocityInvolution intOmega0 * reciprocityInvolution intOmega0 = 1 ∧
    PeirceSpine.comm intCut0 (reciprocityInvolution intOmega0) ≠ 0 ∧
    reciprocityInvolution intOmega0 ≠ partitionPolarity intCut0 := by
  have hthm := thm_omega_indefinite_reciprocal_totality
    intCut0_idem intOmega0_idem intCut0_intOmega0_noncomm intMat2_two_torsion_free
  refine ⟨?_, ?_, ?_, hthm.1, hthm.2.1, hthm.2.2.1.2.1, hthm.2.2.1.2.2⟩
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    revert h00
    decide
  · intro h
    have h11 := congrFun (congrFun h 1) 1
    revert h11
    decide
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    revert h00
    decide

/-- Canonical infinite-stage `Ax.4` model in `ℕ → Matrix (Fin 2) (Fin 2) ℤ`,
embedding `(intCut0, intOmega0)` on coordinate `k` and identity `1` elsewhere. -/
def intStageTower : MetaCognitiveTower (ℕ → Matrix (Fin 2) (Fin 2) ℤ) where
  P k i := if i = k then intCut0 else 1
  Ω k i := if i = k then intOmega0 else 1
  idem_P k := by
    funext i
    change (if i = k then intCut0 else 1) * (if i = k then intCut0 else 1) =
      if i = k then intCut0 else 1
    split_ifs <;> simp [intCut0_idem]
  idem_Ω k := by
    funext i
    change (if i = k then intOmega0 else 1) * (if i = k then intOmega0 else 1) =
      if i = k then intOmega0 else 1
    split_ifs <;> simp [intOmega0_idem]
  noncomm_stage k h0 := by
    have hk := congrFun h0 k
    apply intCut0_intOmega0_noncomm
    simpa [PeirceSpine.comm, Pi.mul_apply, Pi.sub_apply] using hk
  comm_polarity_polarity {j k} hjk := by
    funext i
    change partitionPolarity (if i = j then intCut0 else 1) *
        partitionPolarity (if i = k then intCut0 else 1) =
      partitionPolarity (if i = k then intCut0 else 1) *
        partitionPolarity (if i = j then intCut0 else 1)
    by_cases hij : i = j
    · subst hij
      simp [hjk, partitionPolarity, shadowComp]
    · by_cases hik : i = k
      · subst hik
        simp [hjk.symm, partitionPolarity, shadowComp]
      · simp [hij, hik, partitionPolarity, shadowComp]
  comm_polarity_bridge {j k} hjk := by
    funext i
    change partitionPolarity (if i = j then intCut0 else 1) *
        scaledBridge (if i = k then intCut0 else 1) (if i = k then intOmega0 else 1) =
      scaledBridge (if i = k then intCut0 else 1) (if i = k then intOmega0 else 1) *
        partitionPolarity (if i = j then intCut0 else 1)
    by_cases hij : i = j
    · subst hij
      simp [hjk, scaledBridge, integrativeBridge, outwardProjection,
        inwardIntrusion, coneMinus, conePlus]
    · by_cases hik : i = k
      · subst hik
        simp [hjk.symm, partitionPolarity, shadowComp]
      · simp [hij, partitionPolarity, shadowComp]
  comm_bridge_bridge {j k} hjk := by
    funext i
    change scaledBridge (if i = j then intCut0 else 1) (if i = j then intOmega0 else 1) *
        scaledBridge (if i = k then intCut0 else 1) (if i = k then intOmega0 else 1) =
      scaledBridge (if i = k then intCut0 else 1) (if i = k then intOmega0 else 1) *
        scaledBridge (if i = j then intCut0 else 1) (if i = j then intOmega0 else 1)
    by_cases hij : i = j
    · subst hij
      simp [hjk, scaledBridge, integrativeBridge, outwardProjection,
        inwardIntrusion, coneMinus, conePlus]
    · simp [hij, scaledBridge, integrativeBridge, outwardProjection,
        inwardIntrusion, coneMinus, conePlus]

theorem intStageTower_nonvanishing (k N : ℕ) :
    socraticAporia (intStageTower.P k) (intStageTower.Ω k) ≠ 0 ∧
    metaDirac intStageTower N * metaDirac intStageTower N ≠ 0 := by
  have hco := prop6_parity_soldered_meta_cognitive_coherence intStageTower
  constructor
  · intro h0
    have hk := congrFun h0 k
    have hap : socraticAporia intCut0 intOmega0 = 0 := by
      simpa [intStageTower, socraticAporia, consciousThesis, peirce11] using hk
    exact intMat2_thm_omega_witness.1 hap
  · intro h0
    have hdir := (hco.2.2.2.1 N).1.trans ((hco.2.2.2.1 N).2)
    rw [h0] at hdir
    have hN := congrFun hdir.symm N
    simp only [Pi.zero_apply] at hN
    have hsum : (Finset.range (N + 1)).sum
        (fun j => 4 * substantiveGravity (intStageTower.P j) (intStageTower.Ω j)) N =
        4 * substantiveGravity intCut0 intOmega0 := by
      have hsingle : ∀ j ∈ Finset.range (N + 1),
          (4 * substantiveGravity (intStageTower.P j) (intStageTower.Ω j)) N =
            if j = N then 4 * substantiveGravity intCut0 intOmega0 else 0 := by
        intro j _
        by_cases hjN : j = N
        · subst hjN
          simp [intStageTower, substantiveGravity, outwardProjection, inwardIntrusion,
            coneMinus, conePlus]
        · have hNj : N ≠ j := Ne.symm hjN
          simp [hjN, hNj, intStageTower, substantiveGravity, outwardProjection,
            inwardIntrusion, coneMinus, conePlus]
      have hfin : ((Finset.range (N + 1)).sum
          (fun j => 4 * substantiveGravity (intStageTower.P j) (intStageTower.Ω j))) N =
          (Finset.range (N + 1)).sum
            (fun j => (4 * substantiveGravity (intStageTower.P j) (intStageTower.Ω j)) N) := by
        simp [Finset.sum_apply]
      rw [hfin, Finset.sum_congr rfl hsingle]
      simp
    rw [hsum] at hN
    have h00 := congrFun (congrFun hN 0) 0
    revert h00
    decide

/-- Two-site matrix witness separating naive ungraded addition `B₀ + B₁`
(nonzero confabulation) from parity-soldered addition `B₀ + Γ₀ B₁` (`0` cross term). -/
theorem two_site_ungraded_confabulation_witness :
    let t : Matrix (Fin 2) (Fin 2) ℤ := !![2, 0; 0, 2]
    let B₀ : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ) := !![0, t; t, 0]
    let Γ₀ : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ) := !![1, 0; 0, -1]
    let B₁ : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ) :=
      !![scaledBridge intCut0 intOmega0, 0; 0, scaledBridge intCut0 intOmega0]
    (B₀ + B₁) * (B₀ + B₁) ≠ B₀ * B₀ + B₁ * B₁ ∧
    (B₀ + Γ₀ * B₁) * (B₀ + Γ₀ * B₁) = B₀ * B₀ + B₁ * B₁ := by
  intro t B₀ Γ₀ B₁
  have hB1 : B₁ * B₁ = (Γ₀ * B₁) * (Γ₀ * B₁) := by
    ext i j a b
    fin_cases i <;> fin_cases j <;>
      simp [B₁, Γ₀, Matrix.mul_apply, Fin.sum_univ_two]
  have hcomm_t : t * scaledBridge intCut0 intOmega0 =
      scaledBridge intCut0 intOmega0 * t := by
    ext a b
    fin_cases a <;> fin_cases b <;> decide
  have hanti : B₀ * (Γ₀ * B₁) + (Γ₀ * B₁) * B₀ = 0 := by
    ext i j a b
    fin_cases i <;> fin_cases j
    · simp [B₀, Γ₀, B₁]
    · have h01 := congrFun (congrFun hcomm_t a) b
      simp [B₀, Γ₀, B₁, Matrix.mul_apply, Fin.sum_univ_two, h01]
    · have h10 := congrFun (congrFun hcomm_t a) b
      simp [B₀, Γ₀, B₁, Matrix.mul_apply, Fin.sum_univ_two, h10]
    · simp [B₀, Γ₀, B₁]
  constructor
  · intro heq
    have hentry := congrFun (congrFun (congrFun (congrFun heq 0) 1) 0) 1
    revert hentry
    decide
  · calc
      (B₀ + Γ₀ * B₁) * (B₀ + Γ₀ * B₁) =
          B₀ * B₀ + (B₀ * (Γ₀ * B₁) + (Γ₀ * B₁) * B₀) +
            (Γ₀ * B₁) * (Γ₀ * B₁) := by noncomm_ring
      _ = B₀ * B₀ + 0 + B₁ * B₁ := by rw [hanti, ← hB1]
      _ = B₀ * B₀ + B₁ * B₁ := by abel

/-- Closed non-commutativity witness on the two-site matrix carrier
`Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ)`. -/
theorem twoSite_noncomm_exists :
    ∃ A B : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℤ), A * B ≠ B * A := by
  refine ⟨!![1, 0; 0, -1], !![0, 1; 1, 0], ?_⟩
  intro h
  have h01 := congrFun (congrFun (congrFun (congrFun h 0) 1) 0) 0
  revert h01
  decide

end ConcreteWitnesses

/-! ## Section 7: Exact 16-Node / 7-Stratum Acyclic Causal Poset `(𝒫, ≺)` (`Phase V.1`) -/

section CausalPoset

/-- The 16 extracted nodes across Strata `0`–`6` of the causal poset `(𝒫, ≺)`. -/
inductive AporiaCoagulaNode
  | N0_Omega
  | N1a_ConsciousThesis_P
  | N1b_ShadowComplement_Q
  | N1c_PartitioningPolarity_Gamma
  | N2a_SelfConsistency_T
  | N2b_OutwardProjection_X
  | N2c_InwardIntrusion_Y
  | N2d_AutonomousGround_G
  | N3a_RoundTripHolonomies
  | N3b_IntegrativeBridge_F
  | N3c_SubstantiveGravity_M
  | N3d_DirectionalTension_K
  | N4a_SocraticAporia_A0
  | N4b_SeveredDogma_Sigma0
  | N5_ParitySolderedTower
  | N6_ReciprocalTotality_JOmega
  deriving DecidableEq, Repr, Inhabited

/-- Strict lexicographic rank pair `(s, σ)` embedding `(𝒫, ≺)` into `(ℕ × ℕ, <ₗ)`. -/
def stratumPair : AporiaCoagulaNode → ℕ × ℕ
  | .N0_Omega => (0, 0)
  | .N1a_ConsciousThesis_P => (1, 0)
  | .N1b_ShadowComplement_Q => (1, 1)
  | .N1c_PartitioningPolarity_Gamma => (1, 2)
  | .N2a_SelfConsistency_T => (2, 0)
  | .N2b_OutwardProjection_X => (2, 0)
  | .N2c_InwardIntrusion_Y => (2, 0)
  | .N2d_AutonomousGround_G => (2, 0)
  | .N3a_RoundTripHolonomies => (3, 0)
  | .N3b_IntegrativeBridge_F => (3, 0)
  | .N3c_SubstantiveGravity_M => (3, 1)
  | .N3d_DirectionalTension_K => (3, 2)
  | .N4a_SocraticAporia_A0 => (4, 0)
  | .N4b_SeveredDogma_Sigma0 => (4, 0)
  | .N5_ParitySolderedTower => (5, 0)
  | .N6_ReciprocalTotality_JOmega => (6, 0)

/-- Order-preserving natural rank `10 * s + σ`. -/
def lexRankNat (n : AporiaCoagulaNode) : ℕ :=
  10 * (stratumPair n).1 + (stratumPair n).2

/-- Exact covering relations `u ≺_cov v` across Strata `0`–`6` in `Phase V.1`. -/
inductive AporiaCover : AporiaCoagulaNode → AporiaCoagulaNode → Prop where
  | c0_1a : AporiaCover .N0_Omega .N1a_ConsciousThesis_P
  | c1a_1b : AporiaCover .N1a_ConsciousThesis_P .N1b_ShadowComplement_Q
  | c1a_1c : AporiaCover .N1a_ConsciousThesis_P .N1c_PartitioningPolarity_Gamma
  | c1b_1c : AporiaCover .N1b_ShadowComplement_Q .N1c_PartitioningPolarity_Gamma
  | c0_2a : AporiaCover .N0_Omega .N2a_SelfConsistency_T
  | c1a_2a : AporiaCover .N1a_ConsciousThesis_P .N2a_SelfConsistency_T
  | c0_2b : AporiaCover .N0_Omega .N2b_OutwardProjection_X
  | c1a_2b : AporiaCover .N1a_ConsciousThesis_P .N2b_OutwardProjection_X
  | c1b_2b : AporiaCover .N1b_ShadowComplement_Q .N2b_OutwardProjection_X
  | c0_2c : AporiaCover .N0_Omega .N2c_InwardIntrusion_Y
  | c1a_2c : AporiaCover .N1a_ConsciousThesis_P .N2c_InwardIntrusion_Y
  | c1b_2c : AporiaCover .N1b_ShadowComplement_Q .N2c_InwardIntrusion_Y
  | c0_2d : AporiaCover .N0_Omega .N2d_AutonomousGround_G
  | c1b_2d : AporiaCover .N1b_ShadowComplement_Q .N2d_AutonomousGround_G
  | c2b_3a : AporiaCover .N2b_OutwardProjection_X .N3a_RoundTripHolonomies
  | c2c_3a : AporiaCover .N2c_InwardIntrusion_Y .N3a_RoundTripHolonomies
  | c2b_3b : AporiaCover .N2b_OutwardProjection_X .N3b_IntegrativeBridge_F
  | c2c_3b : AporiaCover .N2c_InwardIntrusion_Y .N3b_IntegrativeBridge_F
  | c3a_3c : AporiaCover .N3a_RoundTripHolonomies .N3c_SubstantiveGravity_M
  | c3b_3c : AporiaCover .N3b_IntegrativeBridge_F .N3c_SubstantiveGravity_M
  | c3a_3d : AporiaCover .N3a_RoundTripHolonomies .N3d_DirectionalTension_K
  | c1c_3d : AporiaCover .N1c_PartitioningPolarity_Gamma .N3d_DirectionalTension_K
  | c3c_3d : AporiaCover .N3c_SubstantiveGravity_M .N3d_DirectionalTension_K
  | c2a_4a : AporiaCover .N2a_SelfConsistency_T .N4a_SocraticAporia_A0
  | c3a_4a : AporiaCover .N3a_RoundTripHolonomies .N4a_SocraticAporia_A0
  | c2a_4b : AporiaCover .N2a_SelfConsistency_T .N4b_SeveredDogma_Sigma0
  | c2d_4b : AporiaCover .N2d_AutonomousGround_G .N4b_SeveredDogma_Sigma0
  | c1a_4b : AporiaCover .N1a_ConsciousThesis_P .N4b_SeveredDogma_Sigma0
  | c1b_4b : AporiaCover .N1b_ShadowComplement_Q .N4b_SeveredDogma_Sigma0
  | c3c_4b : AporiaCover .N3c_SubstantiveGravity_M .N4b_SeveredDogma_Sigma0
  | c4a_5 : AporiaCover .N4a_SocraticAporia_A0 .N5_ParitySolderedTower
  | c1c_5 : AporiaCover .N1c_PartitioningPolarity_Gamma .N5_ParitySolderedTower
  | c3b_5 : AporiaCover .N3b_IntegrativeBridge_F .N5_ParitySolderedTower
  | c4b_6 : AporiaCover .N4b_SeveredDogma_Sigma0 .N6_ReciprocalTotality_JOmega
  | c3b_6 : AporiaCover .N3b_IntegrativeBridge_F .N6_ReciprocalTotality_JOmega
  | c5_6 : AporiaCover .N5_ParitySolderedTower .N6_ReciprocalTotality_JOmega

theorem aporiaCover_lexRank_strictMono {u v : AporiaCoagulaNode}
    (h : AporiaCover u v) : lexRankNat u < lexRankNat v := by
  cases h <;> decide

theorem aporiaCover_transGen_lexRank_strictMono {u v : AporiaCoagulaNode}
    (h : Relation.TransGen AporiaCover u v) : lexRankNat u < lexRankNat v := by
  induction h with
  | single huv => exact aporiaCover_lexRank_strictMono huv
  | tail _ hvw ih => exact Nat.lt_trans ih (aporiaCover_lexRank_strictMono hvw)

theorem aporiaCover_irreflexive (u : AporiaCoagulaNode) :
    ¬ Relation.TransGen AporiaCover u u := by
  intro h
  exact Nat.lt_irrefl (lexRankNat u) (aporiaCover_transGen_lexRank_strictMono h)

theorem aporiaCover_acyclic {u v : AporiaCoagulaNode}
    (h1 : Relation.TransGen AporiaCover u v) (h2 : Relation.TransGen AporiaCover v u) :
    False :=
  aporiaCover_irreflexive u (Relation.TransGen.trans h1 h2)

instance : PartialOrder AporiaCoagulaNode where
  le := Relation.ReflTransGen AporiaCover
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ h1 h2 := Relation.ReflTransGen.trans h1 h2
  le_antisymm u v huv hvu := by
    rcases (Relation.reflTransGen_iff_eq_or_transGen).mp huv with rfl | h1
    · rfl
    · rcases (Relation.reflTransGen_iff_eq_or_transGen).mp hvu with rfl | h2
      · rfl
      · exact (aporiaCover_acyclic h1 h2).elim

end CausalPoset

/-! ## Section 8: Bridges into the `{Leibniz, Derivation, Onsager}` Spine -/

section LeibnizDerivationOnsagerBridge

/-- Leibniz derivation laws connecting `peirceGradingDeriv P` to the fourfold anatomy
and integrative bridge `F` (`ad_P(Ω) = Y - X`, `ad_P²(Ω) = F`, `ad_P³(Ω) = ad_P(Ω)`). -/
theorem peirceGradingDeriv_omega_laws {E : Type*} [Ring E]
    {P Ω : E} (hP : P * P = P) (U V : E) :
    peirceGradingDeriv P (U * V) =
      peirceGradingDeriv P U * V + U * peirceGradingDeriv P V ∧
    peirceGradingDeriv P Ω = inwardIntrusion P Ω - outwardProjection P Ω ∧
    peirceGradingDeriv P (peirceGradingDeriv P Ω) = integrativeBridge P Ω ∧
    peirceGradingDeriv P (peirceGradingDeriv P (peirceGradingDeriv P Ω)) =
      peirceGradingDeriv P Ω := by
  refine ⟨peirceGradingDeriv_leibniz P U V, ?_, ?_, ?_⟩
  · dsimp [peirceGradingDeriv, PeirceSpine.comm, inwardIntrusion, outwardProjection,
      conePlus, coneMinus]
    noncomm_ring
  · dsimp [peirceGradingDeriv, PeirceSpine.comm, integrativeBridge, outwardProjection,
      inwardIntrusion, coneMinus, conePlus]
    peirce_nf hP
  · dsimp [peirceGradingDeriv, PeirceSpine.comm]
    peirce_nf hP

/-- Grading parity of `Σ₀` (`Γ`-even) and `B` (`Γ`-odd) under `parityConj P`,
realizing the Onsager–Casimir parity decomposition of `J_Ω = Σ₀ + B`. -/
theorem parityConj_reciprocity_onsager_split {E : Type*} [Ring E]
    {P Ω : E} (hP : P * P = P) :
    parityConj P (severedDogma P Ω) = severedDogma P Ω ∧
    parityConj P (scaledBridge P Ω) = -scaledBridge P Ω ∧
    parityConj P (reciprocityInvolution Ω) =
      severedDogma P Ω - scaledBridge P Ω := by
  have heven : parityConj P (severedDogma P Ω) = severedDogma P Ω := by
    dsimp [parityConj, severedDogma, consciousThesis, autonomousGround, shadowComp]
    rw [show (2 : E) = (2 : ℤ) • (1 : E) by simp]
    peirce_nf hP
  have hodd : parityConj P (scaledBridge P Ω) = -scaledBridge P Ω := by
    dsimp [parityConj, scaledBridge, integrativeBridge, outwardProjection, inwardIntrusion]
    rw [show (2 : E) = (2 : ℤ) • (1 : E) by simp]
    peirce_nf hP
  have hcoag : severedDogma P Ω + scaledBridge P Ω = reciprocityInvolution Ω := by
    dsimp [severedDogma, scaledBridge, integrativeBridge, consciousThesis, autonomousGround,
      outwardProjection, inwardIntrusion, shadowComp, reciprocityInvolution,
      peirce11, peirce00, coneMinus, conePlus]
    noncomm_ring
  have hadd := (parityConj_involutive_ring_action hP (severedDogma P Ω) (scaledBridge P Ω)).2.2.1
  refine ⟨heven, hodd, ?_⟩
  rw [← hcoag, hadd, heven, hodd, sub_eq_add_neg]

/-- Concrete matrix `OnsagerCasimirSystem.TimeReversal` realized by Peirce cut
conjugation `X ↦ invS P * X * invS P` (`Γ X Γ`). -/
def peirceMatrixTimeReversal (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P * P = P) :
    InfoGeometry.Thermo.OnsagerClosure.OnsagerCasimirSystem.TimeReversal
      (Matrix (Fin n) (Fin n) ℝ) where
  op :=
    { toFun := fun X => parityConj P X
      map_add' := fun X Y =>
        (parityConj_involutive_ring_action hP X Y).2.2.1
      map_smul' := fun c X => by
        dsimp [parityConj]
        simp }
  involutive := fun X =>
    (parityConj_involutive_ring_action hP X 1).1

end LeibnizDerivationOnsagerBridge

end InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityAporiaPoset
