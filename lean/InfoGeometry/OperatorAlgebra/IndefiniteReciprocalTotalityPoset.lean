/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import InfoGeometry.Core.IdempotentGraphGrassmannian
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceDefectBridge

/-!
# Indefinite Reciprocal Totality & Solve et Coagula Epistemic Poset

Formalizes the 6-phase non-commutative `SOLVE -> COAGULA` compilation chain
(`PHASE 0` through `PHASE V`) over any unital associative ring `(E, +, *, 0, 1)`
(`Ax.1`), together with an acyclic causal poset `CoagulaNode` across Strata `0..6`
and a concrete non-vacuous matrix realization in `Matrix (Fin 2) (Fin 2) ℤ`:

* **Phase 0 & I (`Ax.2`–`Ax.3`, `Prop.1`, Strata `0..1`)**: Undivided idempotent act
  `Ω^2 = Ω`, selective cut `P^2 = P` with `[P, Ω] ≠ 0`, shadow complement
  `Q := 1 - P`, and boundary polarity involution `Γ := P - Q` (`Γ^2 = 1`).
* **Phase II (`Prop.2`, Stratum `2`)**: Exhaustive fourfold dissolution
  `Ω = T + X + Y + G` with `T = P Ω P`, `X = Q Ω P`, `Y = P Ω Q`, `G = Q Ω Q`,
  showing `[P, Ω] = Y - X` and unilateral nilpotency `X^2 = 0 = Y^2`.
* **Phase III (`Prop.3`, Stratum `3`)**: Transcendent function `(M, K, F)` with
  `F = X + Y`, `M = X Y + Y X = F^2`, and `K = Y X - X Y = Γ M`, proving oddness
  `Γ F + F Γ = 0` and round-trip holonomy separation `Y X = X Y ↔ M = 0`.
* **Phase IV (`Ax.4`, `Prop.4`–`Prop.6`, Strata `4..5`)**: Exact Socratic aporia
  `A_0 := T - T^2 = Y X` and `G - G^2 = X Y`, dogmatic truncation defect
  `1 - Σ_0^2 = B^2 = 4 M` (`Σ_0 = (2 T - P) + (2 G - Q)`, `B = 2 F`), and the
  parity-soldered meta-cognitive tower `D_N = ∑ k, B_hat k` satisfying
  `B_hat r * B_hat s + B_hat s * B_hat r = 0` (`r ≠ s`) and `D_N^2 = 4 ∑ k, M_k`.
* **Phase V (`Thm. Ω`, Stratum `6`)**: Acyclic cover poset `CoagulaNode` across
  Strata `0..6`, master synthesis `J_Ω := Σ_0 + B = 2 Ω - 1` (`J_Ω^2 = 1`,
  `J_Ω ≠ Γ`, recovering all four sectors), and explicit `M_2(ℤ)` witness.
-/

namespace InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset

open InfoGeometry.Core.IdempotentGraphGrassmannian (idempotencyDefect)
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.OperatorAlgebra.PeirceDefectBridge

/-! ### Non-Commutative `M_2(ℤ)` Model & T16 Witness -/

/-- Explicit T16 non-commutativity witness for `Matrix (Fin 2) (Fin 2) ℤ` (`Ax.1`). -/
theorem mat2Z_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℤ, A * B ≠ B * A := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
  let B : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; -2, -1]
  refine ⟨A, B, ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [A, B, Matrix.mul_apply, Fin.sum_univ_two] at h01

/-- Concrete conscious cut `P₀ ∈ M_2(ℤ)` realizing `Ax.3`. -/
def cutP0 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Concrete non-diagonal idempotent totality `Ω₀ ∈ M_2(ℤ)` realizing `Ax.2`. -/
def totalityOmega0 : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; -2, -1]

theorem cutP0_idem : cutP0 * cutP0 = cutP0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cutP0, Matrix.mul_apply, Fin.sum_univ_two]

theorem totalityOmega0_idem : totalityOmega0 * totalityOmega0 = totalityOmega0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [totalityOmega0, Matrix.mul_apply, Fin.sum_univ_two]

theorem cutP0_totalityOmega0_comm_ne_zero : PeirceSpine.comm cutP0 totalityOmega0 ≠ 0 := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  simp [PeirceSpine.comm, cutP0, totalityOmega0] at h01

/-! ### Phase I–III: Primordial Cut, Fourfold Anatomy & Transcendent Quartet -/

section RingOperators

variable {E : Type*} [Ring E]

/-- Repressed shadow complement `Q := 1 - P` (Stratum `1.1`). -/
def shadowQ (P : E) : E := 1 - P

/-- Partitioning polarity involution `Γ := P - Q = 2 P - 1` (Stratum `1.2`). -/
def polarityGamma (P : E) : E := P - shadowQ P

/-- Internal self-consistency sector `T := P Ω P` (`P -> P`, Stratum `2`). -/
def consciousThesis (P Ω : E) : E := P * Ω * P

/-- Outward projection `X := Q Ω P` (`P -> Q`, Stratum `2`). -/
def outwardProj (P Ω : E) : E := shadowQ P * Ω * P

/-- Inward shadow-intrusion `Y := P Ω Q` (`Q -> P`, Stratum `2`). -/
def inwardIntrusion (P Ω : E) : E := P * Ω * shadowQ P

/-- Autonomous unexamined ground `G := Q Ω Q` (`Q -> Q`, Stratum `2`). -/
def autonomousGround (P Ω : E) : E := shadowQ P * Ω * shadowQ P

/-- Integrative boundary-crossing bridge `F := X + Y` (Stratum `3.0`). -/
def integrativeBridge (P Ω : E) : E := outwardProj P Ω + inwardIntrusion P Ω

/-- Shared substantive gravity `M := X Y + Y X` (Stratum `3.1`). -/
def substantiveGravity (P Ω : E) : E :=
  outwardProj P Ω * inwardIntrusion P Ω + inwardIntrusion P Ω * outwardProj P Ω

/-- Directional tension `K := Y X - X Y` (Stratum `3.1`). -/
def directionalTension (P Ω : E) : E :=
  inwardIntrusion P Ω * outwardProj P Ω - outwardProj P Ω * inwardIntrusion P Ω

/-- Socratic elenctic aporia `A₀ := T - T^2` of the Conscious Thesis (Stratum `4`). -/
def socraticAporia (P Ω : E) : E :=
  consciousThesis P Ω - consciousThesis P Ω * consciousThesis P Ω

/-- Complementary aporia `G - G^2` of the Autonomous Ground (Stratum `4`). -/
def shadowAporia (P Ω : E) : E :=
  autonomousGround P Ω - autonomousGround P Ω * autonomousGround P Ω

/-- Severed block-diagonal dogmatic operator `Σ₀ := (2 T - P) + (2 G - Q)` (Stratum `4`). -/
def dogmaticTruncation (P Ω : E) : E :=
  (2 * consciousThesis P Ω - P) + (2 * autonomousGround P Ω - shadowQ P)

/-- Doubled integrative bridge `B := 2 F` (Stratum `4`–`5`). -/
def doubledBridge (P Ω : E) : E := 2 * integrativeBridge P Ω

/-- Undivided reciprocal totality involution `J_Ω := 2 Ω - 1` (Stratum `6`). -/
def reciprocalTotality (Ω : E) : E := 2 * Ω - 1

/-- Owner bridge: `polarityGamma P` coincides with `PeirceSpine.invS P`. -/
theorem polarityGamma_eq_invS (P : E) : polarityGamma P = invS P := rfl

/-- Owner bridge: the fourfold sectors match `PeirceSpine` (`X = coneMinus`, `Y = conePlus`). -/
theorem fourfold_eq_peirceSpine (P Ω : E) :
    consciousThesis P Ω = peirce11 P Ω ∧
    outwardProj P Ω = coneMinus P Ω ∧
    inwardIntrusion P Ω = conePlus P Ω ∧
    autonomousGround P Ω = peirce00 P Ω :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Owner bridge: `(F, M, K, A₀)` match `genPhi`, `genV`, `genSig`, and `-idempotencyDefect`. -/
theorem transcendent_eq_peirceSpine (P Ω : E) :
    integrativeBridge P Ω = genPhi P Ω Ω ∧
    substantiveGravity P Ω = genV P Ω Ω ∧
    directionalTension P Ω = genSig P Ω Ω ∧
    socraticAporia P Ω = -idempotencyDefect (peirce11 P Ω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold integrativeBridge genPhi outwardProj inwardIntrusion shadowQ conePlus coneMinus
    abel
  · unfold substantiveGravity genV anticomm outwardProj inwardIntrusion shadowQ
      conePlus coneMinus
    abel
  · unfold directionalTension genSig PeirceSpine.comm outwardProj inwardIntrusion shadowQ
      conePlus coneMinus
    rfl
  · unfold socraticAporia idempotencyDefect consciousThesis peirce11
    abel

/-- **`Prop.1` (Orthogonality & Polarity Involution — Stratum `1`)**:
From `P^2 = P`, the complement `Q = 1 - P` and polarity `Γ = P - Q` satisfy mutual
orthogonality, completeness, and the involution/grading laws. -/
theorem prop1_orthogonality_and_polarity_involution {P : E} (hP : P * P = P) :
    shadowQ P * shadowQ P = shadowQ P ∧
    P * shadowQ P = 0 ∧
    shadowQ P * P = 0 ∧
    P + shadowQ P = 1 ∧
    polarityGamma P * polarityGamma P = 1 ∧
    polarityGamma P * P = P ∧
    P * polarityGamma P = P ∧
    polarityGamma P * shadowQ P = -shadowQ P ∧
    shadowQ P * polarityGamma P = -shadowQ P ∧
    PeirceSpine.comm P (polarityGamma P) = 0 := by
  have hQ : shadowQ P * shadowQ P = shadowQ P := by
    unfold shadowQ
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  have hPQ : P * shadowQ P = 0 := by
    unfold shadowQ
    calc
      P * (1 - P) = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hQP : shadowQ P * P = 0 := by
    unfold shadowQ
    calc
      (1 - P) * P = P - P * P := by noncomm_ring
      _ = 0 := by rw [hP, sub_self]
  have hSum : P + shadowQ P = 1 := by
    unfold shadowQ; abel
  have hGG : polarityGamma P * polarityGamma P = 1 := by
    unfold polarityGamma
    calc
      (P - shadowQ P) * (P - shadowQ P)
          = P * P - P * shadowQ P - shadowQ P * P + shadowQ P * shadowQ P := by
            noncomm_ring
      _ = P - 0 - 0 + shadowQ P := by rw [hP, hPQ, hQP, hQ]
      _ = P + shadowQ P := by abel
      _ = 1 := hSum
  have hGP : polarityGamma P * P = P := by
    unfold polarityGamma
    calc
      (P - shadowQ P) * P = P * P - shadowQ P * P := by noncomm_ring
      _ = P - 0 := by rw [hP, hQP]
      _ = P := sub_zero P
  have hPG : P * polarityGamma P = P := by
    unfold polarityGamma
    calc
      P * (P - shadowQ P) = P * P - P * shadowQ P := by noncomm_ring
      _ = P - 0 := by rw [hP, hPQ]
      _ = P := sub_zero P
  have hGQ : polarityGamma P * shadowQ P = -shadowQ P := by
    unfold polarityGamma
    calc
      (P - shadowQ P) * shadowQ P
          = P * shadowQ P - shadowQ P * shadowQ P := by noncomm_ring
      _ = 0 - shadowQ P := by rw [hPQ, hQ]
      _ = -shadowQ P := zero_sub _
  have hQG : shadowQ P * polarityGamma P = -shadowQ P := by
    unfold polarityGamma
    calc
      shadowQ P * (P - shadowQ P)
          = shadowQ P * P - shadowQ P * shadowQ P := by noncomm_ring
      _ = 0 - shadowQ P := by rw [hQP, hQ]
      _ = -shadowQ P := zero_sub _
  have hComm : PeirceSpine.comm P (polarityGamma P) = 0 := by
    unfold PeirceSpine.comm
    rw [hPG, hGP, sub_self]
  exact ⟨hQ, hPQ, hQP, hSum, hGG, hGP, hPG, hGQ, hQG, hComm⟩

/-- **`Prop.2` (Fourfold Exhaustive Decomposition & Unilateral Nilpotency — Stratum `2`)**:
Splitting `Ω` by `1 = P + Q` yields `Ω = T + X + Y + G`, `[P, Ω] = Y - X`,
non-vanishing off-diagonal projection whenever `[P, Ω] ≠ 0`, and `X^2 = 0 = Y^2`. -/
theorem prop2_fourfold_decomp_and_nilpotency {P : E} (hP : P * P = P) (Ω : E) :
    Ω = consciousThesis P Ω + outwardProj P Ω + inwardIntrusion P Ω +
      autonomousGround P Ω ∧
    PeirceSpine.comm P Ω = inwardIntrusion P Ω - outwardProj P Ω ∧
    (PeirceSpine.comm P Ω ≠ 0 → outwardProj P Ω ≠ 0 ∨ inwardIntrusion P Ω ≠ 0) ∧
    outwardProj P Ω * outwardProj P Ω = 0 ∧
    inwardIntrusion P Ω * inwardIntrusion P Ω = 0 := by
  have h1 := prop1_orthogonality_and_polarity_involution hP
  have hPQ := h1.2.1
  have hQP := h1.2.2.1
  have hDecomp :
      Ω = consciousThesis P Ω + outwardProj P Ω + inwardIntrusion P Ω +
        autonomousGround P Ω := by
    unfold consciousThesis outwardProj inwardIntrusion autonomousGround shadowQ
    noncomm_ring
  have hComm : PeirceSpine.comm P Ω = inwardIntrusion P Ω - outwardProj P Ω := by
    unfold PeirceSpine.comm inwardIntrusion outwardProj shadowQ
    calc
      P * Ω - Ω * P = P * Ω * 1 - 1 * Ω * P := by rw [mul_one, one_mul]
      _ = P * Ω * (P + shadowQ P) - (P + shadowQ P) * Ω * P := by rw [h1.2.2.2.1]
      _ = P * Ω * shadowQ P - shadowQ P * Ω * P := by noncomm_ring
  have hNZ : PeirceSpine.comm P Ω ≠ 0 → outwardProj P Ω ≠ 0 ∨ inwardIntrusion P Ω ≠ 0 := by
    intro hne
    by_contra hboth
    rw [not_or, not_ne_iff, not_ne_iff] at hboth
    apply hne
    rw [hComm, hboth.2, hboth.1, sub_zero]
  have hX2 : outwardProj P Ω * outwardProj P Ω = 0 := by
    unfold outwardProj
    calc
      (shadowQ P * Ω * P) * (shadowQ P * Ω * P)
          = shadowQ P * Ω * (P * shadowQ P) * Ω * P := by noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hY2 : inwardIntrusion P Ω * inwardIntrusion P Ω = 0 := by
    unfold inwardIntrusion
    calc
      (P * Ω * shadowQ P) * (P * Ω * shadowQ P)
          = P * Ω * (shadowQ P * P) * Ω * shadowQ P := by noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  exact ⟨hDecomp, hComm, hNZ, hX2, hY2⟩

/-- **`Prop.3` (Oddness of the Integrative Bridge & Duality of Gravity and Tension — Stratum `3`)**:
For `F = X + Y`, `M = X Y + Y X`, and `K = Y X - X Y`, proves oddness under `Γ`,
non-vanishing of `F` when `[P, Ω] ≠ 0`, `F^2 = M`, `[Γ, M] = 0`, `K = Γ M = M Γ`,
and the holonomy separation equivalence `Y X = X Y ↔ M = 0 ↔ Y X = 0 ∧ X Y = 0`. -/
theorem prop3_transcendent_bridge_gravity_tension {P : E} (hP : P * P = P) (Ω : E) :
    polarityGamma P * integrativeBridge P Ω = PeirceSpine.comm P Ω ∧
    integrativeBridge P Ω * polarityGamma P = -PeirceSpine.comm P Ω ∧
    polarityGamma P * integrativeBridge P Ω +
      integrativeBridge P Ω * polarityGamma P = 0 ∧
    (PeirceSpine.comm P Ω ≠ 0 → integrativeBridge P Ω ≠ 0) ∧
    integrativeBridge P Ω * integrativeBridge P Ω = substantiveGravity P Ω ∧
    polarityGamma P * substantiveGravity P Ω =
      substantiveGravity P Ω * polarityGamma P ∧
    directionalTension P Ω = polarityGamma P * substantiveGravity P Ω ∧
    directionalTension P Ω = substantiveGravity P Ω * polarityGamma P ∧
    (inwardIntrusion P Ω * outwardProj P Ω =
        outwardProj P Ω * inwardIntrusion P Ω ↔
      substantiveGravity P Ω = 0) ∧
    (substantiveGravity P Ω = 0 ↔
      inwardIntrusion P Ω * outwardProj P Ω = 0 ∧
        outwardProj P Ω * inwardIntrusion P Ω = 0) := by
  have h1 := prop1_orthogonality_and_polarity_involution hP
  have h2 := prop2_fourfold_decomp_and_nilpotency hP Ω
  rcases h1 with ⟨_, hPQ, hQP, _, _, hGP, hPG, hGQ, hQG, _⟩
  have hGX : polarityGamma P * outwardProj P Ω = -outwardProj P Ω := by
    unfold outwardProj
    calc
      polarityGamma P * (shadowQ P * Ω * P)
          = (polarityGamma P * shadowQ P) * Ω * P := by
            rw [← mul_assoc (polarityGamma P), ← mul_assoc (polarityGamma P)]
      _ = (-shadowQ P) * Ω * P := by rw [hGQ]
      _ = -(shadowQ P * Ω * P) := by noncomm_ring
  have hGY : polarityGamma P * inwardIntrusion P Ω = inwardIntrusion P Ω := by
    unfold inwardIntrusion
    calc
      polarityGamma P * (P * Ω * shadowQ P)
          = (polarityGamma P * P) * Ω * shadowQ P := by
            rw [← mul_assoc (polarityGamma P), ← mul_assoc (polarityGamma P)]
      _ = P * Ω * shadowQ P := by rw [hGP]
  have hXG : outwardProj P Ω * polarityGamma P = outwardProj P Ω := by
    unfold outwardProj
    calc
      shadowQ P * Ω * P * polarityGamma P
          = shadowQ P * Ω * (P * polarityGamma P) := by rw [mul_assoc (shadowQ P * Ω)]
      _ = shadowQ P * Ω * P := by rw [hPG]
  have hYG : inwardIntrusion P Ω * polarityGamma P = -inwardIntrusion P Ω := by
    unfold inwardIntrusion
    calc
      P * Ω * shadowQ P * polarityGamma P
          = P * Ω * (shadowQ P * polarityGamma P) := by rw [mul_assoc (P * Ω)]
      _ = P * Ω * (-shadowQ P) := by rw [hQG]
      _ = -(P * Ω * shadowQ P) := by noncomm_ring
  have hGF : polarityGamma P * integrativeBridge P Ω = PeirceSpine.comm P Ω := by
    unfold integrativeBridge
    rw [mul_add, hGX, hGY, h2.2.1]
    abel
  have hFG : integrativeBridge P Ω * polarityGamma P = -PeirceSpine.comm P Ω := by
    unfold integrativeBridge
    rw [add_mul, hXG, hYG, h2.2.1]
    abel
  have hAnticomm :
      polarityGamma P * integrativeBridge P Ω +
        integrativeBridge P Ω * polarityGamma P = 0 := by
    rw [hGF, hFG, add_neg_cancel]
  have hFne : PeirceSpine.comm P Ω ≠ 0 → integrativeBridge P Ω ≠ 0 := by
    intro hne hF0
    apply hne
    rw [← hGF, hF0, mul_zero]
  have hF2 :
      integrativeBridge P Ω * integrativeBridge P Ω = substantiveGravity P Ω := by
    unfold integrativeBridge substantiveGravity
    calc
      (outwardProj P Ω + inwardIntrusion P Ω) * (outwardProj P Ω + inwardIntrusion P Ω)
          = outwardProj P Ω * outwardProj P Ω + outwardProj P Ω * inwardIntrusion P Ω +
            inwardIntrusion P Ω * outwardProj P Ω + inwardIntrusion P Ω * inwardIntrusion P Ω := by
            noncomm_ring
      _ = 0 + outwardProj P Ω * inwardIntrusion P Ω +
            inwardIntrusion P Ω * outwardProj P Ω + 0 := by rw [h2.2.2.2.1, h2.2.2.2.2]
      _ = outwardProj P Ω * inwardIntrusion P Ω +
            inwardIntrusion P Ω * outwardProj P Ω := by abel
  have hGM :
      polarityGamma P * substantiveGravity P Ω =
        substantiveGravity P Ω * polarityGamma P := by
    rw [← hF2]
    have hGF' :
        polarityGamma P * integrativeBridge P Ω =
          -(integrativeBridge P Ω * polarityGamma P) :=
      eq_neg_of_add_eq_zero_left hAnticomm
    calc
      polarityGamma P * (integrativeBridge P Ω * integrativeBridge P Ω)
          = (polarityGamma P * integrativeBridge P Ω) * integrativeBridge P Ω := by
            rw [mul_assoc]
      _ = -(integrativeBridge P Ω * polarityGamma P) * integrativeBridge P Ω := by rw [hGF']
      _ = -(integrativeBridge P Ω * (polarityGamma P * integrativeBridge P Ω)) := by
            noncomm_ring
      _ = -(integrativeBridge P Ω * -(integrativeBridge P Ω * polarityGamma P)) := by rw [hGF']
      _ = (integrativeBridge P Ω * integrativeBridge P Ω) * polarityGamma P := by
            noncomm_ring
  have hGXY :
      polarityGamma P * (outwardProj P Ω * inwardIntrusion P Ω) =
        -(outwardProj P Ω * inwardIntrusion P Ω) := by
    rw [← mul_assoc, hGX, neg_mul]
  have hGYX :
      polarityGamma P * (inwardIntrusion P Ω * outwardProj P Ω) =
        inwardIntrusion P Ω * outwardProj P Ω := by
    rw [← mul_assoc, hGY]
  have hKeqGM :
      directionalTension P Ω = polarityGamma P * substantiveGravity P Ω := by
    unfold directionalTension substantiveGravity
    rw [mul_add, hGXY, hGYX]
    abel
  have hKeqMG :
      directionalTension P Ω = substantiveGravity P Ω * polarityGamma P :=
    hKeqGM.trans hGM
  have hP_YX : P * (inwardIntrusion P Ω * outwardProj P Ω) =
      inwardIntrusion P Ω * outwardProj P Ω := by
    unfold inwardIntrusion outwardProj
    calc
      P * (P * Ω * shadowQ P * (shadowQ P * Ω * P))
          = (P * P) * Ω * shadowQ P * (shadowQ P * Ω * P) := by noncomm_ring
      _ = P * Ω * shadowQ P * (shadowQ P * Ω * P) := by rw [hP]
  have hP_XY : P * (outwardProj P Ω * inwardIntrusion P Ω) = 0 := by
    unfold outwardProj inwardIntrusion
    calc
      P * (shadowQ P * Ω * P * (P * Ω * shadowQ P))
          = (P * shadowQ P) * Ω * P * (P * Ω * shadowQ P) := by noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hM_iff_both :
      substantiveGravity P Ω = 0 ↔
        inwardIntrusion P Ω * outwardProj P Ω = 0 ∧
          outwardProj P Ω * inwardIntrusion P Ω = 0 := by
    constructor
    · intro hM0
      have hPM : P * substantiveGravity P Ω = 0 := by rw [hM0, mul_zero]
      unfold substantiveGravity at hPM
      rw [mul_add, hP_XY, hP_YX, zero_add] at hPM
      have hXY0 : outwardProj P Ω * inwardIntrusion P Ω = 0 := by
        have hM' := hM0
        unfold substantiveGravity at hM'
        rw [hPM, add_zero] at hM'
        exact hM'
      exact ⟨hPM, hXY0⟩
    · rintro ⟨hYX0, hXY0⟩
      unfold substantiveGravity
      rw [hXY0, hYX0, add_zero]
  have hComm_iff_M :
      inwardIntrusion P Ω * outwardProj P Ω =
          outwardProj P Ω * inwardIntrusion P Ω ↔
        substantiveGravity P Ω = 0 := by
    constructor
    · intro heq
      have hPeq := congrArg (fun Z => P * Z) heq
      rw [hP_YX, hP_XY] at hPeq
      rw [hM_iff_both]
      exact ⟨hPeq, heq.symm.trans hPeq⟩
    · intro hM0
      obtain ⟨hYX0, hXY0⟩ := hM_iff_both.mp hM0
      rw [hYX0, hXY0]
  refine ⟨hGF, hFG, hAnticomm, hFne, hF2, hGM, hKeqGM, hKeqMG, hComm_iff_M, hM_iff_both⟩

/-! ### Phase IV: Socratic Aporia, Dogmatic Truncation & Meta-Cognitive Tower -/

/-- **`Prop.4` (The Exact Socratic Aporia Theorem — Stratum `4`)**:
When `P^2 = P` and `Ω^2 = Ω`, `T - T^2 = Y X`, `G - G^2 = X Y`, their sum and difference
recover `M` and `K`, and the off-diagonal blocks satisfy `T Y + Y G = Y` and `X T + G X = X`. -/
theorem prop4_exact_socratic_aporia
    {P Ω : E} (hP : P * P = P) (hΩ : Ω * Ω = Ω) :
    socraticAporia P Ω = inwardIntrusion P Ω * outwardProj P Ω ∧
    shadowAporia P Ω = outwardProj P Ω * inwardIntrusion P Ω ∧
    socraticAporia P Ω + shadowAporia P Ω = substantiveGravity P Ω ∧
    socraticAporia P Ω - shadowAporia P Ω = directionalTension P Ω ∧
    consciousThesis P Ω * inwardIntrusion P Ω +
        inwardIntrusion P Ω * autonomousGround P Ω =
      inwardIntrusion P Ω ∧
    outwardProj P Ω * consciousThesis P Ω +
        autonomousGround P Ω * outwardProj P Ω =
      outwardProj P Ω := by
  have h1 := prop1_orthogonality_and_polarity_involution hP
  have hSum : P + shadowQ P = 1 := h1.2.2.2.1
  have hTT :
      consciousThesis P Ω * consciousThesis P Ω +
        inwardIntrusion P Ω * outwardProj P Ω = consciousThesis P Ω := by
    unfold consciousThesis inwardIntrusion outwardProj
    calc
      (P * Ω * P) * (P * Ω * P) + (P * Ω * shadowQ P) * (shadowQ P * Ω * P)
          = P * Ω * ((P * P) + shadowQ P * shadowQ P) * Ω * P := by noncomm_ring
      _ = P * Ω * (P + shadowQ P) * Ω * P := by rw [hP, h1.1]
      _ = P * Ω * 1 * Ω * P := by rw [hSum]
      _ = P * (Ω * Ω) * P := by noncomm_ring
      _ = P * Ω * P := by rw [hΩ]
  have hGG :
      autonomousGround P Ω * autonomousGround P Ω +
        outwardProj P Ω * inwardIntrusion P Ω = autonomousGround P Ω := by
    unfold autonomousGround outwardProj inwardIntrusion
    calc
      (shadowQ P * Ω * shadowQ P) * (shadowQ P * Ω * shadowQ P) +
          (shadowQ P * Ω * P) * (P * Ω * shadowQ P)
          = shadowQ P * Ω * (shadowQ P * shadowQ P + P * P) * Ω * shadowQ P := by
            noncomm_ring
      _ = shadowQ P * Ω * (shadowQ P + P) * Ω * shadowQ P := by rw [h1.1, hP]
      _ = shadowQ P * Ω * (P + shadowQ P) * Ω * shadowQ P := by
            rw [add_comm (shadowQ P) P]
      _ = shadowQ P * Ω * 1 * Ω * shadowQ P := by rw [hSum]
      _ = shadowQ P * (Ω * Ω) * shadowQ P := by noncomm_ring
      _ = shadowQ P * Ω * shadowQ P := by rw [hΩ]
  have hApT : socraticAporia P Ω = inwardIntrusion P Ω * outwardProj P Ω := by
    unfold socraticAporia
    calc
      consciousThesis P Ω - consciousThesis P Ω * consciousThesis P Ω
          = (consciousThesis P Ω * consciousThesis P Ω +
              inwardIntrusion P Ω * outwardProj P Ω) -
            consciousThesis P Ω * consciousThesis P Ω := by rw [hTT]
      _ = inwardIntrusion P Ω * outwardProj P Ω := by abel
  have hApG : shadowAporia P Ω = outwardProj P Ω * inwardIntrusion P Ω := by
    unfold shadowAporia
    calc
      autonomousGround P Ω - autonomousGround P Ω * autonomousGround P Ω
          = (autonomousGround P Ω * autonomousGround P Ω +
              outwardProj P Ω * inwardIntrusion P Ω) -
            autonomousGround P Ω * autonomousGround P Ω := by rw [hGG]
      _ = outwardProj P Ω * inwardIntrusion P Ω := by abel
  have hTY :
      consciousThesis P Ω * inwardIntrusion P Ω +
          inwardIntrusion P Ω * autonomousGround P Ω =
        inwardIntrusion P Ω := by
    unfold consciousThesis inwardIntrusion autonomousGround
    calc
      (P * Ω * P) * (P * Ω * shadowQ P) +
          (P * Ω * shadowQ P) * (shadowQ P * Ω * shadowQ P)
          = P * Ω * (P * P + shadowQ P * shadowQ P) * Ω * shadowQ P := by noncomm_ring
      _ = P * Ω * (P + shadowQ P) * Ω * shadowQ P := by rw [hP, h1.1]
      _ = P * Ω * 1 * Ω * shadowQ P := by rw [hSum]
      _ = P * (Ω * Ω) * shadowQ P := by noncomm_ring
      _ = P * Ω * shadowQ P := by rw [hΩ]
  have hXT :
      outwardProj P Ω * consciousThesis P Ω +
          autonomousGround P Ω * outwardProj P Ω =
        outwardProj P Ω := by
    unfold outwardProj consciousThesis autonomousGround
    calc
      (shadowQ P * Ω * P) * (P * Ω * P) +
          (shadowQ P * Ω * shadowQ P) * (shadowQ P * Ω * P)
          = shadowQ P * Ω * (P * P + shadowQ P * shadowQ P) * Ω * P := by noncomm_ring
      _ = shadowQ P * Ω * (P + shadowQ P) * Ω * P := by rw [hP, h1.1]
      _ = shadowQ P * Ω * 1 * Ω * P := by rw [hSum]
      _ = shadowQ P * (Ω * Ω) * P := by noncomm_ring
      _ = shadowQ P * Ω * P := by rw [hΩ]
  refine ⟨hApT, hApG, ?_, ?_, hTY, hXT⟩
  · rw [hApT, hApG]
    unfold substantiveGravity
    abel
  · rw [hApT, hApG]
    rfl

/-- **`Prop.5` (Incompleteness of Dogmatic Truncation — Stratum `4`)**:
The severed diagonal operator `Σ₀ := (2 T - P) + (2 G - Q)` anticommutes with
`B := 2 F` and suffers the exact involutive defect `1 - Σ₀^2 = B^2 = 4 M`. -/
theorem prop5_incompleteness_of_dogmatic_truncation
    {P Ω : E} (hP : P * P = P) (hΩ : Ω * Ω = Ω) :
    dogmaticTruncation P Ω * doubledBridge P Ω +
      doubledBridge P Ω * dogmaticTruncation P Ω = 0 ∧
    doubledBridge P Ω * doubledBridge P Ω = 4 * substantiveGravity P Ω ∧
    1 - dogmaticTruncation P Ω * dogmaticTruncation P Ω =
      doubledBridge P Ω * doubledBridge P Ω ∧
    1 - dogmaticTruncation P Ω * dogmaticTruncation P Ω =
      4 * substantiveGravity P Ω := by
  have h1 := prop1_orthogonality_and_polarity_involution hP
  have h3 := prop3_transcendent_bridge_gravity_tension hP Ω
  have h4 := prop4_exact_socratic_aporia hP hΩ
  have hQ := h1.1
  have hPQ := h1.2.1
  have hQP := h1.2.2.1
  have hTP : consciousThesis P Ω * P = consciousThesis P Ω := by
    unfold consciousThesis; rw [mul_assoc (P * Ω), hP]
  have hPT : P * consciousThesis P Ω = consciousThesis P Ω := by
    unfold consciousThesis; rw [← mul_assoc P (P * Ω), ← mul_assoc P P Ω, hP]
  have hGQ : autonomousGround P Ω * shadowQ P = autonomousGround P Ω := by
    unfold autonomousGround; rw [mul_assoc (shadowQ P * Ω), hQ]
  have hQG : shadowQ P * autonomousGround P Ω = autonomousGround P Ω := by
    unfold autonomousGround
    rw [← mul_assoc (shadowQ P) (shadowQ P * Ω), ← mul_assoc (shadowQ P) (shadowQ P) Ω, hQ]
  have hSq1 :
      (2 * consciousThesis P Ω - P) * (2 * consciousThesis P Ω - P) =
        P - 4 * (inwardIntrusion P Ω * outwardProj P Ω) := by
    calc
      (2 * consciousThesis P Ω - P) * (2 * consciousThesis P Ω - P)
          = 4 * (consciousThesis P Ω * consciousThesis P Ω) -
              2 * (consciousThesis P Ω * P) - 2 * (P * consciousThesis P Ω) + P * P := by
            noncomm_ring
      _ = 4 * (consciousThesis P Ω * consciousThesis P Ω) -
            4 * consciousThesis P Ω + P := by
          rw [hTP, hPT, hP]; noncomm_ring
      _ = P - 4 * socraticAporia P Ω := by
          unfold socraticAporia; noncomm_ring
      _ = P - 4 * (inwardIntrusion P Ω * outwardProj P Ω) := by rw [h4.1]
  have hSq2 :
      (2 * autonomousGround P Ω - shadowQ P) * (2 * autonomousGround P Ω - shadowQ P) =
        shadowQ P - 4 * (outwardProj P Ω * inwardIntrusion P Ω) := by
    calc
      (2 * autonomousGround P Ω - shadowQ P) * (2 * autonomousGround P Ω - shadowQ P)
          = 4 * (autonomousGround P Ω * autonomousGround P Ω) -
              2 * (autonomousGround P Ω * shadowQ P) -
              2 * (shadowQ P * autonomousGround P Ω) + shadowQ P * shadowQ P := by
            noncomm_ring
      _ = 4 * (autonomousGround P Ω * autonomousGround P Ω) -
            4 * autonomousGround P Ω + shadowQ P := by
          rw [hGQ, hQG, hQ]; noncomm_ring
      _ = shadowQ P - 4 * shadowAporia P Ω := by
          unfold shadowAporia; noncomm_ring
      _ = shadowQ P - 4 * (outwardProj P Ω * inwardIntrusion P Ω) := by rw [h4.2.1]
  have hCross12 :
      (2 * consciousThesis P Ω - P) * (2 * autonomousGround P Ω - shadowQ P) = 0 := by
    unfold consciousThesis autonomousGround
    calc
      (2 * (P * Ω * P) - P) * (2 * (shadowQ P * Ω * shadowQ P) - shadowQ P)
          = (2 * (P * Ω) - 1) * (P * shadowQ P) * (2 * (Ω * shadowQ P) - 1) := by
            noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hCross21 :
      (2 * autonomousGround P Ω - shadowQ P) * (2 * consciousThesis P Ω - P) = 0 := by
    unfold autonomousGround consciousThesis
    calc
      (2 * (shadowQ P * Ω * shadowQ P) - shadowQ P) * (2 * (P * Ω * P) - P)
          = (2 * (shadowQ P * Ω) - 1) * (shadowQ P * P) * (2 * (Ω * P) - 1) := by
            noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  have hSigSq :
      dogmaticTruncation P Ω * dogmaticTruncation P Ω =
        1 - 4 * substantiveGravity P Ω := by
    unfold dogmaticTruncation
    calc
      ((2 * consciousThesis P Ω - P) + (2 * autonomousGround P Ω - shadowQ P)) *
          ((2 * consciousThesis P Ω - P) + (2 * autonomousGround P Ω - shadowQ P))
          = (2 * consciousThesis P Ω - P) * (2 * consciousThesis P Ω - P) +
              (2 * consciousThesis P Ω - P) * (2 * autonomousGround P Ω - shadowQ P) +
              (2 * autonomousGround P Ω - shadowQ P) * (2 * consciousThesis P Ω - P) +
              (2 * autonomousGround P Ω - shadowQ P) *
                (2 * autonomousGround P Ω - shadowQ P) := by noncomm_ring
      _ = (P - 4 * (inwardIntrusion P Ω * outwardProj P Ω)) + 0 + 0 +
            (shadowQ P - 4 * (outwardProj P Ω * inwardIntrusion P Ω)) := by
          rw [hSq1, hCross12, hCross21, hSq2]
      _ = (P + shadowQ P) -
            4 * (outwardProj P Ω * inwardIntrusion P Ω +
              inwardIntrusion P Ω * outwardProj P Ω) := by noncomm_ring
      _ = 1 - 4 * substantiveGravity P Ω := by
          rw [h1.2.2.2.1]; unfold substantiveGravity; rfl
  have hB2 : doubledBridge P Ω * doubledBridge P Ω = 4 * substantiveGravity P Ω := by
    unfold doubledBridge
    calc
      (2 * integrativeBridge P Ω) * (2 * integrativeBridge P Ω)
          = 4 * (integrativeBridge P Ω * integrativeBridge P Ω) := by noncomm_ring
      _ = 4 * substantiveGravity P Ω := by rw [h3.2.2.2.2.1]
  have hOneMinus :
      1 - dogmaticTruncation P Ω * dogmaticTruncation P Ω =
        4 * substantiveGravity P Ω := by
    rw [hSigSq]; noncomm_ring
  have hTX : consciousThesis P Ω * outwardProj P Ω = 0 := by
    unfold consciousThesis outwardProj
    calc
      (P * Ω * P) * (shadowQ P * Ω * P)
          = P * (Ω * ((P * shadowQ P) * (Ω * P))) := by simp only [mul_assoc]
      _ = 0 := by rw [hPQ, zero_mul, mul_zero, mul_zero]
  have hXG0 : outwardProj P Ω * autonomousGround P Ω = 0 := by
    unfold outwardProj autonomousGround
    calc
      (shadowQ P * Ω * P) * (shadowQ P * Ω * shadowQ P)
          = shadowQ P * Ω * (P * shadowQ P) * Ω * shadowQ P := by noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hGY0 : autonomousGround P Ω * inwardIntrusion P Ω = 0 := by
    unfold autonomousGround inwardIntrusion
    calc
      (shadowQ P * Ω * shadowQ P) * (P * Ω * shadowQ P)
          = shadowQ P * Ω * (shadowQ P * P) * Ω * shadowQ P := by noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  have hYT0 : inwardIntrusion P Ω * consciousThesis P Ω = 0 := by
    unfold inwardIntrusion consciousThesis
    calc
      (P * Ω * shadowQ P) * (P * Ω * P)
          = P * Ω * (shadowQ P * P) * Ω * P := by noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  have hPY : P * inwardIntrusion P Ω = inwardIntrusion P Ω := by
    unfold inwardIntrusion
    rw [← mul_assoc P (P * Ω), ← mul_assoc P P Ω, hP]
  have hYQ : inwardIntrusion P Ω * shadowQ P = inwardIntrusion P Ω := by
    unfold inwardIntrusion; rw [mul_assoc (P * Ω), hQ]
  have hQX : shadowQ P * outwardProj P Ω = outwardProj P Ω := by
    unfold outwardProj
    rw [← mul_assoc (shadowQ P) (shadowQ P * Ω), ← mul_assoc (shadowQ P) (shadowQ P) Ω, hQ]
  have hXP : outwardProj P Ω * P = outwardProj P Ω := by
    unfold outwardProj; rw [mul_assoc (shadowQ P * Ω), hP]
  have hPX : P * outwardProj P Ω = 0 := by
    unfold outwardProj
    calc
      P * (shadowQ P * Ω * P) = (P * shadowQ P) * Ω * P := by noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hYP : inwardIntrusion P Ω * P = 0 := by
    unfold inwardIntrusion
    calc
      (P * Ω * shadowQ P) * P = P * Ω * (shadowQ P * P) := by noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  have hQY : shadowQ P * inwardIntrusion P Ω = 0 := by
    unfold inwardIntrusion
    calc
      shadowQ P * (P * Ω * shadowQ P) = (shadowQ P * P) * Ω * shadowQ P := by noncomm_ring
      _ = 0 := by rw [hQP]; noncomm_ring
  have hXQ : outwardProj P Ω * shadowQ P = 0 := by
    unfold outwardProj
    calc
      (shadowQ P * Ω * P) * shadowQ P = shadowQ P * Ω * (P * shadowQ P) := by noncomm_ring
      _ = 0 := by rw [hPQ]; noncomm_ring
  have hAntiF :
      dogmaticTruncation P Ω * integrativeBridge P Ω +
        integrativeBridge P Ω * dogmaticTruncation P Ω = 0 := by
    unfold dogmaticTruncation integrativeBridge
    calc
      ((2 * consciousThesis P Ω - P) + (2 * autonomousGround P Ω - shadowQ P)) *
            (outwardProj P Ω + inwardIntrusion P Ω) +
          (outwardProj P Ω + inwardIntrusion P Ω) *
            ((2 * consciousThesis P Ω - P) + (2 * autonomousGround P Ω - shadowQ P))
          = 2 * (consciousThesis P Ω * outwardProj P Ω) +
              2 * (consciousThesis P Ω * inwardIntrusion P Ω) - P * outwardProj P Ω -
              P * inwardIntrusion P Ω + 2 * (autonomousGround P Ω * outwardProj P Ω) +
              2 * (autonomousGround P Ω * inwardIntrusion P Ω) -
              shadowQ P * outwardProj P Ω - shadowQ P * inwardIntrusion P Ω +
              (2 * (outwardProj P Ω * consciousThesis P Ω) - outwardProj P Ω * P +
                2 * (outwardProj P Ω * autonomousGround P Ω) -
                outwardProj P Ω * shadowQ P +
                2 * (inwardIntrusion P Ω * consciousThesis P Ω) - inwardIntrusion P Ω * P +
                2 * (inwardIntrusion P Ω * autonomousGround P Ω) -
                inwardIntrusion P Ω * shadowQ P) := by noncomm_ring
      _ = 2 * 0 + 2 * (consciousThesis P Ω * inwardIntrusion P Ω) - 0 -
              inwardIntrusion P Ω + 2 * (autonomousGround P Ω * outwardProj P Ω) +
              2 * 0 - outwardProj P Ω - 0 +
              (2 * (outwardProj P Ω * consciousThesis P Ω) - outwardProj P Ω +
                2 * 0 - 0 + 2 * 0 - 0 +
                2 * (inwardIntrusion P Ω * autonomousGround P Ω) -
                inwardIntrusion P Ω) := by
            rw [hTX, hPX, hPY, hGY0, hQX, hQY, hXP, hXG0, hXQ, hYT0, hYP, hYQ]
      _ = 2 * (consciousThesis P Ω * inwardIntrusion P Ω +
                inwardIntrusion P Ω * autonomousGround P Ω - inwardIntrusion P Ω) +
              2 * (outwardProj P Ω * consciousThesis P Ω +
                autonomousGround P Ω * outwardProj P Ω - outwardProj P Ω) := by
            noncomm_ring
      _ = 2 * (inwardIntrusion P Ω - inwardIntrusion P Ω) +
            2 * (outwardProj P Ω - outwardProj P Ω) := by rw [h4.2.2.2.2.1, h4.2.2.2.2.2]
      _ = 0 := by noncomm_ring
  have hAntiB :
      dogmaticTruncation P Ω * doubledBridge P Ω +
        doubledBridge P Ω * dogmaticTruncation P Ω = 0 := by
    unfold doubledBridge
    calc
      dogmaticTruncation P Ω * (2 * integrativeBridge P Ω) +
          (2 * integrativeBridge P Ω) * dogmaticTruncation P Ω
          = 2 * (dogmaticTruncation P Ω * integrativeBridge P Ω +
              integrativeBridge P Ω * dogmaticTruncation P Ω) := by noncomm_ring
      _ = 0 := by rw [hAntiF, mul_zero]
  exact ⟨hAntiB, hB2, hOneMinus.trans hB2.symm, hOneMinus⟩

/-- **`Ax.4` (Meta-Cognitive Reflection Tower — Stratum `5`)**:
Stage-wise independent cuts `(P_k, Ω_k)` (`P_k^2 = P_k`, `Ω_k^2 = Ω_k`) whose raw
operators commute across distinct reflection stages `j ≠ k`. -/
structure MetaCognitiveTower (E : Type*) [Ring E] where
  P : ℕ → E
  Ω : ℕ → E
  hP : ∀ k : ℕ, P k * P k = P k
  hΩ : ∀ k : ℕ, Ω k * Ω k = Ω k
  gamma_comm : ∀ j k : ℕ, j ≠ k →
    polarityGamma (P j) * polarityGamma (P k) =
      polarityGamma (P k) * polarityGamma (P j)
  gamma_bridge_comm : ∀ j k : ℕ, j ≠ k →
    polarityGamma (P j) * doubledBridge (P k) (Ω k) =
      doubledBridge (P k) (Ω k) * polarityGamma (P j)
  bridge_comm : ∀ j k : ℕ, j ≠ k →
    doubledBridge (P j) (Ω j) * doubledBridge (P k) (Ω k) =
      doubledBridge (P k) (Ω k) * doubledBridge (P j) (Ω j)

/-- Ordered Jordan–Wigner / parity prefix `∏_{j=0}^{k-1} Γ_j`. -/
def parityPrefix (P : ℕ → E) : ℕ → E
  | 0 => 1
  | k + 1 => parityPrefix P k * polarityGamma (P k)

/-- Parity-soldered meta-bridge `B_hat_k := (∏_{j<k} Γ_j) B_k` (Stratum `5`). -/
def solderedBridge (P Ω : ℕ → E) (k : ℕ) : E :=
  parityPrefix P k * doubledBridge (P k) (Ω k)

/-- Cumulative tower operator `D_N := ∑_{k=0}^{N} B_hat_k` (Stratum `5`). -/
def cumulativeMetaOp (P Ω : ℕ → E) (N : ℕ) : E :=
  ∑ k ∈ Finset.range (N + 1), solderedBridge P Ω k

private lemma polarityGamma_doubledBridge_anticomm
    {P Ω : E} (hP : P * P = P) :
    polarityGamma P * doubledBridge P Ω = -(doubledBridge P Ω * polarityGamma P) := by
  have h3 := prop3_transcendent_bridge_gravity_tension hP Ω
  unfold doubledBridge
  have hAnti :
      polarityGamma P * integrativeBridge P Ω =
        -(integrativeBridge P Ω * polarityGamma P) :=
    eq_neg_of_add_eq_zero_left h3.2.2.1
  calc
    polarityGamma P * (2 * integrativeBridge P Ω)
        = 2 * (polarityGamma P * integrativeBridge P Ω) := by noncomm_ring
    _ = 2 * -(integrativeBridge P Ω * polarityGamma P) := by rw [hAnti]
    _ = -((2 * integrativeBridge P Ω) * polarityGamma P) := by noncomm_ring

private lemma parityPrefix_comm_polarityGamma
    (τ : MetaCognitiveTower E) (k m : ℕ) :
    parityPrefix τ.P k * polarityGamma (τ.P m) =
      polarityGamma (τ.P m) * parityPrefix τ.P k := by
  induction k with
  | zero => simp [parityPrefix]
  | succ k ih =>
    by_cases hkm : k = m
    · subst hkm
      calc
        (parityPrefix τ.P k * polarityGamma (τ.P k)) * polarityGamma (τ.P k)
            = (polarityGamma (τ.P k) * parityPrefix τ.P k) * polarityGamma (τ.P k) := by
              rw [ih]
        _ = polarityGamma (τ.P k) * (parityPrefix τ.P k * polarityGamma (τ.P k)) := by
              rw [mul_assoc]
    · simp only [parityPrefix, mul_assoc]
      rw [τ.gamma_comm k m hkm, ← mul_assoc, ih, mul_assoc]

private lemma parityPrefix_sq (τ : MetaCognitiveTower E) (k : ℕ) :
    parityPrefix τ.P k * parityPrefix τ.P k = 1 := by
  induction k with
  | zero => simp [parityPrefix]
  | succ k ih =>
    have hGk : polarityGamma (τ.P k) * polarityGamma (τ.P k) = 1 :=
      (prop1_orthogonality_and_polarity_involution (τ.hP k)).2.2.2.2.1
    calc
      parityPrefix τ.P (k + 1) * parityPrefix τ.P (k + 1)
          = (parityPrefix τ.P k * polarityGamma (τ.P k)) *
              (parityPrefix τ.P k * polarityGamma (τ.P k)) := rfl
      _ = parityPrefix τ.P k * (polarityGamma (τ.P k) * parityPrefix τ.P k) *
            polarityGamma (τ.P k) := by noncomm_ring
      _ = parityPrefix τ.P k * (parityPrefix τ.P k * polarityGamma (τ.P k)) *
            polarityGamma (τ.P k) := by rw [← parityPrefix_comm_polarityGamma τ k k]
      _ = (parityPrefix τ.P k * parityPrefix τ.P k) *
            (polarityGamma (τ.P k) * polarityGamma (τ.P k)) := by noncomm_ring
      _ = 1 := by rw [ih, hGk, mul_one]

private lemma parityPrefix_comm_doubledBridge
    (τ : MetaCognitiveTower E) {k m : ℕ} (hkm : k ≤ m) :
    parityPrefix τ.P k * doubledBridge (τ.P m) (τ.Ω m) =
      doubledBridge (τ.P m) (τ.Ω m) * parityPrefix τ.P k := by
  induction k with
  | zero => simp [parityPrefix]
  | succ k ih =>
    have hlt : k < m := Nat.lt_of_succ_le hkm
    have hk_le : k ≤ m := Nat.le_of_lt hlt
    have hne : k ≠ m := Nat.ne_of_lt hlt
    calc
      (parityPrefix τ.P k * polarityGamma (τ.P k)) * doubledBridge (τ.P m) (τ.Ω m)
          = parityPrefix τ.P k * (polarityGamma (τ.P k) * doubledBridge (τ.P m) (τ.Ω m)) := by
            rw [mul_assoc]
      _ = parityPrefix τ.P k * (doubledBridge (τ.P m) (τ.Ω m) * polarityGamma (τ.P k)) := by
            rw [τ.gamma_bridge_comm k m hne]
      _ = (parityPrefix τ.P k * doubledBridge (τ.P m) (τ.Ω m)) * polarityGamma (τ.P k) := by
            rw [← mul_assoc]
      _ = (doubledBridge (τ.P m) (τ.Ω m) * parityPrefix τ.P k) * polarityGamma (τ.P k) := by
            rw [ih hk_le]
      _ = doubledBridge (τ.P m) (τ.Ω m) * (parityPrefix τ.P k * polarityGamma (τ.P k)) := by
            rw [mul_assoc]

private lemma parityPrefix_anticomm_doubledBridge
    (τ : MetaCognitiveTower E) {r s : ℕ} (hrs : r < s) :
    parityPrefix τ.P s * doubledBridge (τ.P r) (τ.Ω r) =
      -(doubledBridge (τ.P r) (τ.Ω r) * parityPrefix τ.P s) := by
  induction s with
  | zero => exact False.elim (Nat.not_lt_zero r hrs)
  | succ s ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hrs with hlt | heq
    · have hne : s ≠ r := Nat.ne_of_gt hlt
      calc
        (parityPrefix τ.P s * polarityGamma (τ.P s)) * doubledBridge (τ.P r) (τ.Ω r)
            = parityPrefix τ.P s *
                (polarityGamma (τ.P s) * doubledBridge (τ.P r) (τ.Ω r)) := by
              rw [mul_assoc]
        _ = parityPrefix τ.P s *
              (doubledBridge (τ.P r) (τ.Ω r) * polarityGamma (τ.P s)) := by
              rw [τ.gamma_bridge_comm s r hne]
        _ = (parityPrefix τ.P s * doubledBridge (τ.P r) (τ.Ω r)) *
              polarityGamma (τ.P s) := by rw [← mul_assoc]
        _ = (-(doubledBridge (τ.P r) (τ.Ω r) * parityPrefix τ.P s)) *
              polarityGamma (τ.P s) := by rw [ih hlt]
        _ = -(doubledBridge (τ.P r) (τ.Ω r) *
              (parityPrefix τ.P s * polarityGamma (τ.P s))) := by noncomm_ring
    · subst r
      have hcomm :
          parityPrefix τ.P s * doubledBridge (τ.P s) (τ.Ω s) =
            doubledBridge (τ.P s) (τ.Ω s) * parityPrefix τ.P s :=
        parityPrefix_comm_doubledBridge τ le_rfl
      have hanti := polarityGamma_doubledBridge_anticomm (Ω := τ.Ω s) (τ.hP s)
      calc
        (parityPrefix τ.P s * polarityGamma (τ.P s)) * doubledBridge (τ.P s) (τ.Ω s)
            = parityPrefix τ.P s *
                (polarityGamma (τ.P s) * doubledBridge (τ.P s) (τ.Ω s)) := by
              rw [mul_assoc]
        _ = parityPrefix τ.P s *
              (-(doubledBridge (τ.P s) (τ.Ω s) * polarityGamma (τ.P s))) := by
              rw [hanti]
        _ = -((parityPrefix τ.P s * doubledBridge (τ.P s) (τ.Ω s)) *
              polarityGamma (τ.P s)) := by noncomm_ring
        _ = -((doubledBridge (τ.P s) (τ.Ω s) * parityPrefix τ.P s) *
              polarityGamma (τ.P s)) := by rw [hcomm]
        _ = -(doubledBridge (τ.P s) (τ.Ω s) *
              (parityPrefix τ.P s * polarityGamma (τ.P s))) := by noncomm_ring

/-- **`Prop.6` (Parity-Soldered Meta-Cognitive Coherence — Stratum `5`)**:
At every stage `k`, `A_k = Y_k X_k`, the parity-soldered bridges satisfy `B_hat_k^2 = B_k^2 = 4 M_k`
and strict Clifford anticommutation `{B_hat_r, B_hat_s} = 0` (`r ≠ s`), and the cumulative
meta-operator satisfies `D_N^2 = ∑_{k ≤ N} B_k^2 = 4 ∑_{k ≤ N} M_k`. -/
theorem prop6_parity_soldered_metacognitive_coherence
    (τ : MetaCognitiveTower E) :
    (∀ k : ℕ,
      socraticAporia (τ.P k) (τ.Ω k) =
        inwardIntrusion (τ.P k) (τ.Ω k) * outwardProj (τ.P k) (τ.Ω k)) ∧
    (∀ k : ℕ,
      solderedBridge τ.P τ.Ω k * solderedBridge τ.P τ.Ω k =
        doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k) ∧
      solderedBridge τ.P τ.Ω k * solderedBridge τ.P τ.Ω k =
        4 * substantiveGravity (τ.P k) (τ.Ω k)) ∧
    (∀ r s : ℕ, r ≠ s →
      solderedBridge τ.P τ.Ω r * solderedBridge τ.P τ.Ω s +
        solderedBridge τ.P τ.Ω s * solderedBridge τ.P τ.Ω r = 0) ∧
    (∀ N : ℕ,
      cumulativeMetaOp τ.P τ.Ω N * cumulativeMetaOp τ.P τ.Ω N =
        ∑ k ∈ Finset.range (N + 1),
          (doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k)) ∧
      cumulativeMetaOp τ.P τ.Ω N * cumulativeMetaOp τ.P τ.Ω N =
        4 * ∑ k ∈ Finset.range (N + 1), substantiveGravity (τ.P k) (τ.Ω k)) := by
  have hStageAp : ∀ k : ℕ,
      socraticAporia (τ.P k) (τ.Ω k) =
        inwardIntrusion (τ.P k) (τ.Ω k) * outwardProj (τ.P k) (τ.Ω k) :=
    fun k => (prop4_exact_socratic_aporia (τ.hP k) (τ.hΩ k)).1
  have hBhatSq : ∀ k : ℕ,
      solderedBridge τ.P τ.Ω k * solderedBridge τ.P τ.Ω k =
        doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k) := by
    intro k
    have hcomm := parityPrefix_comm_doubledBridge τ (le_refl k)
    have hsq := parityPrefix_sq τ k
    calc
      solderedBridge τ.P τ.Ω k * solderedBridge τ.P τ.Ω k
          = parityPrefix τ.P k * (doubledBridge (τ.P k) (τ.Ω k) * parityPrefix τ.P k) *
              doubledBridge (τ.P k) (τ.Ω k) := by
            unfold solderedBridge; noncomm_ring
      _ = parityPrefix τ.P k * (parityPrefix τ.P k * doubledBridge (τ.P k) (τ.Ω k)) *
            doubledBridge (τ.P k) (τ.Ω k) := by rw [← hcomm]
      _ = (parityPrefix τ.P k * parityPrefix τ.P k) *
            (doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k)) := by
            noncomm_ring
      _ = doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k) := by
            rw [hsq, one_mul]
  have hBhatM : ∀ k : ℕ,
      solderedBridge τ.P τ.Ω k * solderedBridge τ.P τ.Ω k =
        4 * substantiveGravity (τ.P k) (τ.Ω k) := by
    intro k
    rw [hBhatSq k, (prop5_incompleteness_of_dogmatic_truncation (τ.hP k) (τ.hΩ k)).2.1]
  have hAntiOrdered : ∀ {r s : ℕ}, r < s →
      solderedBridge τ.P τ.Ω r * solderedBridge τ.P τ.Ω s +
        solderedBridge τ.P τ.Ω s * solderedBridge τ.P τ.Ω r = 0 := by
    intro r s hrs
    have hne : r ≠ s := Nat.ne_of_lt hrs
    have h1 := parityPrefix_comm_doubledBridge τ (Nat.le_of_lt hrs)
    have h2 := parityPrefix_anticomm_doubledBridge τ hrs
    have hPcomm :
        parityPrefix τ.P r * parityPrefix τ.P s =
          parityPrefix τ.P s * parityPrefix τ.P r := by
      clear hrs hne h1 h2
      induction r with
      | zero => simp [parityPrefix]
      | succ r ih =>
        calc
          (parityPrefix τ.P r * polarityGamma (τ.P r)) * parityPrefix τ.P s
              = parityPrefix τ.P r * (polarityGamma (τ.P r) * parityPrefix τ.P s) := by
                rw [mul_assoc]
          _ = parityPrefix τ.P r * (parityPrefix τ.P s * polarityGamma (τ.P r)) := by
                rw [← parityPrefix_comm_polarityGamma τ s r]
          _ = (parityPrefix τ.P r * parityPrefix τ.P s) * polarityGamma (τ.P r) := by
                rw [← mul_assoc]
          _ = (parityPrefix τ.P s * parityPrefix τ.P r) * polarityGamma (τ.P r) := by rw [ih]
          _ = parityPrefix τ.P s * (parityPrefix τ.P r * polarityGamma (τ.P r)) := by
                rw [mul_assoc]
    have hBrBs :
        solderedBridge τ.P τ.Ω r * solderedBridge τ.P τ.Ω s =
          -(parityPrefix τ.P r * parityPrefix τ.P s *
            (doubledBridge (τ.P r) (τ.Ω r) * doubledBridge (τ.P s) (τ.Ω s))) := by
      unfold solderedBridge
      calc
        parityPrefix τ.P r * doubledBridge (τ.P r) (τ.Ω r) *
            (parityPrefix τ.P s * doubledBridge (τ.P s) (τ.Ω s))
            = parityPrefix τ.P r * (doubledBridge (τ.P r) (τ.Ω r) * parityPrefix τ.P s) *
                doubledBridge (τ.P s) (τ.Ω s) := by noncomm_ring
        _ = parityPrefix τ.P r * (-(parityPrefix τ.P s * doubledBridge (τ.P r) (τ.Ω r))) *
              doubledBridge (τ.P s) (τ.Ω s) := by rw [h2, neg_neg]
        _ = -(parityPrefix τ.P r * parityPrefix τ.P s *
              (doubledBridge (τ.P r) (τ.Ω r) * doubledBridge (τ.P s) (τ.Ω s))) := by
            noncomm_ring
    have hBsBr :
        solderedBridge τ.P τ.Ω s * solderedBridge τ.P τ.Ω r =
          parityPrefix τ.P r * parityPrefix τ.P s *
            (doubledBridge (τ.P r) (τ.Ω r) * doubledBridge (τ.P s) (τ.Ω s)) := by
      unfold solderedBridge
      calc
        parityPrefix τ.P s * doubledBridge (τ.P s) (τ.Ω s) *
            (parityPrefix τ.P r * doubledBridge (τ.P r) (τ.Ω r))
            = parityPrefix τ.P s * (doubledBridge (τ.P s) (τ.Ω s) * parityPrefix τ.P r) *
                doubledBridge (τ.P r) (τ.Ω r) := by noncomm_ring
        _ = parityPrefix τ.P s * (parityPrefix τ.P r * doubledBridge (τ.P s) (τ.Ω s)) *
              doubledBridge (τ.P r) (τ.Ω r) := by rw [← h1]
        _ = (parityPrefix τ.P s * parityPrefix τ.P r) *
              (doubledBridge (τ.P s) (τ.Ω s) * doubledBridge (τ.P r) (τ.Ω r)) := by
            noncomm_ring
        _ = (parityPrefix τ.P r * parityPrefix τ.P s) *
              (doubledBridge (τ.P r) (τ.Ω r) * doubledBridge (τ.P s) (τ.Ω s)) := by
            rw [hPcomm, τ.bridge_comm s r hne.symm]
    rw [hBrBs, hBsBr, neg_add_cancel]
  have hAntiAll : ∀ r s : ℕ, r ≠ s →
      solderedBridge τ.P τ.Ω r * solderedBridge τ.P τ.Ω s +
        solderedBridge τ.P τ.Ω s * solderedBridge τ.P τ.Ω r = 0 := by
    intro r s hne
    rcases lt_or_gt_of_ne hne with hrs | hsr
    · exact hAntiOrdered hrs
    · rw [add_comm]
      exact hAntiOrdered hsr
  have hSumSq : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) *
        (∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) =
      ∑ k ∈ Finset.range n,
        (doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hCross :
          (∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) * solderedBridge τ.P τ.Ω n +
            solderedBridge τ.P τ.Ω n * (∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) =
          0 := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_eq_zero fun k hk =>
          hAntiAll k n (Nat.ne_of_lt (Finset.mem_range.mp hk))
      calc
        ((∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) + solderedBridge τ.P τ.Ω n) *
            ((∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) + solderedBridge τ.P τ.Ω n)
            = (∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) *
                (∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) +
                ((∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k) *
                    solderedBridge τ.P τ.Ω n +
                  solderedBridge τ.P τ.Ω n *
                    (∑ k ∈ Finset.range n, solderedBridge τ.P τ.Ω k)) +
                solderedBridge τ.P τ.Ω n * solderedBridge τ.P τ.Ω n := by noncomm_ring
        _ = ∑ k ∈ Finset.range n,
              (doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k)) + 0 +
              (doubledBridge (τ.P n) (τ.Ω n) * doubledBridge (τ.P n) (τ.Ω n)) := by
            rw [ih, hCross, hBhatSq n]
        _ = (∑ k ∈ Finset.range n,
              (doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k))) +
              doubledBridge (τ.P n) (τ.Ω n) * doubledBridge (τ.P n) (τ.Ω n) := by
            rw [add_zero]
  have hCumul : ∀ N : ℕ,
      cumulativeMetaOp τ.P τ.Ω N * cumulativeMetaOp τ.P τ.Ω N =
        ∑ k ∈ Finset.range (N + 1),
          (doubledBridge (τ.P k) (τ.Ω k) * doubledBridge (τ.P k) (τ.Ω k)) ∧
      cumulativeMetaOp τ.P τ.Ω N * cumulativeMetaOp τ.P τ.Ω N =
        4 * ∑ k ∈ Finset.range (N + 1), substantiveGravity (τ.P k) (τ.Ω k) := by
    intro N
    unfold cumulativeMetaOp
    have h1N := hSumSq (N + 1)
    refine ⟨h1N, ?_⟩
    rw [h1N, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (prop5_incompleteness_of_dogmatic_truncation (τ.hP k) (τ.hΩ k)).2.1
  exact ⟨hStageAp, fun k => ⟨hBhatSq k, hBhatM k⟩, hAntiAll, hCumul⟩

/-! ### Phase V.2–V.3: Master Synthesis `Thm. Ω` (Stratum `6`) -/

/-- **`Thm. Ω` (Indefinite Reciprocal Totality — Stratum `6`)**:
Coagulation is uniquely realized in the undivided reciprocity involution `J_Ω := Σ₀ + B = 2 Ω - 1`,
achieving exact involutive completeness `J_Ω^2 = 1`, irreducibility to the egoic cut
`J_Ω ≠ Γ` (`[P, J_Ω] ≠ 0` under 2-torsion-freeness and `[P, Ω] ≠ 0`), and exact sector-wise
conservation of `(T, G, X, Y)`. -/
theorem thm_omega_indefinite_reciprocal_totality
    {P Ω : E} (hP : P * P = P) (hΩ : Ω * Ω = Ω) :
    dogmaticTruncation P Ω + doubledBridge P Ω = reciprocalTotality Ω ∧
    reciprocalTotality Ω * reciprocalTotality Ω = 1 ∧
    PeirceSpine.comm P (reciprocalTotality Ω) = 2 * PeirceSpine.comm P Ω ∧
    ((∀ Z : E, 2 * Z = 0 → Z = 0) → PeirceSpine.comm P Ω ≠ 0 →
      PeirceSpine.comm P (reciprocalTotality Ω) ≠ 0 ∧
        reciprocalTotality Ω ≠ polarityGamma P) ∧
    P * reciprocalTotality Ω * P = 2 * consciousThesis P Ω - P ∧
    shadowQ P * reciprocalTotality Ω * shadowQ P =
      2 * autonomousGround P Ω - shadowQ P ∧
    shadowQ P * reciprocalTotality Ω * P = 2 * outwardProj P Ω ∧
    P * reciprocalTotality Ω * shadowQ P = 2 * inwardIntrusion P Ω := by
  have h1 := prop1_orthogonality_and_polarity_involution hP
  have h2 := prop2_fourfold_decomp_and_nilpotency hP Ω
  have h5 := prop5_incompleteness_of_dogmatic_truncation hP hΩ
  have hSum : dogmaticTruncation P Ω + doubledBridge P Ω = reciprocalTotality Ω := by
    unfold dogmaticTruncation doubledBridge reciprocalTotality integrativeBridge
      consciousThesis autonomousGround outwardProj inwardIntrusion shadowQ
    calc
      (2 * (P * Ω * P) - P) + (2 * ((1 - P) * Ω * (1 - P)) - (1 - P)) +
          2 * ((1 - P) * Ω * P + P * Ω * (1 - P))
          = 2 * (P * Ω * P + (1 - P) * Ω * P + P * Ω * (1 - P) +
              (1 - P) * Ω * (1 - P)) - (P + (1 - P)) := by noncomm_ring
      _ = 2 * Ω - 1 := by
          have hD := h2.1
          unfold consciousThesis outwardProj inwardIntrusion autonomousGround shadowQ at hD
          rw [← hD]
          noncomm_ring
  have hJ2 : reciprocalTotality Ω * reciprocalTotality Ω = 1 := by
    rw [← hSum]
    have hOne := h5.2.2.1
    have hSig2 :
        dogmaticTruncation P Ω * dogmaticTruncation P Ω +
          doubledBridge P Ω * doubledBridge P Ω = 1 := by
      rw [← hOne]
      noncomm_ring
    calc
      (dogmaticTruncation P Ω + doubledBridge P Ω) *
          (dogmaticTruncation P Ω + doubledBridge P Ω)
          = (dogmaticTruncation P Ω * dogmaticTruncation P Ω +
                doubledBridge P Ω * doubledBridge P Ω) +
              (dogmaticTruncation P Ω * doubledBridge P Ω +
                doubledBridge P Ω * dogmaticTruncation P Ω) := by noncomm_ring
      _ = 1 + 0 := by rw [hSig2, h5.1]
      _ = 1 := add_zero 1
  have hCommJ : PeirceSpine.comm P (reciprocalTotality Ω) = 2 * PeirceSpine.comm P Ω := by
    unfold PeirceSpine.comm reciprocalTotality
    noncomm_ring
  have hIrred :
      (∀ Z : E, 2 * Z = 0 → Z = 0) → PeirceSpine.comm P Ω ≠ 0 →
        PeirceSpine.comm P (reciprocalTotality Ω) ≠ 0 ∧
          reciprocalTotality Ω ≠ polarityGamma P := by
    intro hTors hPO
    have hPJne : PeirceSpine.comm P (reciprocalTotality Ω) ≠ 0 := by
      intro h0
      rw [hCommJ] at h0
      exact hPO (hTors _ h0)
    have hJneG : reciprocalTotality Ω ≠ polarityGamma P := by
      intro heq
      apply hPJne
      rw [heq]
      exact h1.2.2.2.2.2.2.2.2.2
    exact ⟨hPJne, hJneG⟩
  have hPJP : P * reciprocalTotality Ω * P = 2 * consciousThesis P Ω - P := by
    unfold reciprocalTotality consciousThesis
    calc
      P * (2 * Ω - 1) * P = 2 * (P * Ω * P) - P * P := by noncomm_ring
      _ = 2 * (P * Ω * P) - P := by rw [hP]
  have hQJQ :
      shadowQ P * reciprocalTotality Ω * shadowQ P =
        2 * autonomousGround P Ω - shadowQ P := by
    unfold reciprocalTotality autonomousGround
    calc
      shadowQ P * (2 * Ω - 1) * shadowQ P
          = 2 * (shadowQ P * Ω * shadowQ P) - shadowQ P * shadowQ P := by noncomm_ring
      _ = 2 * (shadowQ P * Ω * shadowQ P) - shadowQ P := by rw [h1.1]
  have hQJP : shadowQ P * reciprocalTotality Ω * P = 2 * outwardProj P Ω := by
    unfold reciprocalTotality outwardProj
    calc
      shadowQ P * (2 * Ω - 1) * P
          = 2 * (shadowQ P * Ω * P) - shadowQ P * P := by noncomm_ring
      _ = 2 * (shadowQ P * Ω * P) := by rw [h1.2.2.1, sub_zero]
  have hPJQ : P * reciprocalTotality Ω * shadowQ P = 2 * inwardIntrusion P Ω := by
    unfold reciprocalTotality inwardIntrusion
    calc
      P * (2 * Ω - 1) * shadowQ P
          = 2 * (P * Ω * shadowQ P) - P * shadowQ P := by noncomm_ring
      _ = 2 * (P * Ω * shadowQ P) := by rw [h1.2.1, sub_zero]
  exact ⟨hSum, hJ2, hCommJ, hIrred, hPJP, hQJQ, hQJP, hPJQ⟩

end RingOperators

/-! ### Phase V.1: Acyclic Causal Poset `(P, ≺)` Across Strata `0..6` -/

/-- The finite set of extracted archetypes `P` across Strata `0..6` of `PHASE V.1`. -/
inductive CoagulaNode where
  | N0_Omega
  | N1a_ThesisP
  | N1b_ShadowQ
  | N1c_PolarityGamma
  | N2a_ConsistencyT
  | N2b_OutwardX
  | N2c_InwardY
  | N2d_AutonomousG
  | N3a_Holonomies
  | N3b_BridgeF
  | N3c_GravityM
  | N3d_TensionK
  | N4a_AporiaA0
  | N4b_TruncationSigma0
  | N5_MetaTower
  | N6_ReciprocalJOmega
  deriving DecidableEq, Repr, Inhabited

/-- Primary stratum index (`0..6`) of each node in `(P, ≺)`. -/
def stratum : CoagulaNode → ℕ
  | .N0_Omega => 0
  | .N1a_ThesisP => 1
  | .N1b_ShadowQ => 1
  | .N1c_PolarityGamma => 1
  | .N2a_ConsistencyT => 2
  | .N2b_OutwardX => 2
  | .N2c_InwardY => 2
  | .N2d_AutonomousG => 2
  | .N3a_Holonomies => 3
  | .N3b_BridgeF => 3
  | .N3c_GravityM => 3
  | .N3d_TensionK => 3
  | .N4a_AporiaA0 => 4
  | .N4b_TruncationSigma0 => 4
  | .N5_MetaTower => 5
  | .N6_ReciprocalJOmega => 6

/-- Fine lexicographic topological rank witnessing strict cover monotonicity. -/
def topoRank : CoagulaNode → ℕ
  | .N0_Omega => 0
  | .N1a_ThesisP => 1
  | .N1b_ShadowQ => 2
  | .N1c_PolarityGamma => 3
  | .N2a_ConsistencyT => 4
  | .N2b_OutwardX => 4
  | .N2c_InwardY => 4
  | .N2d_AutonomousG => 4
  | .N3a_Holonomies => 5
  | .N3b_BridgeF => 5
  | .N3c_GravityM => 6
  | .N3d_TensionK => 7
  | .N4a_AporiaA0 => 8
  | .N4b_TruncationSigma0 => 8
  | .N5_MetaTower => 9
  | .N6_ReciprocalJOmega => 10

/-- The complete cover relation `u ≺_cov v` specifying `(P, ≺)` in `PHASE V.1`. -/
inductive CoagulaCovers : CoagulaNode → CoagulaNode → Prop where
  | omega_to_P : CoagulaCovers .N0_Omega .N1a_ThesisP
  | P_to_Q : CoagulaCovers .N1a_ThesisP .N1b_ShadowQ
  | P_to_Gamma : CoagulaCovers .N1a_ThesisP .N1c_PolarityGamma
  | Q_to_Gamma : CoagulaCovers .N1b_ShadowQ .N1c_PolarityGamma
  | omega_to_T : CoagulaCovers .N0_Omega .N2a_ConsistencyT
  | P_to_T : CoagulaCovers .N1a_ThesisP .N2a_ConsistencyT
  | omega_to_X : CoagulaCovers .N0_Omega .N2b_OutwardX
  | P_to_X : CoagulaCovers .N1a_ThesisP .N2b_OutwardX
  | Q_to_X : CoagulaCovers .N1b_ShadowQ .N2b_OutwardX
  | omega_to_Y : CoagulaCovers .N0_Omega .N2c_InwardY
  | P_to_Y : CoagulaCovers .N1a_ThesisP .N2c_InwardY
  | Q_to_Y : CoagulaCovers .N1b_ShadowQ .N2c_InwardY
  | omega_to_G : CoagulaCovers .N0_Omega .N2d_AutonomousG
  | Q_to_G : CoagulaCovers .N1b_ShadowQ .N2d_AutonomousG
  | X_to_hol : CoagulaCovers .N2b_OutwardX .N3a_Holonomies
  | Y_to_hol : CoagulaCovers .N2c_InwardY .N3a_Holonomies
  | X_to_F : CoagulaCovers .N2b_OutwardX .N3b_BridgeF
  | Y_to_F : CoagulaCovers .N2c_InwardY .N3b_BridgeF
  | hol_to_M : CoagulaCovers .N3a_Holonomies .N3c_GravityM
  | F_to_M : CoagulaCovers .N3b_BridgeF .N3c_GravityM
  | hol_to_K : CoagulaCovers .N3a_Holonomies .N3d_TensionK
  | Gamma_to_K : CoagulaCovers .N1c_PolarityGamma .N3d_TensionK
  | M_to_K : CoagulaCovers .N3c_GravityM .N3d_TensionK
  | T_to_A0 : CoagulaCovers .N2a_ConsistencyT .N4a_AporiaA0
  | hol_to_A0 : CoagulaCovers .N3a_Holonomies .N4a_AporiaA0
  | T_to_Sigma0 : CoagulaCovers .N2a_ConsistencyT .N4b_TruncationSigma0
  | G_to_Sigma0 : CoagulaCovers .N2d_AutonomousG .N4b_TruncationSigma0
  | P_to_Sigma0 : CoagulaCovers .N1a_ThesisP .N4b_TruncationSigma0
  | Q_to_Sigma0 : CoagulaCovers .N1b_ShadowQ .N4b_TruncationSigma0
  | M_to_Sigma0 : CoagulaCovers .N3c_GravityM .N4b_TruncationSigma0
  | A0_to_tower : CoagulaCovers .N4a_AporiaA0 .N5_MetaTower
  | Gamma_to_tower : CoagulaCovers .N1c_PolarityGamma .N5_MetaTower
  | F_to_tower : CoagulaCovers .N3b_BridgeF .N5_MetaTower
  | Sigma0_to_J : CoagulaCovers .N4b_TruncationSigma0 .N6_ReciprocalJOmega
  | F_to_J : CoagulaCovers .N3b_BridgeF .N6_ReciprocalJOmega
  | tower_to_J : CoagulaCovers .N5_MetaTower .N6_ReciprocalJOmega

theorem coagulaCovers_stratum_mono {a b : CoagulaNode} (h : CoagulaCovers a b) :
    stratum a ≤ stratum b := by
  cases h <;> decide

theorem coagulaCovers_topoRank_strictMono {a b : CoagulaNode} (h : CoagulaCovers a b) :
    topoRank a < topoRank b := by
  cases h <;> decide

theorem coagulaCovers_transGen_topoRank_strictMono {a b : CoagulaNode}
    (h : Relation.TransGen CoagulaCovers a b) : topoRank a < topoRank b := by
  induction h with
  | single hab => exact coagulaCovers_topoRank_strictMono hab
  | tail _ hbc ih => exact Nat.lt_trans ih (coagulaCovers_topoRank_strictMono hbc)

/-- Causal reachability along `(P, ≺)` is strictly irreflexive. -/
theorem coagulaCovers_irreflexive (a : CoagulaNode) :
    ¬ Relation.TransGen CoagulaCovers a a := by
  intro h
  exact Nat.lt_irrefl (topoRank a) (coagulaCovers_transGen_topoRank_strictMono h)

/-- The causal poset `(P, ≺)` is strictly acyclic (`u ≺ v` and `v ≺ u` is impossible). -/
theorem coagulaCovers_acyclic {a b : CoagulaNode}
    (h1 : Relation.TransGen CoagulaCovers a b)
    (h2 : Relation.TransGen CoagulaCovers b a) : False :=
  Nat.lt_irrefl (topoRank a)
    (Nat.lt_trans (coagulaCovers_transGen_topoRank_strictMono h1)
      (coagulaCovers_transGen_topoRank_strictMono h2))

/-- Strict causal chain from Stratum `0` (`Ω`) to Stratum `6` (`J_Ω`). -/
theorem coagula_root_reaches_synthesis :
    Relation.TransGen CoagulaCovers .N0_Omega .N6_ReciprocalJOmega :=
  Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail
          (Relation.TransGen.single CoagulaCovers.omega_to_P)
          CoagulaCovers.P_to_X)
        CoagulaCovers.X_to_F)
      CoagulaCovers.F_to_tower)
    CoagulaCovers.tower_to_J

/-- Strictly ordered transitive relation induces a kernel `IsStrictOrder` on `CoagulaNode`. -/
instance : IsStrictOrder CoagulaNode (Relation.TransGen CoagulaCovers) where
  irrefl := coagulaCovers_irreflexive
  trans _ _ _ h1 h2 := Relation.TransGen.trans h1 h2

/-! ### Non-Vacuous `M_2(ℤ)` Realization of the Full Deductive Chain -/

/-- **Concrete `M_2(ℤ)` Realization Witness**:
Instantiates `Ax.1`–`Ax.3`, `Prop.1`–`Prop.5`, and `Thm. Ω` simultaneously on `(cutP0,
totalityOmega0)` inside `Matrix (Fin 2) (Fin 2) ℤ`, proving non-vanishing asymmetric
holonomies `A₀ = Y X ≠ X Y`, global defect `1 - Σ₀^2 = -8 I`, and `J_Ω^2 = 1`, `J_Ω ≠ Γ`. -/
theorem concrete_mat2Z_indefinite_reciprocal_totality_witness :
    cutP0 * cutP0 = cutP0 ∧
    totalityOmega0 * totalityOmega0 = totalityOmega0 ∧
    PeirceSpine.comm cutP0 totalityOmega0 ≠ 0 ∧
    socraticAporia cutP0 totalityOmega0 = !![-2, 0; 0, 0] ∧
    shadowAporia cutP0 totalityOmega0 = !![0, 0; 0, -2] ∧
    socraticAporia cutP0 totalityOmega0 ≠ shadowAporia cutP0 totalityOmega0 ∧
    1 - dogmaticTruncation cutP0 totalityOmega0 * dogmaticTruncation cutP0 totalityOmega0 =
      !![-8, 0; 0, -8] ∧
    reciprocalTotality totalityOmega0 = !![3, 2; -4, -3] ∧
    reciprocalTotality totalityOmega0 * reciprocalTotality totalityOmega0 = 1 ∧
    reciprocalTotality totalityOmega0 ≠ polarityGamma cutP0 := by
  have hP0 := cutP0_idem
  have hO0 := totalityOmega0_idem
  have hComm := cutP0_totalityOmega0_comm_ne_zero
  have h5 := prop5_incompleteness_of_dogmatic_truncation hP0 hO0
  have hOm := thm_omega_indefinite_reciprocal_totality hP0 hO0
  have hTors : ∀ Z : Matrix (Fin 2) (Fin 2) ℤ, 2 * Z = 0 → Z = 0 := by
    intro Z h2
    ext i j
    change Z i j = 0
    rw [two_mul] at h2
    have hij : Z i j + Z i j = 0 := by
      have h := congrFun (congrFun h2 i) j
      simpa using h
    omega
  have hIrred := hOm.2.2.2.1 hTors hComm
  have hA0 : socraticAporia cutP0 totalityOmega0 = !![-2, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [socraticAporia, consciousThesis, cutP0, totalityOmega0]
  have hG0 : shadowAporia cutP0 totalityOmega0 = !![0, 0; 0, -2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shadowAporia, autonomousGround, shadowQ, cutP0, totalityOmega0,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hNe : socraticAporia cutP0 totalityOmega0 ≠ shadowAporia cutP0 totalityOmega0 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    rw [hA0, hG0] at h00
    simp at h00
  have hDef :
      1 - dogmaticTruncation cutP0 totalityOmega0 * dogmaticTruncation cutP0 totalityOmega0 =
        !![-8, 0; 0, -8] := by
    have hM0 :
        substantiveGravity cutP0 totalityOmega0 =
          !![-2, 0; 0, 0] + !![0, 0; 0, -2] := by
      rw [← (prop4_exact_socratic_aporia hP0 hO0).2.2.1, hA0, hG0]
    have h4 :
        (4 : Matrix (Fin 2) (Fin 2) ℤ) * substantiveGravity cutP0 totalityOmega0 =
          substantiveGravity cutP0 totalityOmega0 +
            substantiveGravity cutP0 totalityOmega0 +
            substantiveGravity cutP0 totalityOmega0 +
            substantiveGravity cutP0 totalityOmega0 := by
      noncomm_ring
    rw [h5.2.2.2, h4, hM0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hJval : reciprocalTotality totalityOmega0 = !![3, 2; -4, -3] := by
    unfold reciprocalTotality
    rw [two_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [totalityOmega0]
  exact ⟨hP0, hO0, hComm, hA0, hG0, hNe, hDef, hJval, hOm.2.1, hIrred.2⟩

/-- Pointwise orthogonal stage cut `P_k` in `ℕ → M_2(ℤ)` (supported on slot `k`). -/
def seqCutP (k i : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if i = k then cutP0 else 0

/-- Pointwise orthogonal stage totality `Ω_k` in `ℕ → M_2(ℤ)` (supported on slot `k`). -/
def seqOmega (k i : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if i = k then totalityOmega0 else 0

private lemma doubledBridge_seq_eval {j i : ℕ} (h : i ≠ j) :
    doubledBridge (seqCutP j) (seqOmega j) i = 0 := by
  have hi : seqCutP j i = 0 := by simp [seqCutP, h]
  have ho : seqOmega j i = 0 := by simp [seqOmega, h]
  unfold doubledBridge integrativeBridge outwardProj inwardIntrusion shadowQ
  change 2 * ((1 - seqCutP j i) * seqOmega j i * seqCutP j i +
    seqCutP j i * seqOmega j i * (1 - seqCutP j i)) = 0
  rw [hi, ho]
  simp

private lemma polarityGamma_seq_eval {j i : ℕ} (h : i ≠ j) :
    polarityGamma (seqCutP j) i = (-1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hi : seqCutP j i = 0 := by simp [seqCutP, h]
  unfold polarityGamma shadowQ
  change seqCutP j i - (1 - seqCutP j i) = -1
  rw [hi]
  simp

/-- Constructive non-vacuous inhabitant of `MetaCognitiveTower` over `ℕ → M_2(ℤ)`. -/
def canonicalMetaCognitiveTower : MetaCognitiveTower (ℕ → Matrix (Fin 2) (Fin 2) ℤ) where
  P := seqCutP
  Ω := seqOmega
  hP k := by
    funext i
    by_cases h : i = k
    · subst h
      change seqCutP i i * seqCutP i i = seqCutP i i
      simp [seqCutP, cutP0_idem]
    · change seqCutP k i * seqCutP k i = seqCutP k i
      simp [seqCutP, h]
  hΩ k := by
    funext i
    by_cases h : i = k
    · subst h
      change seqOmega i i * seqOmega i i = seqOmega i i
      simp [seqOmega, totalityOmega0_idem]
    · change seqOmega k i * seqOmega k i = seqOmega k i
      simp [seqOmega, h]
  gamma_comm j k hjk := by
    funext i
    by_cases hij : i = j
    · subst hij
      change polarityGamma (seqCutP i) i * polarityGamma (seqCutP k) i =
        polarityGamma (seqCutP k) i * polarityGamma (seqCutP i) i
      rw [polarityGamma_seq_eval hjk]
      simp [mul_neg, neg_mul]
    · change polarityGamma (seqCutP j) i * polarityGamma (seqCutP k) i =
        polarityGamma (seqCutP k) i * polarityGamma (seqCutP j) i
      rw [polarityGamma_seq_eval hij]
      simp [neg_mul, mul_neg]
  gamma_bridge_comm j k hjk := by
    funext i
    by_cases hik : i = k
    · subst hik
      change polarityGamma (seqCutP j) i * doubledBridge (seqCutP i) (seqOmega i) i =
        doubledBridge (seqCutP i) (seqOmega i) i * polarityGamma (seqCutP j) i
      rw [polarityGamma_seq_eval (Ne.symm hjk)]
      simp [neg_mul, mul_neg]
    · change polarityGamma (seqCutP j) i * doubledBridge (seqCutP k) (seqOmega k) i =
        doubledBridge (seqCutP k) (seqOmega k) i * polarityGamma (seqCutP j) i
      rw [doubledBridge_seq_eval hik]
      simp
  bridge_comm j k hjk := by
    funext i
    by_cases hij : i = j
    · subst hij
      change doubledBridge (seqCutP i) (seqOmega i) i *
          doubledBridge (seqCutP k) (seqOmega k) i =
        doubledBridge (seqCutP k) (seqOmega k) i *
          doubledBridge (seqCutP i) (seqOmega i) i
      rw [doubledBridge_seq_eval hjk]
      simp
    · change doubledBridge (seqCutP j) (seqOmega j) i *
          doubledBridge (seqCutP k) (seqOmega k) i =
        doubledBridge (seqCutP k) (seqOmega k) i *
          doubledBridge (seqCutP j) (seqOmega j) i
      rw [doubledBridge_seq_eval hij]
      simp

instance : Inhabited (MetaCognitiveTower (ℕ → Matrix (Fin 2) (Fin 2) ℤ)) :=
  ⟨canonicalMetaCognitiveTower⟩

/-- Every finite stage `k` and cumulative tower sum `D_N` of `canonicalMetaCognitiveTower`
is genuinely non-commutative, non-aporetic-free (`A_k ≠ 0`), and carries non-vanishing
substantive gravity `D_N^2 k = !![-8, 0; 0, -8] ≠ 0`. -/
theorem canonicalMetaCognitiveTower_nontrivial (N k : ℕ) (hk : k ≤ N) :
    PeirceSpine.comm (canonicalMetaCognitiveTower.P k)
        (canonicalMetaCognitiveTower.Ω k) ≠ 0 ∧
    socraticAporia (canonicalMetaCognitiveTower.P k) (canonicalMetaCognitiveTower.Ω k) ≠ 0 ∧
    (cumulativeMetaOp canonicalMetaCognitiveTower.P canonicalMetaCognitiveTower.Ω N *
        cumulativeMetaOp canonicalMetaCognitiveTower.P canonicalMetaCognitiveTower.Ω N) k =
      !![-8, 0; 0, -8] := by
  have hComm :
      PeirceSpine.comm (canonicalMetaCognitiveTower.P k)
        (canonicalMetaCognitiveTower.Ω k) ≠ 0 := by
    intro h
    have hk0 : PeirceSpine.comm (seqCutP k) (seqOmega k) k = 0 := congrFun h k
    apply cutP0_totalityOmega0_comm_ne_zero
    unfold PeirceSpine.comm at hk0 ⊢
    simpa [seqCutP, seqOmega] using hk0
  have hAp :
      socraticAporia (canonicalMetaCognitiveTower.P k)
        (canonicalMetaCognitiveTower.Ω k) ≠ 0 := by
    intro h
    have hk0 : socraticAporia (seqCutP k) (seqOmega k) k = 0 := congrFun h k
    have hMat := concrete_mat2Z_indefinite_reciprocal_totality_witness.2.2.2.1
    have hEq : socraticAporia cutP0 totalityOmega0 = 0 := by
      unfold socraticAporia consciousThesis at hk0 ⊢
      simpa [seqCutP, seqOmega] using hk0
    rw [hMat] at hEq
    have h00 := congrFun (congrFun hEq 0) 0
    simp at h00
  have h6 := prop6_parity_soldered_metacognitive_coherence canonicalMetaCognitiveTower
  have hDN := (h6.2.2.2 N).2
  have hDef :
      1 - dogmaticTruncation cutP0 totalityOmega0 * dogmaticTruncation cutP0 totalityOmega0 =
        !![-8, 0; 0, -8] :=
    concrete_mat2Z_indefinite_reciprocal_totality_witness.2.2.2.2.2.2.1
  have hGrav0 :
      (4 : Matrix (Fin 2) (Fin 2) ℤ) * substantiveGravity cutP0 totalityOmega0 =
        !![-8, 0; 0, -8] := by
    rw [← (prop5_incompleteness_of_dogmatic_truncation cutP0_idem totalityOmega0_idem).2.2.2]
    exact hDef
  have hSumEval :
      (∑ j ∈ Finset.range (N + 1),
        substantiveGravity (canonicalMetaCognitiveTower.P j)
          (canonicalMetaCognitiveTower.Ω j)) k =
        substantiveGravity cutP0 totalityOmega0 := by
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · unfold canonicalMetaCognitiveTower substantiveGravity outwardProj inwardIntrusion shadowQ
      simp [seqCutP, seqOmega]
    · intro j _ hjk
      have hk_ne : k ≠ j := hjk.symm
      have h0 : seqCutP j k = 0 := by simp [seqCutP, hk_ne]
      have ho0 : seqOmega j k = 0 := by simp [seqOmega, hk_ne]
      unfold canonicalMetaCognitiveTower substantiveGravity outwardProj inwardIntrusion shadowQ
      simp [h0, ho0]
    · intro hkmem
      exfalso
      exact hkmem (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hEval :
      (cumulativeMetaOp canonicalMetaCognitiveTower.P canonicalMetaCognitiveTower.Ω N *
          cumulativeMetaOp canonicalMetaCognitiveTower.P canonicalMetaCognitiveTower.Ω N) k =
        !![-8, 0; 0, -8] := by
    rw [hDN]
    change (4 : Matrix (Fin 2) (Fin 2) ℤ) *
        (∑ j ∈ Finset.range (N + 1),
          substantiveGravity (canonicalMetaCognitiveTower.P j)
            (canonicalMetaCognitiveTower.Ω j)) k =
      !![-8, 0; 0, -8]
    rw [hSumEval, hGrav0]
  exact ⟨hComm, hAp, hEval⟩

end InfoGeometry.OperatorAlgebra.IndefiniteReciprocalTotalityPoset
