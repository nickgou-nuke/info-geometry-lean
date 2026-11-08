/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset
import InfoGeometry.Algebra.Zorn.ZeemanChiralGatedAssociatorPoset
import InfoGeometry.Canonical.ExteriorEvenTraceChernWeil
import InfoGeometry.NCG.BlockSupermatrixGradedTrace
import InfoGeometry.GrandUnification.MoebiusTomitaPacket
import InfoGeometry.GrandUnification.AnomalyInflow
import InfoGeometry.GrandUnification.ModularHamiltonian
import InfoGeometry.GrandUnification.BulkBoundaryCorrespondence
import InfoGeometry.GrandUnification.CantorTypeDBitwordLimit
import InfoGeometry.NCG.NoncommutativeConnectionCurvature
import InfoGeometry.Canonical.Pin55ColimitAnomalyBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.PeirceMaurerCartanCurvatureWitness
import InfoGeometry.OperatorAlgebra.PeirceSpine.InnerPullback
import InfoGeometry.OperatorAlgebra.PeirceSpine.SandwichCharge
import InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus
import InfoGeometry.QuantumContext.AharonovTwoStateSphereTime
import InfoGeometry.Topology.AharonovBohmVortices

open InfoGeometry.GrandUnification.CantorTypeDBitwordLimit
open InfoGeometry.GrandUnification.Dynamics

/-!
# Bridge: DeWitt Split Tetractys $\otimes$ Zeeman Chiral-Gated Zorn Nambu Associator ($\mathfrak{TZ}_1 \prec \dots \prec \mathfrak{TZ}_5$)

## i. Overview

This module establishes the exact algebraic bridge between the **Real DeWitt Split Tetractys**
(`InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset` /
`InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys`) and the **Zeeman Chiral-Gated Zorn
Associator Poset** (`InfoGeometry.Algebra.Zorn.ZeemanChiralGatedAssociatorPoset`) over any
unital associative ring `B` with a Peirce idempotent $P^2 = P$:

1. **Stage $\mathfrak{TZ}_1$ (Universal Peirce–Tetractys Zorn Triad $\langle N_+, N_-, P \rangle$ & Cubic Nambu Law):**
   For any $P^2 = P$ and $A, C \in B$, the ordered three-vector
   $$\mathcal{T}_{\mathrm{Peirce}}(P, A, C) := \langle N_+, N_-, P \rangle
     = \langle P A (1 - P),\, (1 - P) C P,\, P \rangle$$
   in `NoncommutativeZornNambu.Vec3 B` has self-cross product
   $$\mathcal{T}_{\mathrm{Peirce}} \times \mathcal{T}_{\mathrm{Peirce}}
     = \langle N_-, N_+, \Sigma(P, A, C) \rangle$$
   and cubic Nambu volume
   $$\mathrm{nambu}\big(\mathcal{T}_{\mathrm{Peirce}}(P, A, C)\big)
     = (1 + P)\,V(P, A, C) = V(P, A, C) + N_+ N_-.$$
   When the DeWitt bridge $\Phi = N_+ + N_-$ is normalized ($\Phi^2 = V = 1$), this reduces over
   any ring `B` to $\mathrm{nambu}\big(\mathcal{T}_{\mathrm{Peirce}}(P, W, W)\big) = 1 + P$.
2. **Stage $\mathfrak{TZ}_2$ (Cartan-Graded DeWitt Triad $\langle N_+, N_-, S_P \rangle$ & $\mathfrak{sl}_2$ Casimir Identity):**
   Replacing $P$ by the DeWitt Cartan grading involution $S_P = \mathrm{invS}(P) = P - (1 - P)$
   yields the Cartan triad $\mathcal{T}_{\mathrm{Cartan}}(P, A, C) := \langle N_+, N_-, S_P \rangle$,
   whose self-cross product is $\langle 2N_-, 2N_+, \Sigma(P, A, C) \rangle$ and whose cubic Nambu
   volume is
   $$\mathrm{nambu}\big(\mathcal{T}_{\mathrm{Cartan}}(P, A, C)\big)
     = 3\,V(P, A, C)
     = S_P^2 V(P, A, C) + \Phi^2 - J^2,$$
   matching the Row-3 DeWitt $\mathfrak{sl}_2$ quadratic Casimir $S_P^2 + \Phi^2 - J^2 = 3I$ when $V = 1$.
3. **Stage $\mathfrak{TZ}_3$ (Row-3 DeWitt $\mathfrak{sl}_2$ Triad $\langle S_P, \Phi, J \rangle$ & Chiral-Gated vs. Racemic Zorn Associators):**
   Proves the exact cross-product commutator table of $\mathcal{T}_{\mathfrak{sl}_2}(P, A, C) := \langle S_P, \Phi, J \rangle$
   ($\mathcal{T}_{\mathfrak{sl}_2} \times \mathcal{T}_{\mathfrak{sl}_2} = \langle -2\Sigma, -2\Phi, 2J \rangle$)
   and shows that in `ZornNC B`, the ungated racemic state `psiCov r (tetractysPeirceTriad P A C)`
   has zero diagonal self-associator and zero supertrace, whereas its chiral beta-gated projection
   `chiralUpperProj (psiCov r (tetractysPeirceTriad P A C))` has diagonal self-associator
   $\langle (1 + P)V(P, A, C),\, 0,\, 0,\, -(1 + P)V(P, A, C) \rangle$.
4. **Stage $\mathfrak{TZ}_4$ (Peirce Eigenvalue Decomposition $(2P, 1 - P)$ & Nilpotent Cone Commutant):**
   Proves that the Peirce Nambu volume $1 + P$ acts on the upper Peirce corner $P$ with integer
   weight $2$ ($P(1 + P) = P + P$) and on the lower Peirce corner $1 - P$ with weight $1$
   ($(1 - P)(1 + P) = 1 - P$), while $V(P, A, C)$ commutes with both nilpotent Peirce cones $N_\pm$.
5. **Stage $\mathfrak{TZ}_5$ (Exact Identification of the $2 \times 2$ Integer DeWitt Tetractys with `ChiralNambuMatrixWitness`):**
   Proves that the $2 \times 2$ integer DeWitt Tetractys matrices `dtMatP0` and `dtMatPhi0`
   generate the exact noncommutative matrix witness `ChiralNambuMatrixWitness.pChiral`:
   `tetractysPeirceTriad dtMatP0 dtMatPhi0 dtMatPhi0 = pChiral` and
   `nambu pChiral = 1 + dtMatP0 = !![2, 0; 0, 1]`.

## ii. Three-Bucket Audit Classification

- **BUCKET 1 (Genuine Constructive Owner Declarations Kept & Proved):**
  - `TetractysZornBridgeStage` ($\mathfrak{TZ}_1 \prec \dots \prec \mathfrak{TZ}_5$), `rank`, `coverEdge`, `instDecidableRelCoverEdge`, `rank_injective`, `coverEdge_rank_step`, `coverEdge_strictMono`, `coverEdge_acyclic`, `poset_covering_chain`
  - `tetractysPeirceTriad`, `cross_tetractysPeirceTriad`, `nambu_tetractysPeirceTriad`, `nambu_tetractysPeirceTriad_normalized`, `tz1_peirce_tetractys_triad_cross_and_nambu_volume`
  - `tetractysCartanTriad`, `cross_tetractysCartanTriad`, `nambu_tetractysCartanTriad`, `nambu_tetractysCartanTriad_eq_casimir`, `tz2_cartan_tetractys_triad_and_sl2_casimir_identity`
  - `tetractysSl2Triad`, `cross_tetractysSl2Triad`, `nambu_tetractysSl2Triad`, `chiralGated_tetractysPeirceTriad_self_associator`, `tz3_sl2_triad_and_chiral_gated_tetractys_associator`
  - `peirce_corner_eigenvalues_of_one_add_P`, `tz4_peirce_eigenvalue_split_and_cone_commutant`
  - `dtMatP0_eq_e11_and_cones`, `tetractysPeirceTriad_dtMat_eq_pChiral`, `nambu_pChiral_eq_one_add_dtMatP0`, `tz5_finite_dewitt_tetractys_matrix_witness_bridge`, `tz5_master_tetractys_zeeman_zorn_associator_bridge`
- **BUCKET 2 (Conditional Ring-Theoretic Theorems from Explicit Idempotent Hypotheses):**
  - All `[Ring B]` theorems take explicit `hP : P * P = P` (and where normalized, `hPhi : genPhi P W W * genPhi P W W = 1`).
- **BUCKET 3 (Open Closure Debt):**
  - None (`0` `sorry`, `0` `admit`, `0` custom axioms, `0` vacuous wrappers).

## iii. Key results

- `TetractysZornBridgeStage` ($\mathfrak{TZ}_1 \prec \dots \prec \mathfrak{TZ}_5$)
- `tz1_peirce_tetractys_triad_cross_and_nambu_volume`
- `tz2_cartan_tetractys_triad_and_sl2_casimir_identity`
- `tz3_sl2_triad_and_chiral_gated_tetractys_associator`
- `tz4_peirce_eigenvalue_split_and_cone_commutant`
- `tz5_finite_dewitt_tetractys_matrix_witness_bridge`
- `tz5_master_tetractys_zeeman_zorn_associator_bridge`

## iv. Table of contents

- Section 0: The 5-Stage Tetractys–Zorn Bridge Poset ($\mathfrak{TZ}_1 \prec \dots \prec \mathfrak{TZ}_5$)
- Section 1 ($\mathfrak{TZ}_1$): Universal Peirce–Tetractys Zorn Triad $\langle N_+, N_-, P \rangle$ & Cubic Nambu Formula
- Section 2 ($\mathfrak{TZ}_2$): Cartan-Graded DeWitt Triad $\langle N_+, N_-, S_P \rangle$ & the $3V$ Casimir Law
- Section 3 ($\mathfrak{TZ}_3$): Row-3 DeWitt $\mathfrak{sl}_2$ Triad $\langle S_P, \Phi, J \rangle$ & Chiral-Gated Zorn Associator
- Section 4 ($\mathfrak{TZ}_4$): Peirce Corner Eigenvalue Split $(2P, 1 - P)$ & Nilpotent Cone Commutant
- Section 5 ($\mathfrak{TZ}_5$): Exact Identification with `ChiralNambuMatrixWitness` & Master Synthesis
-/

namespace InfoGeometry.Algebra.Zorn.TetractysZeemanZornAssociatorBridge

open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Parafermion.DeWittTetractysRealParafermionPoset
open InfoGeometry.Algebra.NoncommutativeZornNambu
open InfoGeometry.Algebra.Zorn.ZeemanChiralGatedAssociatorPoset

/-!
## Section 0: The 5-Stage Tetractys–Zorn Bridge Poset ($\mathfrak{TZ}_1 \prec \dots \prec \mathfrak{TZ}_5$)
-/

/-- The 5-stage causal poset connecting the DeWitt Split Tetractys to the Zeeman-gated
Zorn Nambu associator. -/
inductive TetractysZornBridgeStage : Type
  | tz1_peirce_tetractys_triad
  | tz2_cartan_casimir_triad
  | tz3_sl2_chiral_associator
  | tz4_peirce_eigenvalue_split
  | tz5_finite_matrix_witness_bridge
  deriving DecidableEq, Repr

namespace TetractysZornBridgeStage

/-- Strict integer rank $\mathfrak{TZ}_1 < \mathfrak{TZ}_2 < \mathfrak{TZ}_3 < \mathfrak{TZ}_4 < \mathfrak{TZ}_5$. -/
def rank : TetractysZornBridgeStage → ℕ
  | .tz1_peirce_tetractys_triad => 1
  | .tz2_cartan_casimir_triad => 2
  | .tz3_sl2_chiral_associator => 3
  | .tz4_peirce_eigenvalue_split => 4
  | .tz5_finite_matrix_witness_bridge => 5

/-- Covering edges of the 5-stage Hasse chain $\mathfrak{TZ}_1 \prec \dots \prec \mathfrak{TZ}_5$. -/
def coverEdge : TetractysZornBridgeStage → TetractysZornBridgeStage → Prop
  | .tz1_peirce_tetractys_triad, .tz2_cartan_casimir_triad => True
  | .tz2_cartan_casimir_triad, .tz3_sl2_chiral_associator => True
  | .tz3_sl2_chiral_associator, .tz4_peirce_eigenvalue_split => True
  | .tz4_peirce_eigenvalue_split, .tz5_finite_matrix_witness_bridge => True
  | _, _ => False

/-- Decidability of the covering relation `coverEdge`. -/
instance instDecidableRelCoverEdge : DecidableRel coverEdge := fun a b => by
  cases a <;> cases b <;> unfold coverEdge <;> infer_instance

/-- The stage rank map is strictly injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge increments `rank` by $1$. -/
theorem coverEdge_rank_step {a b : TetractysZornBridgeStage} (h : coverEdge a b) :
    rank b = rank a + 1 := by
  cases a <;> cases b <;> revert h <;> decide

/-- Every covering edge is strictly monotone in `rank`. -/
theorem coverEdge_strictMono {a b : TetractysZornBridgeStage} (h : coverEdge a b) :
    rank a < rank b := by
  have hstep := coverEdge_rank_step h
  omega

/-- No stage covers itself. -/
theorem coverEdge_acyclic (a : TetractysZornBridgeStage) : ¬ coverEdge a a := by
  intro h
  have hlt := coverEdge_strictMono h
  omega

/-- Complete 4-edge covering chain $\mathfrak{TZ}_1 \prec \mathfrak{TZ}_2 \prec \mathfrak{TZ}_3 \prec \mathfrak{TZ}_4 \prec \mathfrak{TZ}_5$. -/
theorem poset_covering_chain :
    coverEdge .tz1_peirce_tetractys_triad .tz2_cartan_casimir_triad ∧
    coverEdge .tz2_cartan_casimir_triad .tz3_sl2_chiral_associator ∧
    coverEdge .tz3_sl2_chiral_associator .tz4_peirce_eigenvalue_split ∧
    coverEdge .tz4_peirce_eigenvalue_split .tz5_finite_matrix_witness_bridge := by
  decide

end TetractysZornBridgeStage

/-!
## Section 1 ($\mathfrak{TZ}_1$): Universal Peirce–Tetractys Zorn Triad $\langle N_+, N_-, P \rangle$ & Cubic Nambu Formula
-/

section UniversalRingBridge

variable {B : Type*} [Ring B]

/-- The Peirce–Tetractys three-vector $\mathcal{T}_{\mathrm{Peirce}}(P, A, C) = \langle N_+, N_-, P \rangle$
in `NoncommutativeZornNambu.Vec3 B`. -/
def tetractysPeirceTriad (P A C : B) : NoncommutativeZornNambu.Vec3 B :=
  ⟨conePlus P A, coneMinus P C, P⟩

/-- Self-cross product of the Peirce–Tetractys triad:
$\langle N_+, N_-, P \rangle \times \langle N_+, N_-, P \rangle = \langle N_-, N_+, \Sigma(P, A, C) \rangle$. -/
theorem cross_tetractysPeirceTriad {P : B} (hP : P * P = P) (A C : B) :
    cross (tetractysPeirceTriad P A C) (tetractysPeirceTriad P A C) =
      ⟨coneMinus P C, conePlus P A, genSig P A C⟩ := by
  dsimp [tetractysPeirceTriad, cross, genSig, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  congr 1
  · peirce_nf hP
  · peirce_nf hP

/-- **Universal Peirce–Tetractys Cubic Nambu Law:**
For any idempotent $P^2 = P$ in an associative ring `B`, the cubic Nambu volume of
`tetractysPeirceTriad P A C` equals $(1 + P)\,V(P, A, C) = V(P, A, C) + N_+ N_-$. -/
theorem nambu_tetractysPeirceTriad {P : B} (hP : P * P = P) (A C : B) :
    nambu (tetractysPeirceTriad P A C) = (1 + P) * genV P A C ∧
    nambu (tetractysPeirceTriad P A C) =
      genV P A C + conePlus P A * coneMinus P C := by
  unfold nambu
  rw [cross_tetractysPeirceTriad hP]
  dsimp [tetractysPeirceTriad, dot, genV, genSig,
    InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  constructor <;> peirce_nf hP

/-- When the DeWitt bridge $\Phi = N_+ + N_-$ is normalized ($\Phi^2 = 1$), the cubic Nambu
volume of `tetractysPeirceTriad P W W` simplifies to $1 + P$. -/
theorem nambu_tetractysPeirceTriad_normalized
    {P W : B} (hP : P * P = P) (hPhi : genPhi P W W * genPhi P W W = 1) :
    nambu (tetractysPeirceTriad P W W) = 1 + P := by
  have hV : genV P W W = 1 := by
    rw [← (archetype_A3_nilpotent_cones_and_tetraktys_table hP W W).2.2.1, hPhi]
  rw [(nambu_tetractysPeirceTriad hP W W).1, hV, mul_one]

/-- **Stage $\mathfrak{TZ}_1$ Theorem:**
Packages the self-cross product, the general $(1 + P)\,V(P, A, C)$ Nambu formula, and the
normalized $1 + P$ reduction for `tetractysPeirceTriad`. -/
theorem tz1_peirce_tetractys_triad_cross_and_nambu_volume
    {P W : B} (hP : P * P = P) (hPhi : genPhi P W W * genPhi P W W = 1) (A C : B) :
    cross (tetractysPeirceTriad P A C) (tetractysPeirceTriad P A C) =
      ⟨coneMinus P C, conePlus P A, genSig P A C⟩ ∧
    nambu (tetractysPeirceTriad P A C) = (1 + P) * genV P A C ∧
    nambu (tetractysPeirceTriad P A C) =
      genV P A C + conePlus P A * coneMinus P C ∧
    nambu (tetractysPeirceTriad P W W) = 1 + P := by
  have hcross := cross_tetractysPeirceTriad hP A C
  have hnambu := nambu_tetractysPeirceTriad hP A C
  have hnorm := nambu_tetractysPeirceTriad_normalized hP hPhi
  exact ⟨hcross, hnambu.1, hnambu.2, hnorm⟩

/-!
## Section 2 ($\mathfrak{TZ}_2$): Cartan-Graded DeWitt Triad $\langle N_+, N_-, S_P \rangle$ & the $3V$ Casimir Law
-/

/-- The Cartan-graded DeWitt triad $\mathcal{T}_{\mathrm{Cartan}}(P, A, C) = \langle N_+, N_-, S_P \rangle$
with $S_P = \mathrm{invS}(P) = P - (1 - P)$. -/
def tetractysCartanTriad (P A C : B) : NoncommutativeZornNambu.Vec3 B :=
  ⟨conePlus P A, coneMinus P C, invS P⟩

/-- Self-cross product of the Cartan-graded DeWitt triad:
$\langle N_+, N_-, S_P \rangle \times \langle N_+, N_-, S_P \rangle = \langle 2N_-, 2N_+, \Sigma(P, A, C) \rangle$. -/
theorem cross_tetractysCartanTriad {P : B} (hP : P * P = P) (A C : B) :
    cross (tetractysCartanTriad P A C) (tetractysCartanTriad P A C) =
      ⟨coneMinus P C + coneMinus P C,
       conePlus P A + conePlus P A,
       genSig P A C⟩ := by
  dsimp [tetractysCartanTriad, cross, invS, genSig, InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  congr 1
  · peirce_nf hP
  · peirce_nf hP

/-- The cubic Nambu volume of the Cartan-graded DeWitt triad equals $3\,V(P, A, C)$. -/
theorem nambu_tetractysCartanTriad {P : B} (hP : P * P = P) (A C : B) :
    nambu (tetractysCartanTriad P A C) =
      genV P A C + genV P A C + genV P A C := by
  unfold nambu
  rw [cross_tetractysCartanTriad hP]
  dsimp [tetractysCartanTriad, dot, invS, genV, genSig,
    InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  peirce_nf hP

/-- **Cartan Triad Nambu Volume = DeWitt $\mathfrak{sl}_2$ Casimir:**
In any associative ring `B` with $P^2 = P$, the Nambu volume of `tetractysCartanTriad P A C`
equals the weighted DeWitt $\mathfrak{sl}_2$ quadratic Casimir
$S_P^2\,V(P, A, C) + \Phi(P, A, C)^2 - J(P, A, C)^2$. -/
theorem nambu_tetractysCartanTriad_eq_casimir {P : B} (hP : P * P = P) (A C : B) :
    nambu (tetractysCartanTriad P A C) =
      invS P * invS P * genV P A C +
        genPhi P A C * genPhi P A C -
        genJ P A C * genJ P A C := by
  rw [nambu_tetractysCartanTriad hP]
  have hS : invS P * invS P = 1 :=
    (archetype_A2_peirce_cartan_grading_and_tangent_closure hP P P).1
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP A C
  rw [hS, one_mul, hA3.2.2.1, hA3.2.2.2.1]
  abel

/-- **Stage $\mathfrak{TZ}_2$ Theorem:**
Unifies the Cartan-graded DeWitt triad self-cross product, the $3V$ Nambu volume law, and its
identification with the DeWitt $\mathfrak{sl}_2$ quadratic Casimir. -/
theorem tz2_cartan_tetractys_triad_and_sl2_casimir_identity
    {P : B} (hP : P * P = P) (A C : B) :
    cross (tetractysCartanTriad P A C) (tetractysCartanTriad P A C) =
      ⟨coneMinus P C + coneMinus P C,
       conePlus P A + conePlus P A,
       genSig P A C⟩ ∧
    nambu (tetractysCartanTriad P A C) =
      genV P A C + genV P A C + genV P A C ∧
    nambu (tetractysCartanTriad P A C) =
      invS P * invS P * genV P A C +
        genPhi P A C * genPhi P A C -
        genJ P A C * genJ P A C := by
  have hcross := cross_tetractysCartanTriad hP A C
  have hnambu := nambu_tetractysCartanTriad hP A C
  have hcas := nambu_tetractysCartanTriad_eq_casimir hP A C
  exact ⟨hcross, hnambu, hcas⟩

/-!
## Section 3 ($\mathfrak{TZ}_3$): Row-3 DeWitt $\mathfrak{sl}_2$ Triad $\langle S_P, \Phi, J \rangle$ & Chiral-Gated Zorn Associator
-/

/-- The Row-3 DeWitt $\mathfrak{sl}_2$ triad $\mathcal{T}_{\mathfrak{sl}_2}(P, A, C) = \langle S_P, \Phi, J \rangle$. -/
def tetractysSl2Triad (P A C : B) : NoncommutativeZornNambu.Vec3 B :=
  ⟨invS P, genPhi P A C, genJ P A C⟩

/-- Self-cross product of the Row-3 DeWitt $\mathfrak{sl}_2$ triad reproduces the $\mathfrak{sl}_2$
commutator table $\langle -2\Sigma,\, -2\Phi,\, 2J \rangle$. -/
theorem cross_tetractysSl2Triad {P : B} (hP : P * P = P) (A C : B) :
    cross (tetractysSl2Triad P A C) (tetractysSl2Triad P A C) =
      ⟨-(genSig P A C + genSig P A C),
       -(genPhi P A C + genPhi P A C),
       genJ P A C + genJ P A C⟩ := by
  dsimp [tetractysSl2Triad, cross, invS, genPhi, genJ, genSig,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm]
  congr 1
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

/-- The cubic Nambu volume of the Row-3 DeWitt $\mathfrak{sl}_2$ triad equals $-6\,V(P, A, C)$. -/
theorem nambu_tetractysSl2Triad {P : B} (hP : P * P = P) (A C : B) :
    nambu (tetractysSl2Triad P A C) =
      -(genV P A C + genV P A C + genV P A C +
        genV P A C + genV P A C + genV P A C) := by
  unfold nambu
  rw [cross_tetractysSl2Triad hP]
  dsimp [tetractysSl2Triad, dot, invS, genPhi, genJ, genSig, genV,
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm,
    InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm]
  peirce_nf hP

/-- **Chiral Beta-Gating of the Peirce–Tetractys State in `ZornNC B`:**
In `ZornNC B`, the ungated covariant state `psiCov r (tetractysPeirceTriad P A C)` has zero
diagonal self-associator and zero supertrace, whereas its chiral beta-gated upper projection
`chiralUpperProj (psiCov r (tetractysPeirceTriad P A C))` has diagonal self-associator
$\langle (1 + P)V(P, A, C),\, 0,\, 0,\, -(1 + P)V(P, A, C) \rangle$. -/
theorem chiralGated_tetractysPeirceTriad_self_associator
    {P : B} (hP : P * P = P) (r A C : B) :
    superTrace
      (associator (psiCov r (tetractysPeirceTriad P A C))
        (psiCov r (tetractysPeirceTriad P A C))
        (psiCov r (tetractysPeirceTriad P A C))) = 0 ∧
    associator
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C)))
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C)))
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C))) =
      ⟨(1 + P) * genV P A C, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -((1 + P) * genV P A C)⟩ := by
  have hungated :=
    (psiCov_ungated_self_associator_diagonal_zero r (tetractysPeirceTriad P A C)).2.2
  have hgated :=
    (chiralGated_psiCov_self_associator r (tetractysPeirceTriad P A C)).1
  rw [(nambu_tetractysPeirceTriad hP A C).1] at hgated
  exact ⟨hungated, hgated⟩

/-- **Stage $\mathfrak{TZ}_3$ Theorem:**
Combines the Row-3 DeWitt $\mathfrak{sl}_2$ cross/Nambu identities with the chiral-gated
self-associator activation of `tetractysPeirceTriad`. -/
theorem tz3_sl2_triad_and_chiral_gated_tetractys_associator
    {P : B} (hP : P * P = P) (r A C : B) :
    cross (tetractysSl2Triad P A C) (tetractysSl2Triad P A C) =
      ⟨-(genSig P A C + genSig P A C),
       -(genPhi P A C + genPhi P A C),
       genJ P A C + genJ P A C⟩ ∧
    nambu (tetractysSl2Triad P A C) =
      -(genV P A C + genV P A C + genV P A C +
        genV P A C + genV P A C + genV P A C) ∧
    superTrace
      (associator (psiCov r (tetractysPeirceTriad P A C))
        (psiCov r (tetractysPeirceTriad P A C))
        (psiCov r (tetractysPeirceTriad P A C))) = 0 ∧
    associator
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C)))
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C)))
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C))) =
      ⟨(1 + P) * genV P A C, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -((1 + P) * genV P A C)⟩ := by
  have hcross := cross_tetractysSl2Triad hP A C
  have hnambu := nambu_tetractysSl2Triad hP A C
  have hgated := chiralGated_tetractysPeirceTriad_self_associator hP r A C
  exact ⟨hcross, hnambu, hgated.1, hgated.2⟩

/-!
## Section 4 ($\mathfrak{TZ}_4$): Peirce Corner Eigenvalue Split $(2P, 1 - P)$ & Nilpotent Cone Commutant
-/

/-- The normalized Peirce Nambu operator $1 + P$ acts with weight $2$ on the upper Peirce
idempotent $P$ ($P(1 + P) = P + P$) and with weight $1$ on the complementary idempotent
$1 - P$ ($(1 - P)(1 + P) = 1 - P$). -/
theorem peirce_corner_eigenvalues_of_one_add_P {P : B} (hP : P * P = P) :
    P * (1 + P) = P + P ∧
    (1 - P) * (1 + P) = 1 - P ∧
    P * (1 + P) + (1 - P) * (1 + P) = 1 + P := by
  refine ⟨?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Stage $\mathfrak{TZ}_4$ Theorem:**
When $\Phi^2 = 1$, the Peirce–Tetractys Nambu volume `nambu (tetractysPeirceTriad P W W) = 1 + P`
splits into weight $2$ on $P$ and weight $1$ on $1 - P$, while the Jordan mass $V(P, A, C)$
commutes with both nilpotent Peirce cones $N_+$ and $N_-$. -/
theorem tz4_peirce_eigenvalue_split_and_cone_commutant
    {P W : B} (hP : P * P = P) (hPhi : genPhi P W W * genPhi P W W = 1) (A C : B) :
    P * nambu (tetractysPeirceTriad P W W) = P + P ∧
    (1 - P) * nambu (tetractysPeirceTriad P W W) = 1 - P ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (conePlus P A) (genV P A C) = 0 ∧
    InfoGeometry.OperatorAlgebra.PeirceSpine.comm (coneMinus P C) (genV P A C) = 0 := by
  have hn := nambu_tetractysPeirceTriad_normalized hP hPhi
  have heig := peirce_corner_eigenvalues_of_one_add_P hP
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table hP A C
  rw [hn]
  exact ⟨heig.1, heig.2.1, hA3.2.2.2.2.2.2.2.2.2.2.2.1, hA3.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

end UniversalRingBridge

/-!
## Section 5 ($\mathfrak{TZ}_5$): Exact Identification with `ChiralNambuMatrixWitness` & Master Synthesis
-/

open InfoGeometry.Algebra.NoncommutativeZornNambu.InsertionMatrixWitness
open ChiralNambuMatrixWitness

/-- The $2 \times 2$ integer DeWitt projector `dtMatP0` and split bridge `dtMatPhi0` produce
the elementary matrix units `e₁₁`, `e₁₂`, and `e₂₁`. -/
theorem dtMatP0_eq_e11_and_cones :
    dtMatP0 = e₁₁ ∧
    conePlus dtMatP0 dtMatPhi0 = e₁₂ ∧
    coneMinus dtMatP0 dtMatPhi0 = e₂₁ := by
  refine ⟨rfl, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · ext i j
    fin_cases i <;> fin_cases j <;> decide

/-- **Exact Triad Identification:**
The universal Peirce–Tetractys triad `tetractysPeirceTriad` instantiated at the $2 \times 2$
integer DeWitt Tetractys `(dtMatP0, dtMatPhi0, dtMatPhi0)` is identically equal to the concrete
matrix witness `ChiralNambuMatrixWitness.pChiral = ⟨e₁₂, e₂₁, e₁₁⟩`. -/
theorem tetractysPeirceTriad_dtMat_eq_pChiral :
    tetractysPeirceTriad dtMatP0 dtMatPhi0 dtMatPhi0 = pChiral := by
  obtain ⟨hP0, hplus, hminus⟩ := dtMatP0_eq_e11_and_cones
  dsimp [tetractysPeirceTriad, pChiral]
  rw [hplus, hminus, hP0]

/-- Consequently, the cubic Nambu volume `nambu pChiral` of the concrete matrix witness equals
$1 + \mathrm{dtMatP0} = \begin{pmatrix} 2 & 0 \\ 0 & 1 \end{pmatrix}$. -/
theorem nambu_pChiral_eq_one_add_dtMatP0 :
    nambu pChiral = 1 + dtMatP0 := by
  have hP : dtMatP0 * dtMatP0 = dtMatP0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  have hPhi : genPhi dtMatP0 dtMatPhi0 dtMatPhi0 * genPhi dtMatP0 dtMatPhi0 dtMatPhi0 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← tetractysPeirceTriad_dtMat_eq_pChiral]
  exact nambu_tetractysPeirceTriad_normalized hP hPhi

/-- Explicit $2 \times 2$ integer matrix noncommutativity witness for `dtMatP0` and `dtMatPhi0`. -/
theorem dtMatP0_mul_dtMatPhi0_ne_comm :
    dtMatP0 * dtMatPhi0 ≠ dtMatPhi0 * dtMatP0 := by
  intro h
  have h01 := congr_fun (congr_fun h 0) 1
  revert h01
  decide

/-- **Stage $\mathfrak{TZ}_5$ Theorem:**
Certifies the exact specialization from the universal Peirce–Tetractys Nambu law to the
$2 \times 2$ integer matrix witness `ChiralNambuMatrixWitness.pChiral`. -/
theorem tz5_finite_dewitt_tetractys_matrix_witness_bridge :
    tetractysPeirceTriad dtMatP0 dtMatPhi0 dtMatPhi0 = pChiral ∧
    nambu pChiral = 1 + dtMatP0 ∧
    (nambu pChiral) 0 0 = 2 ∧
    (nambu pChiral) 1 1 = 1 ∧
    nambu pChiral ≠ 0 := by
  have hent := nambu_pChiral_diagonal_entries
  exact ⟨tetractysPeirceTriad_dtMat_eq_pChiral,
    nambu_pChiral_eq_one_add_dtMatP0,
    hent.1,
    hent.2,
    nambu_pChiral_ne_zero⟩

/-- **Master DeWitt Tetractys $\otimes$ Zeeman-Gated Zorn Associator Bridge ($\mathfrak{TZ}_1 \prec \dots \prec \mathfrak{TZ}_5$):**
Unifies the 5-stage covering poset with:
1. ($\mathfrak{TZ}_1$) Universal Peirce–Tetractys Nambu law $\mathrm{nambu}\langle N_+, N_-, P \rangle = (1 + P)V$;
2. ($\mathfrak{TZ}_2$) Cartan-graded DeWitt triad Nambu law $\mathrm{nambu}\langle N_+, N_-, S_P \rangle = 3V = S_P^2 V + \Phi^2 - J^2$;
3. ($\mathfrak{TZ}_3$) Row-3 DeWitt $\mathfrak{sl}_2$ triad cross-product table and chiral-gated vs. racemic Zorn associators;
4. ($\mathfrak{TZ}_4$) Peirce corner eigenvalue split $(2P, 1 - P)$ of $1 + P$;
5. ($\mathfrak{TZ}_5$) Exact specialization to the $2 \times 2$ integer DeWitt Tetractys matrix witness `pChiral`. -/
theorem tz5_master_tetractys_zeeman_zorn_associator_bridge
    {B : Type*} [Ring B] {P W : B}
    (hP : P * P = P) (hPhi : genPhi P W W * genPhi P W W = 1) (r A C : B) :
    (TetractysZornBridgeStage.coverEdge .tz1_peirce_tetractys_triad .tz2_cartan_casimir_triad ∧
     TetractysZornBridgeStage.coverEdge .tz2_cartan_casimir_triad .tz3_sl2_chiral_associator ∧
     TetractysZornBridgeStage.coverEdge .tz3_sl2_chiral_associator .tz4_peirce_eigenvalue_split ∧
     TetractysZornBridgeStage.coverEdge .tz4_peirce_eigenvalue_split .tz5_finite_matrix_witness_bridge) ∧
    (nambu (tetractysPeirceTriad P A C) = (1 + P) * genV P A C ∧
     nambu (tetractysPeirceTriad P W W) = 1 + P) ∧
    (nambu (tetractysCartanTriad P A C) =
      invS P * invS P * genV P A C +
        genPhi P A C * genPhi P A C -
        genJ P A C * genJ P A C) ∧
    (superTrace
      (associator (psiCov r (tetractysPeirceTriad P A C))
        (psiCov r (tetractysPeirceTriad P A C))
        (psiCov r (tetractysPeirceTriad P A C))) = 0 ∧
     associator
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C)))
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C)))
      (chiralUpperProj (psiCov r (tetractysPeirceTriad P A C))) =
      ⟨(1 + P) * genV P A C, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, -((1 + P) * genV P A C)⟩) ∧
    (P * nambu (tetractysPeirceTriad P W W) = P + P ∧
     (1 - P) * nambu (tetractysPeirceTriad P W W) = 1 - P) ∧
    (tetractysPeirceTriad dtMatP0 dtMatPhi0 dtMatPhi0 = pChiral ∧
     nambu pChiral = 1 + dtMatP0 ∧
     nambu pChiral ≠ 0) := by
  have hposet := TetractysZornBridgeStage.poset_covering_chain
  have htz1 := tz1_peirce_tetractys_triad_cross_and_nambu_volume hP hPhi A C
  have htz2 := nambu_tetractysCartanTriad_eq_casimir hP A C
  have htz3 := chiralGated_tetractysPeirceTriad_self_associator hP r A C
  have htz4 := tz4_peirce_eigenvalue_split_and_cone_commutant hP hPhi A C
  exact ⟨hposet,
    ⟨htz1.2.1, htz1.2.2.2⟩,
    htz2,
    htz3,
    ⟨htz4.1, htz4.2.1⟩,
    ⟨tetractysPeirceTriad_dtMat_eq_pChiral, nambu_pChiral_eq_one_add_dtMatP0, nambu_pChiral_ne_zero⟩⟩

/-- **Unified DeWitt Tetractys, Klein–Nishina Coincidence Cross-Ratio, Cayley Transform, & $^{60}\text{Co} \to {}^{60}\text{Ni}^*$ Zorn Cascade Time-Reversal Anomaly Bridge:**
Combines:
1. Universal Peirce–Tetractys Nambu volume $\mathrm{nambu}\langle N_+, N_-, P \rangle = (1 + P)V(P, A, C)$
   and operator Cayley transform recovery $(1 - U)(1 + S) = S + S$;
2. Multiplicative single-detector efficiency cancellation in the Klein–Nishina coincidence
   cross-ratio $CR = \frac{N_{12} N_{34}}{N_{14} N_{23}}$ and its native Zorn Cayley chiral
   asymmetry $\mathcal{A}_{\mathrm{chiral}} = \frac{CR - 1}{CR + 1}$;
3. Constructive 3-vector Zorn associator identity (`volume_is_associator`) and Time-Reversal
   symmetry breaking ($\Omega(-\vec{s}, \vec{e}_1, \vec{e}_2) \ne \Omega(\vec{s}, \vec{e}_1, \vec{e}_2)$)
   whenever the chiral-gated Zorn associator readout is non-zero. -/
theorem tz5_klein_nishina_cayley_zorn_cascade_time_reversal_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C S R : B) (hR : R * (1 + S) = 1)
    (ε1 ε3 η2 η4 M12 M34 M14 M23 : ℝ)
    (hε1 : ε1 ≠ 0) (hε3 : ε3 ≠ 0) (hη2 : η2 ≠ 0) (hη4 : η4 ≠ 0)
    (hden : M14 * M23 ≠ 0) (hCR : coincidenceCrossRatio M12 M34 M14 M23 + 1 ≠ 0)
    (a b c : ℝ) (s e1 e2 : NoncommutativeZornNambu.Vec3 ℝ) :
    (nambu (tetractysPeirceTriad P A C) = (1 + P) * genV P A C ∧
     (1 - (1 - S) * R) * (1 + S) = S + S) ∧
    (coincidenceCrossRatio
        (ε1 * η2 * M12) (ε3 * η4 * M34) (ε1 * η4 * M14) (ε3 * η2 * M23) =
      coincidenceCrossRatio M12 M34 M14 M23 ∧
     chiralCoincidenceAsymmetry
        (ε1 * η2 * M12) (ε3 * η4 * M34) (ε1 * η4 * M14) (ε3 * η2 * M23) =
      chiralCoincidenceAsymmetry M12 M34 M14 M23 ∧
     zornChiralSuperTrace
        (InfoGeometry.Algebra.Zorn.QuadraticCayleyDomain.nativeCayley
          (InfoGeometry.Algebra.Zorn.QuadraticCayleyDomain.diagonal
            (coincidenceCrossRatio M12 M34 M14 M23) 1)) =
      chiralCoincidenceAsymmetry M12 M34 M14 M23) ∧
    ((associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))).α = cascadeTripleVolume s e1 e2 ∧
     superTrace
      (associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))) = 2 * cascadeTripleVolume s e1 e2 ∧
     ((associator
        (chiralUpperProj (psiCov a s))
        (chiralUpperProj (psiCov b e1))
        (chiralUpperProj (psiCov c e2))).α ≠ 0 →
      cascadeTripleVolume (negVec3 s) e1 e2 ≠ cascadeTripleVolume s e1 e2) ∧
     cascadeTripleVolume (negVec3 spinEx) photonEy photonEz ≠
       cascadeTripleVolume spinEx photonEy photonEz) := by
  have hnambu := (nambu_tetractysPeirceTriad hP A C).1
  have hcayOp := (operator_cayley_transform_recovery S R hR).2.2.2
  have heff := coincidenceCrossRatio_efficiency_cancellation ε1 ε3 η2 η4 M12 M34 M14 M23
    hε1 hε3 hη2 hη4
  have hcayCR := (chiralCoincidenceAsymmetry_eq_cayley_of_crossRatio M12 M34 M14 M23 hden hCR).2.1
  have hvol := chiralGated_three_vector_associator_eq_triple_volume a b c s e1 e2
  have hdisc := zorn_cascade_associator_anomaly_breaks_time_reversal a b c s e1 e2
  exact ⟨⟨hnambu, hcayOp⟩,
    ⟨heff.1, heff.2, hcayCR⟩,
    ⟨hvol.2.2.1, hvol.2.2.2, hdisc.2.2.1, hdisc.2.2.2.2.2.2⟩⟩

/-- **Unified Peirce Error-Correction, Scalar Identity Noise Rejection, Coplanar Crosstalk Rejection, & $\mathrm{SL}(3)$ Unimodular Scaling Invariance Bridge:**
Combines all five layers of Section 7 of `ZeemanChiralGatedAssociatorPoset`:
1. Four-sector Peirce resolution of identity on `ZornNC R`;
2. Exact invariance of the Zorn associator under scalar identity noise `scalarIdZorn c`;
3. Annihilation of duplicated vector channels and invariance under coplanar crosstalk
   $\vec{s} \mapsto \vec{s} + \alpha\vec{e}_1 + \beta\vec{e}_2$, $\vec{e}_1 \mapsto \vec{e}_1 + \gamma\vec{e}_2$;
4. Opposite-chirality cancellation of `chiralUpperProj` and `chiralLowerProj` associators;
5. Exact $\mathrm{SL}(3, R)$ determinant-$1$ scaling invariance of the upper Peirce-gated Zorn associator. -/
theorem tz5_peirce_error_correction_and_sl3_scaling_invariance_bridge
    {R : Type*} [CommRing R]
    (A B C : ZornNC R) (c1 c2 c3 α β γ : R)
    (u v d s e1 e2 : NoncommutativeZornNambu.Vec3 R) (hdet : detScaleVec3 d = 1) :
    NoncommutativeZornNambu.add
      (NoncommutativeZornNambu.add (peirceUpperDiagProj A) (chiralUpperProj A))
      (NoncommutativeZornNambu.add (chiralLowerProj A) (peirceLowerDiagProj A)) = A ∧
    associator
      (NoncommutativeZornNambu.add A (scalarIdZorn c1))
      (NoncommutativeZornNambu.add B (scalarIdZorn c2))
      (NoncommutativeZornNambu.add C (scalarIdZorn c3)) =
      associator A B C ∧
    associator (pureUpper u) (pureUpper u) (pureUpper v) = (zeroZornNC : ZornNC R) ∧
    associator
      (pureUpper (addVec3 s (addVec3 (smulVec3 α e1) (smulVec3 β e2))))
      (pureUpper (addVec3 e1 (smulVec3 γ e2)))
      (pureUpper e2) =
      associator (pureUpper s) (pureUpper e1) (pureUpper e2) ∧
    NoncommutativeZornNambu.add
      (associator
        (chiralUpperProj (psiCov c1 s))
        (chiralUpperProj (psiCov c2 e1))
        (chiralUpperProj (psiCov c3 e2)))
      (associator
        (chiralLowerProj (psiCov c1 s))
        (chiralLowerProj (psiCov c2 e1))
        (chiralLowerProj (psiCov c3 e2))) = (zeroZornNC : ZornNC R) ∧
    associator
      (pureUpper (scaleVec3 d s))
      (pureUpper (scaleVec3 d e1))
      (pureUpper (scaleVec3 d e2)) =
      associator (pureUpper s) (pureUpper e1) (pureUpper e2) := by
  have hpeirce := (zorn_peirce_idempotent_orthogonal_decomposition A).2.2.2.2.2.2
  have hnoise := (zornAssociator_invariant_under_scalar_identity_noise A B C c1 c2 c3).2.2
  have hcross := zorn_peirce_coplanar_crosstalk_and_duplication_error_correction u v s e1 e2 α β γ
  have hrac := (zorn_racemic_cancellation_vs_peirce_gating c1 c2 c3 s e1 e2).2.2.2
  have hsl3 := (zorn_sl3_det_one_scaling_invariance d s e1 e2 hdet).2.2.1
  exact ⟨hpeirce, hnoise, hcross.1, hcross.2.2.2, hrac, hsl3⟩

/-!
## Section 6: Prima Materia Noncommutative Peirce Order-One, Plabic Master Index, Graded Maurer–Cartan Superbracket, & Non-Abelian Chern–Weil Synthesis
-/

open InfoGeometry.Canonical.ExteriorHomogeneousDegreeBridge
open InfoGeometry.Canonical.ExteriorGradedDerivationBridge
open InfoGeometry.NCG.BlockSupermatrixGradedTrace

/-- **Universal Noncommutative Order-One Commutator Symmetry:**
Over any associative (not necessarily commutative) ring `B`, the commutator `OperatorAlgebra.PeirceSpine.comm X Y = X * Y - Y * X`
satisfies the universal Jacobi identity
$$\mathrm{comm}(\mathrm{comm}(D, a), b) - \mathrm{comm}(\mathrm{comm}(D, b), a)
  = \mathrm{comm}(D, \mathrm{comm}(a, b)),$$
and therefore whenever `OperatorAlgebra.PeirceSpine.comm a b = 0`, `OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D a) b = OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D b) a` for every operator `D : B`. -/
theorem order_one_comm_symmetry {B : Type*} [Ring B] (D a b : B) :
    OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D a) b - OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D b) a =
      OperatorAlgebra.PeirceSpine.comm D (OperatorAlgebra.PeirceSpine.comm a b) ∧
    (OperatorAlgebra.PeirceSpine.comm a b = 0 →
      OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D a) b = OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D b) a) := by
  have hjac :
      OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D a) b - OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D b) a =
        OperatorAlgebra.PeirceSpine.comm D (OperatorAlgebra.PeirceSpine.comm a b) := by
    unfold OperatorAlgebra.PeirceSpine.comm
    noncomm_ring
  refine ⟨hjac, ?_⟩
  intro hab
  have hjac0 := hjac
  rw [hab] at hjac0
  have hD0 : OperatorAlgebra.PeirceSpine.comm D (0 : B) = 0 := by
    unfold OperatorAlgebra.PeirceSpine.comm
    simp
  rw [hD0] at hjac0
  exact sub_eq_zero.mp hjac0

/-- **Bipartite Peirce Sheet Order-One Commutator Theorem:**
Over any associative ring `B` with an idempotent $P^2 = P$, right-sheet operators $a = P X P$ and
left-sheet operators $b = (1 - P) Y (1 - P)$ mutually annihilate ($a b = 0$ and $b a = 0$), commute
($\mathrm{comm}(a, b) = 0$), and satisfy the Connes Order-One commutator symmetry
`OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D (P * X * P)) ((1 - P) * Y * (1 - P)) = OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D ((1 - P) * Y * (1 - P))) (P * X * P)`
for every operator $D \in B$. -/
theorem peirce_bipartite_sheet_order_one_symmetry {B : Type*} [Ring B]
    {P : B} (hP : P * P = P) (D X Y : B) :
    (P * X * P) * ((1 - P) * Y * (1 - P)) = 0 ∧
    ((1 - P) * Y * (1 - P)) * (P * X * P) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (P * X * P) ((1 - P) * Y * (1 - P)) = 0 ∧
    OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D (P * X * P)) ((1 - P) * Y * (1 - P)) =
      OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D ((1 - P) * Y * (1 - P))) (P * X * P) := by
  have hP_comp : P * (1 - P) = 0 := by
    calc
      P * (1 - P) = P - P * P := by noncomm_ring
      _ = P - P := by rw [hP]
      _ = 0 := sub_self P
  have hcomp_P : (1 - P) * P = 0 := by
    calc
      (1 - P) * P = P - P * P := by noncomm_ring
      _ = P - P := by rw [hP]
      _ = 0 := sub_self P
  have hab : (P * X * P) * ((1 - P) * Y * (1 - P)) = 0 := by
    calc
      (P * X * P) * ((1 - P) * Y * (1 - P))
        = (P * X) * (P * (1 - P)) * (Y * (1 - P)) := by noncomm_ring
      _ = (P * X) * 0 * (Y * (1 - P)) := by rw [hP_comp]
      _ = 0 := by simp
  have hba : ((1 - P) * Y * (1 - P)) * (P * X * P) = 0 := by
    calc
      ((1 - P) * Y * (1 - P)) * (P * X * P)
        = ((1 - P) * Y) * ((1 - P) * P) * (X * P) := by noncomm_ring
      _ = ((1 - P) * Y) * 0 * (X * P) := by rw [hcomp_P]
      _ = 0 := by simp
  have hcomm : OperatorAlgebra.PeirceSpine.comm (P * X * P) ((1 - P) * Y * (1 - P)) = 0 := by
    unfold OperatorAlgebra.PeirceSpine.comm
    rw [hab, hba, sub_self]
  exact ⟨hab, hba, hcomm, (order_one_comm_symmetry D _ _).2 hcomm⟩

/-- **Bipartite Plabic Graph Amplituhedron Master Index Tetrad:**
For any trivalent bipartite plabic graph with $3 V_B + 3 V_W = 2 E + n$ and helicity grade
$k = 2 V_B + V_W - E$, the topological index $2 k - n$ equals the bipartite color excess $V_B - V_W$,
and $V_B \ne V_W \iff 2 k \ne n$. -/
theorem amplituhedron_bipartite_master_index (V_B V_W E n k : ℤ)
    (h_trivalent : 3 * V_B + 3 * V_W = 2 * E + n)
    (h_helicity : k = 2 * V_B + V_W - E) :
    2 * k - n = V_B - V_W ∧ (V_B ≠ V_W ↔ 2 * k ≠ n) := by
  have hidx : 2 * k - n = V_B - V_W := by
    linarith [h_trivalent, h_helicity]
  refine ⟨hidx, ?_⟩
  omega

/-- The Maurer–Cartan curvature $F(\omega) := d\omega + \omega * \omega$ on `ExteriorAlgebra R V`. -/
def maurerCartanCurvature {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (d : Module.End R (ExteriorAlgebra R V)) (ω : ExteriorAlgebra R V) :
    ExteriorAlgebra R V :=
  d ω + ω * ω

/-- **Odd Graded Superbracket & Maurer–Cartan Curvature Identity:**
Using the repository's canonical `ringSuperbracket` (`InfoGeometry.NCG.BlockSupermatrixGradedTrace`):
1. For any $\omega \in \mathrm{ExteriorAlgebra}\,R\,V$, the odd-odd superbracket is
   $\mathrm{ringSuperbracket}\,.odd\,.odd\,\omega\,\omega = \omega * \omega + \omega * \omega = (2 : R) \bullet (\omega * \omega)$;
2. When $2$ is invertible in $R$, $(\operatorname{invOf} 2) \bullet \mathrm{ringSuperbracket}\,.odd\,.odd\,\omega\,\omega = \omega * \omega$,
   so the graded Maurer–Cartan curvature expression
   $d\omega + \tfrac{1}{2}[\omega, \omega]_{\mathrm{super}}$ equals `maurerCartanCurvature d ω = d ω + ω * ω`. -/
theorem ringSuperbracket_odd_self_and_maurerCartan
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (d : Module.End R (ExteriorAlgebra R V)) (ω : ExteriorAlgebra R V) :
    ringSuperbracket .odd .odd ω ω = ω * ω + ω * ω ∧
    ringSuperbracket .odd .odd ω ω = (2 : R) • (ω * ω) ∧
    ∀ [Invertible (2 : R)],
      (⅟(2 : R)) • ringSuperbracket .odd .odd ω ω = ω * ω ∧
      d ω + (⅟(2 : R)) • ringSuperbracket .odd .odd ω ω =
        maurerCartanCurvature d ω := by
  have h1 : ringSuperbracket .odd .odd ω ω = ω * ω + ω * ω := rfl
  have h2 : ringSuperbracket .odd .odd ω ω = (2 : R) • (ω * ω) := by
    rw [h1, two_smul]
  refine ⟨h1, h2, ?_⟩
  intro _
  have hhalf : (⅟(2 : R)) • ringSuperbracket .odd .odd ω ω = ω * ω := by
    rw [h2, smul_smul, invOf_mul_self, one_smul]
  refine ⟨hhalf, ?_⟩
  rw [hhalf, maurerCartanCurvature]

/-- **Pauli Exterior 1-Form Nilpotency, Odd Superbracket Vanishing, & Abelian Maurer–Cartan Reduction:**
For any vectors $u, v \in V$ and `D : ExteriorDifferentialData R V`
(`InfoGeometry.Canonical.ExteriorGradedDerivationBridge`):
1. $\iota_R(v)$ is homogeneous of exterior degree $1$ (`IsHomogeneousExteriorDegree 1 (ι R v)`);
2. $\iota_R(v) * \iota_R(v) = 0$ and $\iota_R(u) * \iota_R(v) + \iota_R(v) * \iota_R(u) = 0$;
3. The odd-odd superbrackets `ringSuperbracket .odd .odd (ι R v) (ι R v)` and
   `ringSuperbracket .odd .odd (ι R u) (ι R v)` vanish identically;
4. The Maurer–Cartan curvature `maurerCartanCurvature D.d (ι R v)` reduces to `D.d (ι R v)`
   and is strictly closed ($D.d(\mathrm{maurerCartanCurvature}\,D.d\,(\iota_R v)) = 0$). -/
theorem exterior_one_form_nilpotent_and_maurerCartan
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (D : ExteriorDifferentialData R V) (u v : V) :
    IsHomogeneousExteriorDegree 1 (ExteriorAlgebra.ι R v) ∧
    ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v = 0 ∧
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v +
      ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u = 0 ∧
    ringSuperbracket .odd .odd (ExteriorAlgebra.ι R v) (ExteriorAlgebra.ι R v) = 0 ∧
    ringSuperbracket .odd .odd (ExteriorAlgebra.ι R u) (ExteriorAlgebra.ι R v) = 0 ∧
    maurerCartanCurvature D.d (ExteriorAlgebra.ι R v) = D.d (ExteriorAlgebra.ι R v) ∧
    D.d (maurerCartanCurvature D.d (ExteriorAlgebra.ι R v)) = 0 := by
  have hdeg : IsHomogeneousExteriorDegree 1 (ExteriorAlgebra.ι R v) :=
    (homogeneous_one_iff_exists_generator (ExteriorAlgebra.ι R v)).mpr ⟨v, rfl⟩
  have hsq : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v = 0 :=
    ExteriorAlgebra.ι_sq_zero v
  have hanti :
      ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v +
        ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u = 0 := by
    have hsum : ExteriorAlgebra.ι R (u + v) * ExteriorAlgebra.ι R (u + v) = 0 :=
      ExteriorAlgebra.ι_sq_zero (u + v)
    rw [map_add, mul_add, add_mul, add_mul, ExteriorAlgebra.ι_sq_zero u,
      ExteriorAlgebra.ι_sq_zero v, zero_add, add_zero, add_comm] at hsum
    exact hsum
  have hsb_vv :
      ringSuperbracket .odd .odd (ExteriorAlgebra.ι R v) (ExteriorAlgebra.ι R v) = 0 := by
    change ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v +
      ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R v = 0
    rw [hsq, add_zero]
  have hsb_uv :
      ringSuperbracket .odd .odd (ExteriorAlgebra.ι R u) (ExteriorAlgebra.ι R v) = 0 := hanti
  have hmc :
      maurerCartanCurvature D.d (ExteriorAlgebra.ι R v) = D.d (ExteriorAlgebra.ι R v) := by
    simp [maurerCartanCurvature, hsq]
  refine ⟨hdeg, hsq, hanti, hsb_vv, hsb_uv, hmc, ?_⟩
  rw [hmc]
  exact differential_sq_zero D (ExteriorAlgebra.ι R v)

/-- **Graded Maurer–Cartan Bianchi Identity on `ExteriorAlgebra R V`:**
For any `D : ExteriorDifferentialData R V` (`InfoGeometry.Canonical.ExteriorGradedDerivationBridge`)
and any homogeneous 1-form $\omega \in \mathrm{ExteriorAlgebra}\,R\,V$ (`hω : IsHomogeneousExteriorDegree 1 ω`):
1. $D.d(\omega * \omega) = D.d \omega * \omega - \omega * D.d \omega$ (from `one_form_leibniz`);
2. $D.d(\mathrm{maurerCartanCurvature}\,D.d\,\omega) = D.d \omega * \omega - \omega * D.d \omega$;
3. **Graded Bianchi Identity:**
   $$D.d\big(\mathrm{maurerCartanCurvature}\,D.d\,\omega\big)
     + \mathrm{ringSuperbracket}\,.odd\,.even\,\omega\,\big(\mathrm{maurerCartanCurvature}\,D.d\,\omega\big) = 0;$$
4. Whenever $\omega$ satisfies the Maurer–Cartan flatness equation
   `maurerCartanCurvature D.d ω = 0` ($D.d \omega + \omega * \omega = 0$), we have
   $D.d \omega = -\omega * \omega$, $D.d(\mathrm{maurerCartanCurvature}\,D.d\,\omega) = 0$, and $D.d(\omega * \omega) = 0$. -/
theorem maurerCartanCurvature_graded_bianchi
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (D : ExteriorDifferentialData R V) (ω : ExteriorAlgebra R V)
    (hω : IsHomogeneousExteriorDegree 1 ω) :
    D.d (ω * ω) = D.d ω * ω - ω * D.d ω ∧
    D.d (maurerCartanCurvature D.d ω) = D.d ω * ω - ω * D.d ω ∧
    D.d (maurerCartanCurvature D.d ω) +
      ringSuperbracket .odd .even ω (maurerCartanCurvature D.d ω) = 0 ∧
    (maurerCartanCurvature D.d ω = 0 →
      D.d ω = -(ω * ω) ∧
      D.d (maurerCartanCurvature D.d ω) = 0 ∧
      D.d (ω * ω) = 0) := by
  have hd_sq : D.d (ω * ω) = D.d ω * ω - ω * D.d ω :=
    one_form_leibniz D ω ω hω
  have hd_mc : D.d (maurerCartanCurvature D.d ω) = D.d ω * ω - ω * D.d ω := by
    unfold maurerCartanCurvature
    rw [map_add, differential_sq_zero D ω, zero_add, hd_sq]
  have h_bianchi :
      D.d (maurerCartanCurvature D.d ω) +
        ringSuperbracket .odd .even ω (maurerCartanCurvature D.d ω) = 0 := by
    rw [hd_mc]
    unfold maurerCartanCurvature ringSuperbracket
    noncomm_ring
  refine ⟨hd_sq, hd_mc, h_bianchi, ?_⟩
  intro hflat
  have hd_ω : D.d ω = -(ω * ω) := eq_neg_of_add_eq_zero_left hflat
  have hd_flat : D.d (maurerCartanCurvature D.d ω) = 0 := by
    rw [hflat, map_zero]
  have hd_ω2 : D.d (ω * ω) = 0 := by
    rw [hd_sq, hd_ω]
    noncomm_ring
  exact ⟨hd_ω, hd_flat, hd_ω2⟩

/-- **Abelian Collapse of Scalar Homogeneous 1-Forms vs. Non-Abelian Matrix 1-Forms:**
In the scalar exterior algebra `ExteriorAlgebra R V`, every homogeneous degree-1 form
`ω` (`IsHomogeneousExteriorDegree 1 ω`) lies in the image of `ExteriorAlgebra.ι R`
(`homogeneous_one_iff_exists_generator`). Consequently, for every scalar homogeneous 1-form $\omega \in \bigwedge^1 V$:
1. $\omega * \omega = 0$ and $\mathrm{ringSuperbracket}\,.odd\,.odd\,\omega\,\omega = 0$ identically;
2. `maurerCartanCurvature D.d ω = D.d ω` (the quadratic Maurer–Cartan term $\tfrac{1}{2}[\omega, \omega]_{\mathrm{super}}$
   collapses to zero unless $\omega$ is tensored with a noncommutative matrix/Lie algebra or has mixed odd degrees). -/
theorem scalar_homogeneous_one_form_maurerCartan_abelian_collapse
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (D : ExteriorDifferentialData R V) (ω : ExteriorAlgebra R V)
    (hω : IsHomogeneousExteriorDegree 1 ω) :
    ω * ω = 0 ∧
    ringSuperbracket .odd .odd ω ω = 0 ∧
    maurerCartanCurvature D.d ω = D.d ω ∧
    D.d (maurerCartanCurvature D.d ω) = 0 := by
  rcases (homogeneous_one_iff_exists_generator ω).mp hω with ⟨v, rfl⟩
  have hex := exterior_one_form_nilpotent_and_maurerCartan D v v
  exact ⟨hex.2.1, hex.2.2.2.1, hex.2.2.2.2.2.1, hex.2.2.2.2.2.2⟩

/-- The $2 \times 2$ chiral off-diagonal matrix-valued 1-form connection
$$A_{\mathrm{chiral}}(u, v) = \begin{pmatrix} 0 & \iota_R(u) \\ \iota_R(v) & 0 \end{pmatrix}
  \in M_2(\mathrm{ExteriorAlgebra}\,R\,V),$$
whose matrix wedge-square is $\mathrm{diag}\big(\iota_R(u)\iota_R(v),\, -\iota_R(u)\iota_R(v)\big)$. -/
def chiralMatrixOneForm {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (u v : V) : Matrix (Fin 2) (Fin 2) (ExteriorAlgebra R V) :=
  !![0, ExteriorAlgebra.ι R u; ExteriorAlgebra.ι R v, 0]

/-- **Non-Abelian Matrix-Valued 1-Form Graded Maurer–Cartan Curvature, Chiral 2-Form Wedge Witness, & Covariant Bianchi Identity:**
1. On $M_2(\mathrm{ExteriorAlgebra}\,R\,V)$, `chiralMatrixOneForm u v` is entrywise homogeneous of degree $1$
   (`MatrixIsHomogeneous 1 (chiralMatrixOneForm u v)`), yet its matrix square is the diagonal 2-form matrix
   `!![ι R u * ι R v, 0; 0, -(ι R u * ι R v)]` and its odd matrix superbracket is
   `(2 : R) • !![ι R u * ι R v, 0; 0, -(ι R u * ι R v)]`;
2. On $M_n(\mathrm{ExteriorAlgebra}\,R\,V)$ over a field $R$ with `[Invertible (2 : R)]`, for any
   homogeneous 1-form connection matrix $A$ (`MatrixIsHomogeneous 1 A`) and `D : ExteriorDifferentialData R V`:
   - `matrixExteriorDerivative D.d A + (⅟(2 : R)) • ringSuperbracket .odd .odd A A = curvatureFromConnection D.d A`,
   - `matrixExteriorDerivative D.d (curvatureFromConnection D.d A) + ringSuperbracket .odd .even A (curvatureFromConnection D.d A) = covariantDerivative A D.d (curvatureFromConnection D.d A)`,
   - and this graded Bianchi expression vanishes identically (`= 0`). -/
theorem matrix_homogeneous_one_form_nonabelian_maurerCartan_and_chiral_witness
    {R V : Type*} [Field R] [Invertible (2 : R)] [AddCommGroup V] [Module R V] {n_mat : ℕ}
    (D : ExteriorDifferentialData R V) (u v : V)
    (A : Matrix (Fin n_mat) (Fin n_mat) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    MatrixIsHomogeneous 1 (chiralMatrixOneForm (R := R) u v) ∧
    chiralMatrixOneForm (R := R) u v * chiralMatrixOneForm (R := R) u v =
      !![ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v, 0;
         0, -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)] ∧
    ringSuperbracket .odd .odd (chiralMatrixOneForm (R := R) u v) (chiralMatrixOneForm (R := R) u v) =
      (2 : R) • !![ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v, 0;
                   0, -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)] ∧
    InfoGeometry.Canonical.MatrixTracedChernWeilBridge.matrixExteriorDerivative D.d A +
      (⅟(2 : R)) • ringSuperbracket .odd .odd A A =
      InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A ∧
    InfoGeometry.Canonical.MatrixTracedChernWeilBridge.matrixExteriorDerivative D.d
        (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) +
      ringSuperbracket .odd .even A
        (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) =
      InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge.covariantDerivative A D.d
        (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) ∧
    InfoGeometry.Canonical.MatrixTracedChernWeilBridge.matrixExteriorDerivative D.d
        (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) +
      ringSuperbracket .odd .even A
        (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) = 0 := by
  have hhom : MatrixIsHomogeneous 1 (chiralMatrixOneForm (R := R) u v) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [chiralMatrixOneForm]
    · exact Submodule.zero_mem _
    · exact (homogeneous_one_iff_exists_generator _).mpr ⟨u, rfl⟩
    · exact (homogeneous_one_iff_exists_generator _).mpr ⟨v, rfl⟩
    · exact Submodule.zero_mem _
  have hanti :
      ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u =
        -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) := by
    have h := (exterior_one_form_nilpotent_and_maurerCartan D u v).2.2.1
    exact eq_neg_of_add_eq_zero_right h
  have hsq :
      chiralMatrixOneForm (R := R) u v * chiralMatrixOneForm (R := R) u v =
        !![ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v, 0;
           0, -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [chiralMatrixOneForm, Matrix.mul_apply, Fin.sum_univ_two, hanti]
  have hsb_chiral :
      ringSuperbracket .odd .odd (chiralMatrixOneForm (R := R) u v) (chiralMatrixOneForm (R := R) u v) =
        (2 : R) • !![ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v, 0;
                     0, -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)] := by
    change chiralMatrixOneForm (R := R) u v * chiralMatrixOneForm (R := R) u v +
      chiralMatrixOneForm (R := R) u v * chiralMatrixOneForm (R := R) u v = _
    rw [hsq, ← two_smul R]
  have hmc_A :
      InfoGeometry.Canonical.MatrixTracedChernWeilBridge.matrixExteriorDerivative D.d A +
        (⅟(2 : R)) • ringSuperbracket .odd .odd A A =
        InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A := by
    have hsbA : ringSuperbracket .odd .odd A A = (2 : R) • (A * A) := by
      change A * A + A * A = (2 : R) • (A * A)
      exact (two_smul R (A * A)).symm
    rw [hsbA, smul_smul, invOf_mul_self, one_smul]
    rfl
  have hcov_eq :
      InfoGeometry.Canonical.MatrixTracedChernWeilBridge.matrixExteriorDerivative D.d
          (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) +
        ringSuperbracket .odd .even A
          (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) =
        InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge.covariantDerivative A D.d
          (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) := rfl
  have hbianchi :
      InfoGeometry.Canonical.MatrixTracedChernWeilBridge.matrixExteriorDerivative D.d
          (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) +
        ringSuperbracket .odd .even A
          (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) = 0 := by
    rw [hcov_eq]
    exact InfoGeometry.Canonical.GradedConnectionBianchiBridge.graded_connection_curvature_bianchi D A hA
  exact ⟨hhom, hsq, hsb_chiral, hmc_A, hcov_eq, hbianchi⟩

/-- **Unified Prima Materia, Graded Maurer–Cartan Superbracket, & Non-Abelian Chern–Weil Bridge:**
Connects the noncommutative Peirce Order-One sheet symmetry and bipartite plabic Master Index directly
to the repository's canonical graded exterior derivation, superbracket, non-abelian Bianchi, and
Chern–Weil owners (`ExteriorGradedDerivationBridge`, `BlockSupermatrixGradedTrace`,
`GradedConnectionBianchiBridge`, `ExteriorEvenTraceChernWeil`):
1. Bipartite Peirce sheet Order-One symmetry `OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D (P * X * P)) ((1 - P) * Y * (1 - P)) = OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D ((1 - P) * Y * (1 - P))) (P * X * P)`;
2. Bipartite plabic Master Index identity $2 k - n = V_B - V_W$;
3. Odd superbracket Maurer–Cartan curvature identity `D.d ω + (⅟(2 : R)) • ringSuperbracket .odd .odd ω ω = maurerCartanCurvature D.d ω`
   and Graded Bianchi identity $D.d F(\omega) + [\omega, F(\omega)]_{\mathrm{super}} = 0$;
4. Non-abelian matrix connection Bianchi identity `covariantDerivative A D.d (curvatureFromConnection D.d A) = 0`,
   degree-four trace vanishing `matrixTraceForm (A * A * A * A) = 0`, and Chern–Weil closedness
   `D.d (matrixTraceForm (curvatureFromConnection D.d A * curvatureFromConnection D.d A)) = 0`. -/
theorem tz5_prima_materia_and_graded_maurer_cartan_chern_weil_bridge
    {B R V : Type*} [Ring B] [Field R] [CharZero R] [AddCommGroup V] [Module R V]
    [Module.IsTorsionFree R (ExteriorAlgebra R V)] [Invertible (2 : R)] {n_mat : ℕ}
    {P : B} (hP : P * P = P) (D_op X Y : B)
    (V_B V_W E n k : ℤ)
    (h_trivalent : 3 * V_B + 3 * V_W = 2 * E + n)
    (h_helicity : k = 2 * V_B + V_W - E)
    (D : ExteriorDifferentialData R V)
    (hd : ∀ x, IsHomogeneousExteriorDegree 1 x → IsHomogeneousExteriorDegree 2 (D.d x))
    (ω : ExteriorAlgebra R V) (hω : IsHomogeneousExteriorDegree 1 ω)
    (A : Matrix (Fin n_mat) (Fin n_mat) (ExteriorAlgebra R V))
    (hA : MatrixIsHomogeneous 1 A) :
    (OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D_op (P * X * P)) ((1 - P) * Y * (1 - P)) =
      OperatorAlgebra.PeirceSpine.comm (OperatorAlgebra.PeirceSpine.comm D_op ((1 - P) * Y * (1 - P))) (P * X * P) ∧
     2 * k - n = V_B - V_W) ∧
    (D.d ω + (⅟(2 : R)) • ringSuperbracket .odd .odd ω ω =
      maurerCartanCurvature D.d ω ∧
     D.d (maurerCartanCurvature D.d ω) +
      ringSuperbracket .odd .even ω (maurerCartanCurvature D.d ω) = 0) ∧
    (InfoGeometry.Canonical.NonAbelianCovariantBianchiChernWeilBridge.covariantDerivative
        A D.d
        (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A) = 0 ∧
     InfoGeometry.Canonical.MatrixTracedChernWeilBridge.matrixTraceForm (A * A * A * A) = 0 ∧
     D.d (InfoGeometry.Canonical.MatrixTracedChernWeilBridge.matrixTraceForm
       (InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A *
         InfoGeometry.Canonical.ChernSimonsTransgressionInstantonBridge.curvatureFromConnection D.d A)) = 0) := by
  have hord := (peirce_bipartite_sheet_order_one_symmetry hP D_op X Y).2.2.2
  have hidx := (amplituhedron_bipartite_master_index V_B V_W E n k h_trivalent h_helicity).1
  have hmc_sb := (ringSuperbracket_odd_self_and_maurerCartan D.d ω).2.2.2
  have hmc_bianchi := (maurerCartanCurvature_graded_bianchi D ω hω).2.2.1
  have hmat_bianchi :=
    InfoGeometry.Canonical.GradedConnectionBianchiBridge.graded_connection_curvature_bianchi D A hA
  have htr4 :=
    InfoGeometry.Canonical.ExteriorEvenTraceChernWeil.matrix_trace_fourth_power_one_form_eq_zero A hA
  have hcw :=
    InfoGeometry.Canonical.ExteriorEvenTraceChernWeil.degree_raising_connection_chern_weil_closed D hd A hA
  exact ⟨⟨hord, hidx⟩, ⟨hmc_sb, hmc_bianchi⟩, ⟨hmat_bianchi, htr4, hcw⟩⟩

/-!
## Section 7: Majorana Twist Involution (`𝒯 * 𝒯 = 1`), $\mathrm{Cl}(1,1)$ Boundary Algebra, Nilpotent Lightcone Modes, & Automatic Phase Separation
-/

/-- **Universal $\mathrm{Cl}(1,1)$ Majorana–Krein Generator Laws from `twist_involution` ($\mathcal{T}^2 = 1$) and `klein_twist_anticommute` ($J_\Delta \mathcal{T} = -\mathcal{T} J_\Delta$):**
In any associative ring `B`, let $J_\Delta, \mathcal{T} \in B$ satisfy:
- `hJ : J_Δ * J_Δ = 1` (Modular reflection involution),
- `hT : 𝒯 * 𝒯 = 1` (`twist_involution` — Majorana double-cover involution),
- `h_anti : J_Δ * 𝒯 = -(𝒯 * J_Δ)` (`klein_twist_anticommute` — Klein-bottle anticommutation).
Then:
1. **Symplectic $\mathrm{Cl}(1,1)$ Volume Square:** $(J_\Delta * \mathcal{T}) * (J_\Delta * \mathcal{T}) = -1$;
2. **Mutual Particle–Antiparticle Conjugation:**
   $J_\Delta * \mathcal{T} * J_\Delta = -\mathcal{T}$ and $\mathcal{T} * J_\Delta * \mathcal{T} = -J_\Delta$;
3. **Exact Boundary Commutator & Krein Product:**
   $(J_\Delta * \mathcal{T}) * \mathcal{T} - \mathcal{T} * (J_\Delta * \mathcal{T}) = J_\Delta + J_\Delta$ and
   $J_\Delta * \big((J_\Delta * \mathcal{T}) * \mathcal{T} - \mathcal{T} * (J_\Delta * \mathcal{T})\big) = 1 + 1$;
4. **Nilpotent Majorana Lightcone Modes $N_\pm = J_\Delta \pm J_\Delta * \mathcal{T}$:**
   $(J_\Delta + J_\Delta * \mathcal{T})^2 = 0$, $(J_\Delta - J_\Delta * \mathcal{T})^2 = 0$, and
   $(J_\Delta + J_\Delta * \mathcal{T})(J_\Delta - J_\Delta * \mathcal{T}) + (J_\Delta - J_\Delta * \mathcal{T})(J_\Delta + J_\Delta * \mathcal{T}) = (4 : ℤ) \bullet (1 : B)$. -/
theorem majorana_klein_twist_cl11_generator_laws {B : Type*} [Ring B]
    {J_Δ 𝒯 : B} (hJ : J_Δ * J_Δ = 1) (hT : 𝒯 * 𝒯 = 1) (h_anti : J_Δ * 𝒯 = -(𝒯 * J_Δ)) :
    (J_Δ * 𝒯) * (J_Δ * 𝒯) = -1 ∧
    J_Δ * 𝒯 * J_Δ = -𝒯 ∧
    𝒯 * J_Δ * 𝒯 = -J_Δ ∧
    (J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯) = J_Δ + J_Δ ∧
    J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯)) = 1 + 1 ∧
    (J_Δ + J_Δ * 𝒯) * (J_Δ + J_Δ * 𝒯) = 0 ∧
    (J_Δ - J_Δ * 𝒯) * (J_Δ - J_Δ * 𝒯) = 0 ∧
    (J_Δ + J_Δ * 𝒯) * (J_Δ - J_Δ * 𝒯) + (J_Δ - J_Δ * 𝒯) * (J_Δ + J_Δ * 𝒯) =
      (4 : ℤ) • (1 : B) := by
  have hTJ : 𝒯 * J_Δ = -(J_Δ * 𝒯) := by
    calc
      𝒯 * J_Δ = -(-(𝒯 * J_Δ)) := (neg_neg _).symm
      _ = -(J_Δ * 𝒯) := by rw [← h_anti]
  have hJT_sq : (J_Δ * 𝒯) * (J_Δ * 𝒯) = -1 := by
    calc
      (J_Δ * 𝒯) * (J_Δ * 𝒯) = J_Δ * (𝒯 * J_Δ) * 𝒯 := by noncomm_ring
      _ = J_Δ * (-(J_Δ * 𝒯)) * 𝒯 := by rw [hTJ]
      _ = -(J_Δ * J_Δ) * (𝒯 * 𝒯) := by noncomm_ring
      _ = -1 * 1 := by rw [hJ, hT]
      _ = -1 := by noncomm_ring
  have hJ_conj_T : J_Δ * 𝒯 * J_Δ = -𝒯 := by
    calc
      J_Δ * 𝒯 * J_Δ = (-(𝒯 * J_Δ)) * J_Δ := by rw [h_anti]
      _ = -𝒯 * (J_Δ * J_Δ) := by noncomm_ring
      _ = -𝒯 * 1 := by rw [hJ]
      _ = -𝒯 := by noncomm_ring
  have hT_conj_J : 𝒯 * J_Δ * 𝒯 = -J_Δ := by
    calc
      𝒯 * J_Δ * 𝒯 = (-(J_Δ * 𝒯)) * 𝒯 := by rw [hTJ]
      _ = -J_Δ * (𝒯 * 𝒯) := by noncomm_ring
      _ = -J_Δ * 1 := by rw [hT]
      _ = -J_Δ := by noncomm_ring
  have h_comm_JTT : (J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯) = J_Δ + J_Δ := by
    calc
      (J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯)
        = J_Δ * (𝒯 * 𝒯) - (𝒯 * J_Δ * 𝒯) := by noncomm_ring
      _ = J_Δ * 1 - (-J_Δ) := by rw [hT, hT_conj_J]
      _ = J_Δ + J_Δ := by noncomm_ring
  have h_J_comm_JTT : J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯)) = 1 + 1 := by
    rw [h_comm_JTT, mul_add, hJ]
  have hJ_JT : J_Δ * (J_Δ * 𝒯) = 𝒯 := by
    calc
      J_Δ * (J_Δ * 𝒯) = (J_Δ * J_Δ) * 𝒯 := by noncomm_ring
      _ = 1 * 𝒯 := by rw [hJ]
      _ = 𝒯 := one_mul 𝒯
  have hN_plus_sq : (J_Δ + J_Δ * 𝒯) * (J_Δ + J_Δ * 𝒯) = 0 := by
    calc
      (J_Δ + J_Δ * 𝒯) * (J_Δ + J_Δ * 𝒯)
        = J_Δ * J_Δ + J_Δ * (J_Δ * 𝒯) + (J_Δ * 𝒯) * J_Δ + (J_Δ * 𝒯) * (J_Δ * 𝒯) := by noncomm_ring
      _ = 1 + 𝒯 + (-𝒯) + (-1) := by rw [hJ, hJ_JT, hJ_conj_T, hJT_sq]
      _ = 0 := by abel
  have hN_minus_sq : (J_Δ - J_Δ * 𝒯) * (J_Δ - J_Δ * 𝒯) = 0 := by
    calc
      (J_Δ - J_Δ * 𝒯) * (J_Δ - J_Δ * 𝒯)
        = J_Δ * J_Δ - J_Δ * (J_Δ * 𝒯) - (J_Δ * 𝒯) * J_Δ + (J_Δ * 𝒯) * (J_Δ * 𝒯) := by noncomm_ring
      _ = 1 - 𝒯 - (-𝒯) + (-1) := by rw [hJ, hJ_JT, hJ_conj_T, hJT_sq]
      _ = 0 := by abel
  have hN_anticomm :
      (J_Δ + J_Δ * 𝒯) * (J_Δ - J_Δ * 𝒯) + (J_Δ - J_Δ * 𝒯) * (J_Δ + J_Δ * 𝒯) =
        (4 : ℤ) • (1 : B) := by
    calc
      (J_Δ + J_Δ * 𝒯) * (J_Δ - J_Δ * 𝒯) + (J_Δ - J_Δ * 𝒯) * (J_Δ + J_Δ * 𝒯)
        = (2 : ℤ) • (J_Δ * J_Δ - (J_Δ * 𝒯) * (J_Δ * 𝒯)) := by noncomm_ring
      _ = (2 : ℤ) • (1 - (-1)) := by rw [hJ, hJT_sq]
      _ = (4 : ℤ) • (1 : B) := by noncomm_ring
  exact ⟨hJT_sq, hJ_conj_T, hT_conj_J, h_comm_JTT, h_J_comm_JTT,
    hN_plus_sq, hN_minus_sq, hN_anticomm⟩

/-- **Majorana Edge-Mode Pairing & Automatic Krein Supertrace Phase Separation on `Module.End R M`:**
For any free finite-rank module `M` over a commutative ring `R` with `[Invertible (2 : R)]`, if
$J_\Delta, \mathcal{T} \in \mathrm{Module.End}\,R\,M$ satisfy `hJ : J_Δ * J_Δ = 1`,
`hT : 𝒯 * 𝒯 = 1` (`twist_involution`), and `h_anti : J_Δ * 𝒯 = -(𝒯 * J_Δ)` (`klein_twist_anticommute`):
1. **Exact Krein Supertrace of $[J_\Delta \mathcal{T}, \mathcal{T}]$:**
   $$\mathrm{trace}\,R\,M\,\Big(J_\Delta * \big((J_\Delta * \mathcal{T}) * \mathcal{T} - \mathcal{T} * (J_\Delta * \mathcal{T})\big)\Big)
     = (2 : R) * \mathrm{trace}\,R\,M\,(1 : \mathrm{Module.End}\,R\,M);$$
2. **Automatic Phase Separation (`trace R M 1 ≠ 0`):**
   Whenever $\mathrm{trace}\,R\,M\,(1 : \mathrm{Module.End}\,R\,M) \ne 0$, the Majorana involution and
   anticommutation unconditionally force $J_\Delta \ne 1$, $J_\Delta \ne -1$, $\mathcal{T} \ne 1$,
   $\mathcal{T} \ne -1$, and $(J_\Delta * \mathcal{T}) * \mathcal{T} \ne \mathcal{T} * (J_\Delta * \mathcal{T})$;
3. **Majorana Double-Cover Involution & Bijective Eigenspace Pairing:**
   For every state $v \in M$, $\mathcal{T}(\mathcal{T} v) = v$ and
   $$v \in \mathrm{ker}(J_\Delta - 1) \iff \mathcal{T} v \in \mathrm{ker}(J_\Delta + 1).$$ -/
theorem majorana_klein_twist_endomorphism_phase_separation_and_edge_pairing
    {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (J_Δ 𝒯 : Module.End R M)
    (hJ : J_Δ * J_Δ = 1)
    (hT : 𝒯 * 𝒯 = 1)
    (h_anti : J_Δ * 𝒯 = -(𝒯 * J_Δ)) :
    LinearMap.trace R M (J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯))) =
      (2 : R) * LinearMap.trace R M (1 : Module.End R M) ∧
    (LinearMap.trace R M (1 : Module.End R M) ≠ 0 →
      J_Δ ≠ 1 ∧ J_Δ ≠ -1 ∧ 𝒯 ≠ 1 ∧ 𝒯 ≠ -1 ∧
      (J_Δ * 𝒯) * 𝒯 ≠ 𝒯 * (J_Δ * 𝒯)) ∧
    (∀ v : M, 𝒯 (𝒯 v) = v ∧
      (v ∈ LinearMap.ker (J_Δ - 1) ↔ 𝒯 v ∈ LinearMap.ker (J_Δ + 1))) := by
  have hcl := majorana_klein_twist_cl11_generator_laws hJ hT h_anti
  have h_str :
      LinearMap.trace R M (J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯))) =
        (2 : R) * LinearMap.trace R M (1 : Module.End R M) := by
    rw [hcl.2.2.2.2.1, ← two_smul R (1 : Module.End R M), map_smul, smul_eq_mul]
  refine ⟨h_str, ?_, ?_⟩
  · intro htr
    have h_str_ne : LinearMap.trace R M (J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯))) ≠ 0 := by
      rw [h_str]
      intro hzero
      have hinv : ⅟(2 : R) * ((2 : R) * LinearMap.trace R M (1 : Module.End R M)) = 0 := by
        rw [hzero, mul_zero]
      rw [← mul_assoc, invOf_mul_self, one_mul] at hinv
      exact htr hinv
    have hJ1 : J_Δ ≠ 1 := by
      intro h1
      have hzero : J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯)) = 0 := by
        rw [h1]
        noncomm_ring
      rw [hzero, map_zero] at h_str_ne
      exact h_str_ne rfl
    have hJm1 : J_Δ ≠ -1 := by
      intro hm1
      have hzero : J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯)) = 0 := by
        rw [hm1]
        noncomm_ring
      rw [hzero, map_zero] at h_str_ne
      exact h_str_ne rfl
    have hT1 : 𝒯 ≠ 1 := by
      intro h1
      have hzero : J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯)) = 0 := by
        rw [h1]
        noncomm_ring
      rw [hzero, map_zero] at h_str_ne
      exact h_str_ne rfl
    have hTm1 : 𝒯 ≠ -1 := by
      intro hm1
      have hzero : J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯)) = 0 := by
        rw [hm1]
        noncomm_ring
      rw [hzero, map_zero] at h_str_ne
      exact h_str_ne rfl
    have h_noncomm : (J_Δ * 𝒯) * 𝒯 ≠ 𝒯 * (J_Δ * 𝒯) := by
      intro heq
      rw [heq, sub_self, mul_zero, map_zero] at h_str_ne
      exact h_str_ne rfl
    exact ⟨hJ1, hJm1, hT1, hTm1, h_noncomm⟩
  · intro v
    have hTTv : 𝒯 (𝒯 v) = v := by
      have h1 := congrArg (fun f : Module.End R M => f v) hT
      simpa [Module.End.mul_apply] using h1
    have hJTv : ∀ w : M, J_Δ (𝒯 w) = - 𝒯 (J_Δ w) := by
      intro w
      have h1 := congrArg (fun f : Module.End R M => f w) h_anti
      simpa [Module.End.mul_apply] using h1
    refine ⟨hTTv, ?_⟩
    constructor
    · intro hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, hJTv v, hv,
        neg_add_cancel]
    · intro hTv
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hTv
      have hJ_Tv : J_Δ (𝒯 v) = - 𝒯 v := add_eq_zero_iff_eq_neg.mp hTv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
      calc
        J_Δ v - v = J_Δ (𝒯 (𝒯 v)) - 𝒯 (𝒯 v) := by rw [hTTv]
        _ = - 𝒯 (J_Δ (𝒯 v)) - 𝒯 (𝒯 v) := by rw [hJTv (𝒯 v)]
        _ = - 𝒯 (- 𝒯 v) - 𝒯 (𝒯 v) := by rw [hJ_Tv]
        _ = 𝒯 (𝒯 v) - 𝒯 (𝒯 v) := by simp [map_neg]
        _ = 0 := sub_self _

/-!
## Section 8: Tomita–Takesaki Submodule Commutant Reflection ($J_\Delta \mathcal{M} J_\Delta = \mathcal{M}'$), Determinant Spinning Instability (`spinning_instability_anomaly`), Bogoliubov/Berry Flatness, & $\mathrm{Pin}(5,5)$ Anomaly Inflow
-/

/-- **Tomita–Takesaki Submodule Commutant Reflection ($J_\Delta \mathcal{M} J_\Delta = \mathcal{M}'$) & Phase Separation:**
For any commutative ring `R`, `R`-module `M`, submodule $\mathcal{M} \le \mathrm{Module.End}\,R\,M$, and
modular involution $J_\Delta \in \mathrm{Module.End}\,R\,M$ (`hJ : J_Δ * J_Δ = 1`):
1. **Racemic Vacuum Collapse (`scalar_submodule_mem_commutant`):**
   If every $X \in \mathcal{M}$ is a scalar multiple of the identity ($\exists c : R,\, X = c \bullet 1$),
   then every $Y \in \mathrm{Module.End}\,R\,M$ lies in `MoebiusTomitaPacket.Commutant ℳ`;
2. **Contrapositive Phase Separation of Non-Scalar Ego $\mathcal{M}$ and Anima $\mathrm{Commutant}(\mathcal{M})$:**
   If $X \in \mathcal{M}$ and $Y \in \mathrm{Module.End}\,R\,M$ satisfy $X * Y \ne Y * X$, then
   $Y \notin \mathrm{MoebiusTomitaPacket.Commutant}\,\mathcal{M}$ and $X$ is strictly non-scalar
   ($\forall c : R,\, X \ne c \bullet 1$);
3. **Involutive Modular Conjugation (`conjugation_by_involution_involutive`):**
   For every $X \in \mathrm{Module.End}\,R\,M$, $J_\Delta * (J_\Delta * X * J_\Delta) * J_\Delta = X$;
4. **Bijective Ego–Anima Exchange & Mutual Causal Independence ($J_\Delta \mathcal{M} J_\Delta = \mathcal{M}'$):**
   Whenever conjugation by $J_\Delta$ maps $\mathcal{M}$ into `Commutant ℳ` and `Commutant ℳ` into $\mathcal{M}$,
   $X \in \mathcal{M} \iff J_\Delta * X * J_\Delta \in \mathrm{MoebiusTomitaPacket.Commutant}\,\mathcal{M}$,
   and every $X_1, X_2 \in \mathcal{M}$ satisfy $X_1 * (J_\Delta * X_2 * J_\Delta) = (J_\Delta * X_2 * J_\Delta) * X_1$. -/
theorem tomita_submodule_commutant_reflection_and_phase_separation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ℳ : Submodule R (Module.End R M))
    (J_Δ : Module.End R M) (hJ : J_Δ * J_Δ = 1) :
    ((∀ X ∈ ℳ, ∃ c : R, X = c • (1 : Module.End R M)) →
      ∀ Y : Module.End R M, Y ∈ InfoGeometry.GrandUnification.MoebiusTomitaPacket.Commutant ℳ) ∧
    (∀ X ∈ ℳ, ∀ Y : Module.End R M, X * Y ≠ Y * X →
      Y ∉ InfoGeometry.GrandUnification.MoebiusTomitaPacket.Commutant ℳ ∧
      ∀ c : R, X ≠ c • (1 : Module.End R M)) ∧
    (∀ X : Module.End R M, J_Δ * (J_Δ * X * J_Δ) * J_Δ = X) ∧
    ((∀ X ∈ ℳ, J_Δ * X * J_Δ ∈ InfoGeometry.GrandUnification.MoebiusTomitaPacket.Commutant ℳ) →
     (∀ Y ∈ InfoGeometry.GrandUnification.MoebiusTomitaPacket.Commutant ℳ, J_Δ * Y * J_Δ ∈ ℳ) →
      (∀ X : Module.End R M,
        (X ∈ ℳ ↔ J_Δ * X * J_Δ ∈ InfoGeometry.GrandUnification.MoebiusTomitaPacket.Commutant ℳ)) ∧
      (∀ X₁ ∈ ℳ, ∀ X₂ ∈ ℳ,
        X₁ * (J_Δ * X₂ * J_Δ) = (J_Δ * X₂ * J_Δ) * X₁)) := by
  refine ⟨InfoGeometry.GrandUnification.MoebiusTomitaPacket.scalar_submodule_mem_commutant ℳ,
    ?_, fun X =>
      InfoGeometry.GrandUnification.MoebiusTomitaPacket.conjugation_by_involution_involutive J_Δ X hJ,
    ?_⟩
  · intro X hX Y hne
    refine ⟨fun hY => hne (hY X hX), ?_⟩
    intro c rfl
    apply hne
    calc
      (c • (1 : Module.End R M)) * Y = c • (1 * Y) := smul_mul_assoc c 1 Y
      _ = c • Y := by rw [one_mul]
      _ = c • (Y * 1) := by rw [mul_one]
      _ = Y * (c • (1 : Module.End R M)) := (mul_smul_comm c Y 1).symm
  · intro h_to h_from
    refine ⟨fun X => ⟨fun hX => h_to X hX, fun hJX => ?_⟩,
      fun X₁ hX₁ X₂ hX₂ => h_to X₂ hX₂ X₁ hX₁⟩
    have h_back := h_from (J_Δ * X * J_Δ) hJX
    rwa [InfoGeometry.GrandUnification.MoebiusTomitaPacket.conjugation_by_involution_involutive
      J_Δ X hJ] at h_back

/-- **Determinant Spinning Instability (`spinning_instability_anomaly`), Callan–Harvey Anomaly Inflow, & Spontaneous Modular Phase Separation:**
For any free finite-rank module `M` over a commutative ring `R` with `[Invertible (2 : R)]`, any
chiral/Krein grading $\Gamma \in \mathrm{Module.End}\,R\,M$, and any two $\Gamma$-odd Cartan 1-forms
$A, B \in \mathrm{Module.End}\,R\,M$ (`hA : Γ * A = -(A * Γ)` and `hB : Γ * B = -(B * Γ)`):
1. **Ungraded Trace Collapse vs. Graded Supertrace Doubling (`spinning_instability_anomaly`):**
   $$\mathrm{trace}\,R\,M\,(A * B - B * A) = 0
     \quad\land\quad
     \mathrm{supertrace}\,\Gamma\,(A * B - B * A) = (2 : R) * \mathrm{supertrace}\,\Gamma\,(A * B);$$
2. **Callan–Harvey Anomaly Inflow Conservation:**
   Whenever a bulk topological index $I_{\mathrm{bulk}} : R$ matches the boundary commutator supertrace
   ($I_{\mathrm{bulk}} = \mathrm{supertrace}\,\Gamma\,(A * B - B * A)$), it equals
   $(2 : R) * \mathrm{supertrace}\,\Gamma\,(A * B)$ and the combined boundary-minus-bulk anomaly vanishes:
   $$\mathrm{supertrace}\,\Gamma\,(A * B - B * A) - I_{\mathrm{bulk}} = 0;$$
3. **Spontaneous Modular Phase Separation from Non-Vanishing Spinning Instability:**
   Whenever $\mathrm{supertrace}\,\Gamma\,(A * B) \ne 0$, the commutator supertrace is non-zero
   ($\mathrm{supertrace}\,\Gamma\,(A * B - B * A) \ne 0$), unconditionally forcing
   $\Gamma \ne 1$, $\Gamma \ne -1$, $A * B \ne B * A$, and both $A, B$ to be non-scalar
   ($\forall c : R,\, A \ne c \bullet 1 \;\land\; B \ne c \bullet 1$). -/
theorem spinning_instability_anomaly_and_inflow_phase_separation
    {R M : Type*} [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (Γ A B : Module.End R M)
    (hA : Γ * A = -(A * Γ))
    (hB : Γ * B = -(B * Γ)) :
    LinearMap.trace R M (A * B - B * A) = 0 ∧
    InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B - B * A) =
      (2 : R) * InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B) ∧
    (∀ I_bulk : R,
      I_bulk = InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B - B * A) →
      I_bulk = (2 : R) * InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B) ∧
      InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B - B * A) - I_bulk = 0) ∧
    (InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B) ≠ 0 →
      InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B - B * A) ≠ 0 ∧
      Γ ≠ 1 ∧ Γ ≠ -1 ∧ A * B ≠ B * A ∧
      (∀ c : R, A ≠ c • (1 : Module.End R M)) ∧
      (∀ c : R, B ≠ c • (1 : Module.End R M))) := by
  have h_tr_zero : LinearMap.trace R M (A * B - B * A) = 0 := by
    rw [map_sub, LinearMap.trace_mul_comm R A B, sub_self]
  have h_spin := InfoGeometry.TopologicalFieldTheory.spinning_instability_anomaly Γ A B hA hB
  refine ⟨h_tr_zero, h_spin, fun I_bulk hI => ⟨hI.trans h_spin, sub_eq_zero.mpr hI.symm⟩, ?_⟩
  intro h_ab_ne
  have h_comm_ne : InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B - B * A) ≠ 0 := by
    rw [h_spin]
    intro hzero
    have hinv : ⅟(2 : R) * ((2 : R) * InfoGeometry.TopologicalFieldTheory.supertrace Γ (A * B)) = 0 := by
      rw [hzero, mul_zero]
    rw [← mul_assoc, invOf_mul_self, one_mul] at hinv
    exact h_ab_ne hinv
  have hΓ1 : Γ ≠ 1 := by
    intro h1
    apply h_comm_ne
    unfold InfoGeometry.TopologicalFieldTheory.supertrace
    rw [h1, one_mul]
    exact h_tr_zero
  have hΓm1 : Γ ≠ -1 := by
    intro hm1
    apply h_comm_ne
    unfold InfoGeometry.TopologicalFieldTheory.supertrace
    rw [hm1, neg_one_mul, map_neg, h_tr_zero, neg_zero]
  have hAB_ne : A * B ≠ B * A := by
    intro heq
    apply h_comm_ne
    unfold InfoGeometry.TopologicalFieldTheory.supertrace
    rw [heq, sub_self, mul_zero, map_zero]
  have hA_nonscalar : ∀ c : R, A ≠ c • (1 : Module.End R M) := by
    intro c rfl
    apply hAB_ne
    calc
      (c • (1 : Module.End R M)) * B = c • (1 * B) := smul_mul_assoc c 1 B
      _ = c • B := by rw [one_mul]
      _ = c • (B * 1) := by rw [mul_one]
      _ = B * (c • (1 : Module.End R M)) := (mul_smul_comm c B 1).symm
  have hB_nonscalar : ∀ c : R, B ≠ c • (1 : Module.End R M) := by
    intro c rfl
    apply hAB_ne
    calc
      A * (c • (1 : Module.End R M)) = c • (A * 1) := mul_smul_comm c A 1
      _ = c • A := by rw [mul_one]
      _ = c • (1 * A) := by rw [one_mul]
      _ = (c • (1 : Module.End R M)) * A := (smul_mul_assoc c 1 A).symm
  exact ⟨h_comm_ne, hΓ1, hΓm1, hAB_ne, hA_nonscalar, hB_nonscalar⟩

/-- **Bogoliubov/Berry Right Maurer–Cartan Flatness & $\mathrm{Pin}(5,5)$ Projective Boundary Transport:**
Unifies the dressed-vacuum right Maurer–Cartan flatness identity
`D(u) * D(u⁻¹) + ω_B * ω_B = 0` (`BogoliubovBerryMaurerCartanBridge.berryMaurerCartan_flat`) with
the $\mathrm{Pin}(5,5)$ algebra-cone transport of the nilpotent projective compensation
$(\psi_n(a))^2 = 0$, the TKK scale symmetry $[[\psi_n(a), \psi_n(c)], \psi_n(a)] = \psi_n(a) + \psi_n(a)$,
and the $\mathrm{Pin}(5,5)$ reflection (`Pin55ColimitAnomalyBridge`). -/
theorem berry_maurer_cartan_and_pin55_colimit_anomaly_bridge
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (D : InfoGeometry.NCG.AlgebraDerivation R A) (u : Aˣ)
    {A_inf : Type*} [Ring A_inf] [Algebra ℚ A_inf]
    {A_seq : ℕ → Type*} [∀ n, Ring (A_seq n)] [∀ n, Algebra ℚ (A_seq n)]
    (psi : ∀ n, A_seq n →ₐ[ℚ] A_inf) (n : ℕ)
    (e f : Fin 5 → A_seq n)
    [InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.OperatorCl55 e f]
    (i : Fin 5) (v : A_seq n) :
    InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u *
      InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u =
        -(D (u : A) * D (u⁻¹ : Aˣ).val) ∧
    (psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_a e f)) *
      (psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_a e f)) = 0 ∧
    NoncommutativeGeometry.lie_bracket
      (NoncommutativeGeometry.lie_bracket
        (psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_a e f))
        (psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_c e f)))
      (psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_a e f)) *
      psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_a e f) = 0 ∧
    NoncommutativeGeometry.e_reflect (fun j => psi n (e j)) (fun j => psi n (f j)) i (psi n v) =
      psi n (NoncommutativeGeometry.e_reflect e f i v) := by
  have hflat := InfoGeometry.NCG.AlgebraDerivation.maurer_cartan_flatness D u
  have hberry_sq :
      InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u *
        InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u =
          -(D (u : A) * D (u⁻¹ : Aˣ).val) := by
    calc
      InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u *
          InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u
        = (D (u : A) * D (u⁻¹ : Aˣ).val +
            InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u *
              InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u) -
          D (u : A) * D (u⁻¹ : Aˣ).val := by abel
      _ = 0 - D (u : A) * D (u⁻¹ : Aˣ).val := by rw [hflat]
      _ = -(D (u : A) * D (u⁻¹ : Aˣ).val) := by abel
  have hsq := InfoGeometry.Canonical.Pin55ColimitAnomalyBridge.target_projective_compensation_sq psi n e f
  have htkk := InfoGeometry.Canonical.Pin55ColimitAnomalyBridge.target_tkk_scale_symmetry psi n e f
  have htkk_nil :
      NoncommutativeGeometry.lie_bracket
        (NoncommutativeGeometry.lie_bracket
          (psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_a e f))
          (psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_c e f)))
        (psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_a e f)) *
        psi n (InfoGeometry.Canonical.Cl55OperatorProjectiveBoundary.projective_compensation_a e f) = 0 := by
    rw [htkk, add_mul, hsq, add_zero]
  have hrefl := InfoGeometry.Canonical.Pin55ColimitAnomalyBridge.target_pin55_reflection psi n e f i v
  exact ⟨hberry_sq, hsq, htkk_nil, hrefl⟩

/-!
## Section 9: Modular Hamiltonian ($K = -\log \Delta$), $(5,5)$ Horizon Capacitance, Bulk–Boundary Defect Correspondence, & Type-D Cantor Bitword Colimit Synthesis
-/

/-- **Modular Hamiltonian ($K = -\log \Delta$), $(5,5)$ Horizon Capacitance, `time_requires_horizon`, & Bulk–Boundary Defect Bridge:**
Unifies `InfoGeometry.GrandUnification.Dynamics` (`ModularHamiltonian`) and
`InfoGeometry.GrandUnification.bulk_index_forces_boundary_defect_mode` (`BulkBoundaryCorrespondence`):
1. Logarithmic Modular Hamiltonian laws ($K(1) = 0$, $K(\delta^{-1}) = -K(\delta)$, $\exp(-K(\delta)) = \delta$);
2. Tomita conjugation oddness ($J_\Delta K J_\Delta = -K \iff J_\Delta K = -K J_\Delta$) and twin-sheet
   time reversal $K(J_\Delta v) = -J_\Delta(K v)$;
3. Exact $(5,5)$ holographic horizon capacitance quantization (`horizon_capacitance Γ = 5`,
   `witten_index Γ = 0`, and $\dim_R M = 10$);
4. Constructive `time_requires_horizon` ($\mathcal{T} K_{\mathrm{triv}} = K_{\mathrm{triv}} \land \mathrm{horizon\_capacitance}\,\mathcal{T} = 0 \implies K_{\mathrm{triv}} = 0$);
5. Constructive bulk-boundary defect correspondence: if $\mathcal{T}_b * K_b = K_b$ and
   $\mathrm{trace}\,R\,M\,(\Gamma * (K_b * B_b - B_b * K_b)) \ne 0$, then $K_b \ne 0$,
   $K_b * B_b \ne B_b * K_b$, and the boundary defect subspace is non-trivial ($\ker(\mathcal{T}_b - 1) \ne \bot$). -/
theorem modular_hamiltonian_horizon_capacitance_and_bulk_boundary_defect_bridge
    {R M : Type*} [Field R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M]
    (δ : ℝ) (hδ : 0 < δ)
    (Γ J_Δ 𝒯 K K_triv 𝒯_b K_b B_b : Module.End R M)
    (h_krein : InfoGeometry.GrandUnification.ModularPhaseSeparation.IsKreinSymmetry Γ)
    (h_left : Module.finrank R (InfoGeometry.GrandUnification.MachianCosmology.Ego Γ) = 5)
    (h_right : Module.finrank R (InfoGeometry.GrandUnification.MachianCosmology.Anima Γ) = 5)
    (hJ : J_Δ * J_Δ = 1)
    (hconj : J_Δ * K * J_Δ = -K)
    (h_triv_support : 𝒯 * K_triv = K_triv)
    (h_triv_cap : InfoGeometry.GrandUnification.HorizonCapacitance.horizon_capacitance 𝒯 = 0)
    (hTK_b : 𝒯_b * K_b = K_b)
    (h_bulk_idx : LinearMap.trace R M (Γ * (K_b * B_b - B_b * K_b)) ≠ 0) :
    (InfoGeometry.GrandUnification.Dynamics.modularLogEigenvalue 1 = 0 ∧
     InfoGeometry.GrandUnification.Dynamics.modularLogEigenvalue δ⁻¹ =
       -InfoGeometry.GrandUnification.Dynamics.modularLogEigenvalue δ ∧
     Real.exp (-InfoGeometry.GrandUnification.Dynamics.modularLogEigenvalue δ) = δ) ∧
    (J_Δ * K = -(K * J_Δ) ∧ ∀ v : M, K (J_Δ v) = - J_Δ (K v)) ∧
    (InfoGeometry.GrandUnification.HorizonCapacitance.horizon_capacitance Γ = 5 ∧
     InfoGeometry.GrandUnification.MoebiusWittenIndex.witten_index Γ = 0 ∧
     Module.finrank R M = 10) ∧
    (K_triv = 0 ∧
     InfoGeometry.GrandUnification.ModularPhaseSeparation.supertrace J_Δ K_triv = 0) ∧
    (LinearMap.range K_b ≤ LinearMap.ker (𝒯_b - 1) ∧
     K_b ≠ 0 ∧ K_b * B_b ≠ B_b * K_b ∧ LinearMap.ker (𝒯_b - 1) ≠ ⊥) := by
  have hmh :=
    InfoGeometry.GrandUnification.Dynamics.mh5_master_modular_hamiltonian_horizon_capacitance_synthesis
      δ hδ Γ J_Δ 𝒯 K K_triv h_krein h_left h_right hJ hconj h_triv_support h_triv_cap
  have hbb :=
    InfoGeometry.GrandUnification.bulk_index_forces_boundary_defect_mode 𝒯_b Γ K_b B_b hTK_b h_bulk_idx
  exact ⟨hmh.2.1, hmh.2.2.1, hmh.2.2.2.1, hmh.2.2.2.2, hbb⟩

/-- **Type-D Cantor Bitword Filtered Colimit & Zorn–Tetractys–Majorana–Anomaly Grand Unification Capstone:**
Unifies:
1. Filtered colimit preservation of Type-D even-parity bitwords (`parity (extendBitword w) = parity w`,
   `iteratedExtendParityHom_comp`, `injectFiniteState_iteratedExtend`, `injectFiniteState_extendParityHom`);
2. Universal Peirce–Tetractys Zorn Nambu law $\mathrm{nambu}\langle N_+, N_-, P \rangle = (1 + P)V(P, A, C)$;
3. Boundary $\mathrm{Cl}(1,1)$ Majorana involution laws $(J_\Delta \mathcal{T})^2 = -1$ and
   $J_\Delta [(J_\Delta \mathcal{T}), \mathcal{T}] = 1 + 1$;
4. $\Gamma$-evenness of the product of two $\Gamma$-odd Cartan 1-forms ($\Gamma (A_{\mathrm{odd}} B_{\mathrm{odd}}) = (A_{\mathrm{odd}} B_{\mathrm{odd}}) \Gamma$)
   and the Determinant Spinning Instability $\mathrm{supertrace}\,\Gamma\,[A_{\mathrm{odd}}, B_{\mathrm{odd}}] = 2\,\mathrm{supertrace}\,\Gamma\,(A_{\mathrm{odd}} B_{\mathrm{odd}})$. -/
theorem cantor_typeD_bitword_colimit_and_zorn_tetractys_grand_unification_capstone
    {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k)
    (w : Bitword n)
    (state : TypeDEvenParity n)
    {B : Type*} [Ring B] {P J_Δ 𝒯 : B}
    (hP : P * P = P) (A C : B)
    (hJ : J_Δ * J_Δ = 1) (hT : 𝒯 * 𝒯 = 1) (h_anti : J_Δ * 𝒯 = -(𝒯 * J_Δ))
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (Γ A_odd B_odd : Module.End R M)
    (hA_odd : Γ * A_odd = -(A_odd * Γ))
    (hB_odd : Γ * B_odd = -(B_odd * Γ)) :
    (parity
        (extendBitword w) =
      parity w ∧
     (iteratedExtendParityHom hmk).comp
        (iteratedExtendParityHom hnm) =
      iteratedExtendParityHom (le_trans hnm hmk) ∧
     injectFiniteState m
        (iteratedExtendParityHom hnm state) =
      injectFiniteState n state ∧
     injectFiniteState (n + 1)
        (extendParityHom state) =
      injectFiniteState n state) ∧
    nambu (tetractysPeirceTriad P A C) = (1 + P) * genV P A C ∧
    ((J_Δ * 𝒯) * (J_Δ * 𝒯) = -1 ∧
     J_Δ * ((J_Δ * 𝒯) * 𝒯 - 𝒯 * (J_Δ * 𝒯)) = 1 + 1) ∧
    (Γ * (A_odd * B_odd) = (A_odd * B_odd) * Γ ∧
     InfoGeometry.TopologicalFieldTheory.supertrace Γ (A_odd * B_odd - B_odd * A_odd) =
       (2 : R) * InfoGeometry.TopologicalFieldTheory.supertrace Γ (A_odd * B_odd)) := by
  have hpar := parity_extendBitword w
  have hcomp := iteratedExtendParityHom_comp hnm hmk
  have hinj_m := injectFiniteState_iteratedExtend hnm state
  have hinj_succ := injectFiniteState_extendParityHom n state
  have hnambu := (nambu_tetractysPeirceTriad hP A C).1
  have hcl := majorana_klein_twist_cl11_generator_laws hJ hT h_anti
  have heven := InfoGeometry.TopologicalFieldTheory.odd_mul_odd_commutes_with_grading Γ A_odd B_odd hA_odd hB_odd
  have hspin := InfoGeometry.TopologicalFieldTheory.spinning_instability_anomaly Γ A_odd B_odd hA_odd hB_odd
  exact ⟨⟨hpar, hcomp, hinj_m, hinj_succ⟩, hnambu, ⟨hcl.1, hcl.2.2.2.2.1⟩, ⟨heven, hspin⟩⟩

/-!
## 10. Aharonov Two-State Vector Formalism (TSVF), Quantum Cheshire Cat, Modular Momentum & Faraday-Cage Holonomy
-/

/-- **Aharonov–Bergmann–Lebowitz Two-State Peirce Sandwich, Universal Quantum Cheshire Cat &
Heisenberg Modular-Momentum Causality Protection:**
In any unital associative ring `B` with a Peirce idempotent $P^2 = P$, arbitrary $A, C \in B$,
and any which-way slit involution $V^2 = 1$ anticommuting with the non-local modular translation
operator $U$ ($V U = - U V$):
1. **Two-State Graph-Chart Overlap & Bruhat Transition (`TwoStateSandwich`):**
   The pre-selected chart point $P - N_+$ and post-selected chart point $P + N_-$ satisfy
   $(P - N_+)(P + N_-) = P - N_+ N_-$ and are intertwined by `chartBruhatConj` / `chartBruhatConjInv`.
2. **Two-State Peirce Generator Sandwiches:**
   Between $P - N_+$ and $P + N_-$, the symmetric bridge $\Phi = N_+ + N_-$ has vanishing sandwich
   $(P - N_+)\Phi(P + N_-) = 0$, whereas the chiral generator $J = N_+ - N_-$ has non-vanishing
   sandwich $(P - N_+)J(P + N_-) = 2 N_+ N_-$.
3. **Universal Ring-Theoretic Quantum Cheshire Cat Separation:**
   The composite corridor projector $Q_{\mathrm{cat}} := (1 - P) + N_+$ is an idempotent
   ($Q_{\mathrm{cat}}^2 = Q_{\mathrm{cat}}$) that right-supports the chiral spin/cone operator $N_+$
   ($N_+ Q_{\mathrm{cat}} = N_+$); yet its two-state sandwich vanishes identically
   ($(P - N_+) Q_{\mathrm{cat}} (P + N_-) = 0$ — the "Cat" has zero weak presence in the
   $Q_{\mathrm{cat}}$-corridor), while the supported operator $N_+$ has non-zero two-state sandwich
   $(P - N_+) N_+ (P + N_-) = N_+ N_-$ (the disembodied "Smile").
4. **Heisenberg Modular-Momentum Uncertainty & Causality Protection:**
   On either definite-slit projection $1 + V$ or $1 - V$, the diagonal expectation of the
   anticommuting modular translation operator $U$ vanishes identically
   ($(1 + V) U (1 + V) = 0$ and $(1 - V) U (1 - V) = 0$), proving algebraically that definite
   which-way localization erases the non-local modular expectation and prevents causality
   violation, whereas the coherent two-slit anticommutator $(1 + V) U + U (1 + V) = U + U$
   preserves $U$. -/
theorem aharonov_two_state_peirce_cheshire_cat_and_modular_momentum_causality_protection
    {B : Type*} [Ring B] {P V U : B}
    (hP : P * P = P) (A C : B)
    (hV : V * V = 1) (h_anti_VU : V * U = -(U * V)) :
    ((P - conePlus P A) * (P + coneMinus P C) = P - conePlus P A * coneMinus P C ∧
     chartBruhatConj P A C (P + coneMinus P C) = P - conePlus P A ∧
     chartBruhatConjInv P A C (P - conePlus P A) = P + coneMinus P C) ∧
    ((P - conePlus P A) * genPhi P A C * (P + coneMinus P C) = 0 ∧
     (P - conePlus P A) * genJ P A C * (P + coneMinus P C) =
       (2 : ℤ) • (conePlus P A * coneMinus P C)) ∧
    (((1 - P) + conePlus P A) * ((1 - P) + conePlus P A) = (1 - P) + conePlus P A ∧
     conePlus P A * ((1 - P) + conePlus P A) = conePlus P A ∧
     (P - conePlus P A) * ((1 - P) + conePlus P A) * (P + coneMinus P C) = 0 ∧
     (P - conePlus P A) * conePlus P A * (P + coneMinus P C) =
       conePlus P A * coneMinus P C) ∧
    ((1 + V) * U * (1 + V) = 0 ∧
     (1 - V) * U * (1 - V) = 0 ∧
     (1 + V) * U + U * (1 + V) = U + U) := by
  have hprod := chart_point_product hP A C
  have hbruhat := chart_bruhat_conjugation_transition hP A C
  have hsand := chart_two_state_generator_sandwich hP A C
  have hcat_idem : ((1 - P) + conePlus P A) * ((1 - P) + conePlus P A) = (1 - P) + conePlus P A := by
    peirce_nf hP
  have hcat_supp : conePlus P A * ((1 - P) + conePlus P A) = conePlus P A := by
    peirce_nf hP
  have hcat_zero : (P - conePlus P A) * ((1 - P) + conePlus P A) * (P + coneMinus P C) = 0 := by
    peirce_nf hP
  have hsmile : (P - conePlus P A) * conePlus P A * (P + coneMinus P C) =
      conePlus P A * coneMinus P C := by
    peirce_nf hP
  have hVU_V : V * U * V = -U := by
    calc
      V * U * V = -(U * V) * V := by rw [h_anti_VU]
      _ = -(U * (V * V)) := by rw [neg_mul, mul_assoc]
      _ = -U := by rw [hV, mul_one]
  have h_slit1_mod : (1 + V) * U * (1 + V) = 0 := by
    calc
      (1 + V) * U * (1 + V)
        = (U + V * U) * (1 + V) := by rw [add_mul, one_mul]
      _ = U * 1 + U * V + (V * U * 1 + V * U * V) := by
            rw [add_mul, mul_add, mul_add]
      _ = U + U * V + (-(U * V) + -U) := by
            rw [mul_one, mul_one, hVU_V, h_anti_VU]
      _ = 0 := by abel
  have h_slit2_mod : (1 - V) * U * (1 - V) = 0 := by
    calc
      (1 - V) * U * (1 - V)
        = (U - V * U) * (1 - V) := by rw [sub_mul, one_mul]
      _ = (U * 1 - U * V) - (V * U * 1 - V * U * V) := by
            rw [sub_mul, mul_sub, mul_sub]
      _ = (U - U * V) - (-(U * V) - -U) := by
            rw [mul_one, mul_one, hVU_V, h_anti_VU]
      _ = 0 := by abel
  have h_anticomm_sum : (1 + V) * U + U * (1 + V) = U + U := by
    calc
      (1 + V) * U + U * (1 + V)
        = (U + -(U * V)) + (U + U * V) := by
            rw [add_mul, one_mul, mul_add, mul_one, h_anti_VU]
      _ = U + U := by abel
  exact ⟨⟨hprod, hbruhat.1, hbruhat.2⟩, ⟨hsand.1, hsand.2.1⟩,
    ⟨hcat_idem, hcat_supp, hcat_zero, hsmile⟩,
    ⟨h_slit1_mod, h_slit2_mod, h_anticomm_sum⟩⟩

/-- **Aharonov Concentric $S^3$ Sphere-Time Lock, Negative Weak Dwell-Time (Counter-Particle) &
Faraday-Cage Aharonov–Bohm Gauge Cocycle Bridge:**
Unifies:
1. **Concentric $S^3$ Sphere-Time Dilatation & Twin-Shell Horizon Lock (`AharonovTwoStateSphereTime`):**
   Dilating $X \in \mathrm{Sphere4D}\,R$ by $s$ scales `radiusSq` by $s^2$, while forward-expanding
   ($r_0 e^{+\tau}$) and backward-contracting ($r_0 e^{-\tau}$) shells with $e^{+\tau} e^{-\tau} = 1$
   lock onto the static horizon squared radius $r_0^2$.
2. **Standard Single-State Non-Negativity vs. Two-State Negative Counter-Particle Occupation:**
   While every single-state Slit-1 expectation $\langle \psi \mid \hat{P}_1 \mid \psi \rangle \ge 0$
   is non-negative, the two-state weak readouts satisfy the partition of unity
   $\langle \phi \mid \hat{P}_1 \mid \psi \rangle + \langle \phi \mid \hat{P}_2 \mid \psi \rangle = \langle \phi \mid \psi \rangle$
   and exhibit a strictly negative normalized Slit-1 weak occupation $W(\hat{P}_1) = -1 < 0$
   (Aharonov's counter-particle witness) balanced by $W(\hat{P}_2) = +2$ so $W(\hat{P}_1) + W(\hat{P}_2) = 1$.
3. **Two-Faraday-Cage Pure-Gauge Maurer–Cartan Difference & Fractional Vortex Holonomy:**
   For any derivation $D : A \to_R A$ (`IsDerivation D`) and gauge transformations $u, v \in A^\times$,
   each local branch has vanishing Maurer–Cartan curvature ($D(u) D(u^{-1}) + \omega_B(u)^2 = 0$),
   yet the potential difference $\omega_B(u v) - \omega_B(u) = u \, \omega_B(v) \, u^{-1}$ isolates
   the gauge-covariant relative holonomy, while a third-root Aharonov–Bohm vortex phase
   ($\mathrm{phase}^3 = 1$) satisfies $\mathrm{diagonalVortexOperator}(\mathrm{phase})^3 = 1$. -/
theorem aharonov_sphere_time_counter_particle_and_faraday_cage_holonomy_bridge
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (s r₀ ep en : R) (hep_en : ep * en = 1)
    (X : InfoGeometry.QuantumContext.AharonovTime.Sphere4D R)
    (ϕ ψ : InfoGeometry.QuantumContext.AharonovTime.SlitState2D R)
    {A : Type*} [Ring A] [Algebra R A]
    (D : InfoGeometry.NCG.AlgebraDerivation R A) (u v : Aˣ)
    {phase : ℂ} (h_phase : InfoGeometry.Topology.Parafermion.IsThirdRootPhase phase) :
    (InfoGeometry.QuantumContext.AharonovTime.Sphere4D.radiusSq
        (InfoGeometry.QuantumContext.AharonovTime.Sphere4D.dilate s X) =
      s ^ 2 * InfoGeometry.QuantumContext.AharonovTime.Sphere4D.radiusSq X ∧
     (r₀ * ep) * (r₀ * en) = r₀ ^ 2) ∧
    (0 ≤ InfoGeometry.QuantumContext.AharonovTime.SlitState2D.bracket ψ
        (InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit1 ψ) ∧
     InfoGeometry.QuantumContext.AharonovTime.SlitState2D.bracket ϕ
        (InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit1 ψ) +
      InfoGeometry.QuantumContext.AharonovTime.SlitState2D.bracket ϕ
        (InfoGeometry.QuantumContext.AharonovTime.SlitState2D.projSlit2 ψ) =
      InfoGeometry.QuantumContext.AharonovTime.SlitState2D.bracket ϕ ψ ∧
     InfoGeometry.QuantumContext.AharonovTime.SlitState2D.normalizedWeakValue1
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.backwardPostSelected
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.forwardPreSelected = -1 ∧
     InfoGeometry.QuantumContext.AharonovTime.SlitState2D.normalizedWeakValue1
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.backwardPostSelected
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.forwardPreSelected < 0 ∧
     InfoGeometry.QuantumContext.AharonovTime.SlitState2D.normalizedWeakValue2
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.backwardPostSelected
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.forwardPreSelected = 2 ∧
     InfoGeometry.QuantumContext.AharonovTime.SlitState2D.normalizedWeakValue1
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.backwardPostSelected
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.forwardPreSelected +
      InfoGeometry.QuantumContext.AharonovTime.SlitState2D.normalizedWeakValue2
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.backwardPostSelected
        InfoGeometry.QuantumContext.AharonovTime.SlitState2D.forwardPreSelected = 1) ∧
    (D (u : A) * D (u⁻¹ : Aˣ).val +
        InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u *
          InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u = 0 ∧
     InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D (u * v) -
        InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u =
        (u : A) * InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D v * (u⁻¹ : Aˣ).val ∧
     phase * phase * phase = 1 ∧
     InfoGeometry.Topology.Parafermion.diagonalVortexOperator phase *
        InfoGeometry.Topology.Parafermion.diagonalVortexOperator phase *
          InfoGeometry.Topology.Parafermion.diagonalVortexOperator phase = 1) := by
  have hdil := InfoGeometry.QuantumContext.AharonovTime.Sphere4D.radiusSq_dilate s X
  have hlock := InfoGeometry.QuantumContext.AharonovTime.Sphere4D.twin_shell_horizon_lock r₀ ep en hep_en
  have hpos := InfoGeometry.QuantumContext.AharonovTime.SlitState2D.standard_qm_slit1_nonneg ψ
  have hpart := InfoGeometry.QuantumContext.AharonovTime.SlitState2D.two_state_weak_partition ϕ ψ
  have hneg := InfoGeometry.QuantumContext.AharonovTime.SlitState2D.double_slit_registers_negative_weak_time
  have hflat := InfoGeometry.NCG.AlgebraDerivation.maurer_cartan_flatness D u
  have hcocycle := InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm_mul D u v
  have hdiff :
      InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D (u * v) -
          InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u =
        (u : A) * InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D v * (u⁻¹ : Aˣ).val := by
    calc
      InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D (u * v) -
          InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u
        = ((u : A) * InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D v * (u⁻¹ : Aˣ).val +
            InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u) -
          InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D u := by rw [hcocycle]
      _ = (u : A) * InfoGeometry.NCG.AlgebraDerivation.pureGaugeForm D v * (u⁻¹ : Aˣ).val := by abel
  have hphase3 := InfoGeometry.Topology.Parafermion.thirdRootPhase_triple_product h_phase
  have hvortex3 := InfoGeometry.Topology.Parafermion.diagonalVortexOperator_cube_eq_one h_phase
  exact ⟨⟨hdil, hlock⟩, ⟨hpos, hpart, hneg.2.1, hneg.2.2.1, hneg.2.2.2.1, hneg.2.2.2.2⟩,
    ⟨hflat, hdiff, hphase3, hvortex3⟩⟩

/-!
## 11. Differential Forms as Operators & Maurer–Cartan Forms as Operators
-/

/-- **Differential Forms as Operators & Maurer–Cartan Operator Conjugation-Curvature Law:**
In any unital associative operator ring `B`:
1. **Connes Operator Differential 1-Forms & 2-Forms (`NoncommutativeConnesCalculus`):**
   For any involution $F \in B$ ($F * F = 1$), cyclic additive functional $\tau : B \to_+ R_0$,
   and operators $X, Y \in B$, the inner commutator 1-form
   $d_F(X) := \mathrm{connesDifferential}\,F\,X = F * X - X * F$ satisfies:
   - the noncommutative Leibniz rule
     $d_F(X * Y) = d_F(X) * Y + X * d_F(Y)$,
   - $F$-oddness of operator 1-forms ($\{F, d_F(X)\} = 0$) and $F$-evenness of operator 2-form
     products ($[F, d_F(X) * d_F(Y)] = 0$),
   - vanishing cyclic graded trace on exact operator 1-forms ($\tau(F \, d_F(X)) = 0$) and
     graded skew-symmetry on operator 2-form products
     ($\tau(F \, d_F(X) \, d_F(Y)) = -\tau(F \, d_F(Y) \, d_F(X))$).
2. **Maurer–Cartan Forms as Operators (`peirceMaurerCartanForm (comm D) U Uinv`):**
   For any operator $D \in B$ and any inverse operator pair $U, U_{\mathrm{inv}} \in B$
   ($U * U_{\mathrm{inv}} = 1$, $U_{\mathrm{inv}} * U = 1$), the operator Maurer–Cartan 1-form
   $\omega_D := \mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,D)\,U\,U_{\mathrm{inv}}
   = U_{\mathrm{inv}} * (D * U - U * D)$ satisfies:
   - **Dirac Shift = Gauge Conjugation:**
     $$\omega_D = U_{\mathrm{inv}} * D * U - D \quad\text{and}\quad D + \omega_D = U_{\mathrm{inv}} * D * U,$$
   - **Universal Graded Operator Maurer–Cartan Curvature Identity:**
     $$\mathrm{anticomm}\,D\,\omega_D + \omega_D * \omega_D = U_{\mathrm{inv}} * (D * D) * U - D * D,$$
   - **Identical Graded Flatness for Involutive Dirac/Cartan Operators ($F * F = 1$):**
     For $\omega_F := \mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,F)\,U\,U_{\mathrm{inv}}$,
     $$\mathrm{anticomm}\,F\,\omega_F + \omega_F * \omega_F = 0.$$ -/
theorem operator_differential_forms_and_maurer_cartan_conjugation_curvature_bridge
    {B : Type*} [Ring B]
    {R₀ : Type*} [AddCommGroup R₀]
    (τ : B →+ R₀)
    (hτ : InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.IsCyclic τ)
    {F : B} (hF : F * F = 1) (D X Y U Uinv : B)
    (hU_right : U * Uinv = 1) (hU_left : Uinv * U = 1) :
    (InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F (X * Y) =
       InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F X * Y +
         X * InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F Y ∧
     InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.operatorAnticommutator F
       (InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F X) = 0 ∧
     InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.operatorCommutator F
       (InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F X *
         InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F Y) = 0 ∧
     InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.gradedTrace τ F
       (InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F X) = 0 ∧
     InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.gradedTrace τ F
       (InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F X *
         InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F Y) =
       -InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace.gradedTrace τ F
         (InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F Y *
           InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential F X)) ∧
    (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv =
       Uinv * D * U - D ∧
     D + peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv =
       Uinv * D * U ∧
     anticomm D (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv) +
       peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv *
         peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv =
       Uinv * (D * D) * U - D * D ∧
     anticomm F (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm F) U Uinv) +
       peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm F) U Uinv *
         peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm F) U Uinv = 0) := by
  have hleib :=
    InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential_leibniz F X Y
  have hodd :=
    InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential_anticommutes hF X
  have heven :=
    InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.connesDifferential_product_commutes hF X Y
  have htr0 :=
    InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.cyclic_gradedTrace_differential_eq_zero
      τ hτ hF X
  have htr_skew :=
    InfoGeometry.OperatorAlgebra.NoncommutativeConnesCalculus.cyclic_gradedTrace_differential_pair_skew
      τ hτ hF X Y
  have hmc_eq :
      peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv =
        Uinv * D * U - D := by
    unfold peirceMaurerCartanForm InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    calc
      Uinv * (D * U - U * D) = Uinv * D * U - (Uinv * U) * D := by noncomm_ring
      _ = Uinv * D * U - 1 * D := by rw [hU_left]
      _ = Uinv * D * U - D := by rw [one_mul]
  have hmc_shift :
      D + peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv =
        Uinv * D * U := by
    rw [hmc_eq]
    abel
  have hmc_curv :
      anticomm D (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv) +
        peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv *
          peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm D) U Uinv =
        Uinv * (D * D) * U - D * D := by
    rw [hmc_eq]
    unfold anticomm
    calc
      (D * (Uinv * D * U - D) + (Uinv * D * U - D) * D) +
          (Uinv * D * U - D) * (Uinv * D * U - D)
        = Uinv * D * (U * Uinv) * D * U - D * D := by noncomm_ring
      _ = Uinv * D * 1 * D * U - D * D := by rw [hU_right]
      _ = Uinv * (D * D) * U - D * D := by noncomm_ring
  have hmc_F_flat :
      anticomm F (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm F) U Uinv) +
        peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm F) U Uinv *
          peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm F) U Uinv = 0 := by
    have hmc_F_eq :
        peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm F) U Uinv =
          Uinv * F * U - F := by
      unfold peirceMaurerCartanForm InfoGeometry.OperatorAlgebra.PeirceSpine.comm
      calc
        Uinv * (F * U - U * F) = Uinv * F * U - (Uinv * U) * F := by noncomm_ring
        _ = Uinv * F * U - 1 * F := by rw [hU_left]
        _ = Uinv * F * U - F := by rw [one_mul]
    rw [hmc_F_eq]
    unfold anticomm
    calc
      (F * (Uinv * F * U - F) + (Uinv * F * U - F) * F) +
          (Uinv * F * U - F) * (Uinv * F * U - F)
        = Uinv * F * (U * Uinv) * F * U - F * F := by noncomm_ring
      _ = Uinv * F * 1 * F * U - F * F := by rw [hU_right]
      _ = Uinv * (F * F) * U - F * F := by noncomm_ring
      _ = Uinv * 1 * U - 1 := by rw [hF]
      _ = Uinv * U - 1 := by rw [mul_one]
      _ = 1 - 1 := by rw [hU_left]
      _ = 0 := sub_self 1
  exact ⟨⟨hleib, hodd, heven, htr0, htr_skew⟩, ⟨hmc_eq, hmc_shift, hmc_curv, hmc_F_flat⟩⟩

/-- **Peirce Operator Maurer–Cartan Dichotomy (Ungraded Projector Curvature vs. Cartan-Graded Flatness) &
Soldered Tetrad–Spin-Connection Differential Calculus:**
For any Peirce idempotent $P * P = P$ and $A, C \in B$:
1. **Unipotent Inverse Pair ($U = 1 + N_+$, $U_{\mathrm{inv}} = 1 - N_+$):**
   $(1 + \mathrm{conePlus}\,P\,A) * (1 - \mathrm{conePlus}\,P\,A) = 1$ and
   $(1 - \mathrm{conePlus}\,P\,A) * (1 + \mathrm{conePlus}\,P\,A) = 1$.
2. **Ungraded Projector Maurer–Cartan Operator ($\omega_P = N_+$) & Non-Flat Curvature (`PeirceMaurerCartanCurvatureWitness`):**
   Under $d_P = \mathrm{comm}\,P$, the left Maurer–Cartan operator 1-form is
   $\omega_P = \mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,P)\,(1 + N_+)\,(1 - N_+) = N_+$,
   whose ungraded commutator curvature is $\mathrm{comm}\,P\,\omega_P + \omega_P * \omega_P = N_+$
   (witnessed non-zero on $2 \times 2$ integer matrices by `peirce_matrix_unipotent_maurer_cartan_nonflat`).
3. **Cartan-Graded Involution Maurer–Cartan Operator ($\omega_{S_P} = -2 N_+$) & Exact Graded Flatness:**
   Under the DeWitt Cartan grading involution $S_P = \mathrm{invS}\,P = P - (1 - P)$ ($S_P * S_P = 1$),
   the left Maurer–Cartan operator 1-form is
   $\omega_{S_P} := \mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,(\mathrm{invS}\,P))\,(1 + N_+)\,(1 - N_+) = -((2 : \mathbb{Z}) \bullet N_+)$,
   shifting $S_P$ by $\omega_{S_P}$ conjugates $S_P$ by $1 \pm N_+$
   ($\mathrm{invS}\,P + \omega_{S_P} = (1 - N_+) * \mathrm{invS}\,P * (1 + N_+)$),
   and its graded operator Maurer–Cartan curvature vanishes identically:
   $$\mathrm{anticomm}\,(\mathrm{invS}\,P)\,\omega_{S_P} + \omega_{S_P} * \omega_{S_P} = 0.$$
4. **Soldered Tetrad ($\Phi, J$) and Uncertainty Spin Connection ($\Sigma = [N_+, N_-]$) Operator Differential Curvature & Bianchi Laws:**
   - $\mathrm{comm}\,P\,(\mathrm{genPhi}\,P\,A\,C) + \mathrm{genPhi}\,P\,A\,C * \mathrm{genPhi}\,P\,A\,C = \mathrm{genJ}\,P\,A\,C + \mathrm{genV}\,P\,A\,C$,
   - $\mathrm{comm}\,P\,(\mathrm{genJ}\,P\,A\,C) + \mathrm{genJ}\,P\,A\,C * \mathrm{genJ}\,P\,A\,C = \mathrm{genPhi}\,P\,A\,C - \mathrm{genV}\,P\,A\,C$,
   - $\mathrm{comm}\,P\,(\mathrm{genSig}\,P\,A\,C) = 0$,
     $\mathrm{comm}\,P\,(\mathrm{genSig}\,P\,A\,C) + \mathrm{genSig}\,P\,A\,C * \mathrm{genSig}\,P\,A\,C = \mathrm{genV}\,P\,A\,C * \mathrm{genV}\,P\,A\,C$,
   - $\mathrm{comm}\,P\,(\mathrm{genV}\,P\,A\,C * \mathrm{genV}\,P\,A\,C) = 0$ and
     $\mathrm{comm}\,(\mathrm{genSig}\,P\,A\,C)\,(\mathrm{genV}\,P\,A\,C * \mathrm{genV}\,P\,A\,C) = 0$. -/
theorem peirce_operator_maurer_cartan_ungraded_vs_cartan_graded_and_tetrad_curvature_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P) (A C : B) :
    ((1 + conePlus P A) * (1 - conePlus P A) = 1 ∧
     (1 - conePlus P A) * (1 + conePlus P A) = 1) ∧
    (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P)
       (1 + conePlus P A) (1 - conePlus P A) = conePlus P A ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
       (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P)
         (1 + conePlus P A) (1 - conePlus P A)) +
       peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P)
         (1 + conePlus P A) (1 - conePlus P A) *
         peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P)
           (1 + conePlus P A) (1 - conePlus P A) =
       conePlus P A ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm curvatureWitnessP
         (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm curvatureWitnessP)
           (1 + conePlus curvatureWitnessP curvatureWitnessA)
           (1 - conePlus curvatureWitnessP curvatureWitnessA)) +
       peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm curvatureWitnessP)
           (1 + conePlus curvatureWitnessP curvatureWitnessA)
           (1 - conePlus curvatureWitnessP curvatureWitnessA) *
         peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm curvatureWitnessP)
           (1 + conePlus curvatureWitnessP curvatureWitnessA)
           (1 - conePlus curvatureWitnessP curvatureWitnessA) ≠ 0) ∧
    (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P))
       (1 + conePlus P A) (1 - conePlus P A) =
       (2 : ℤ) • conePlus P A ∧
     invS P + peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P))
       (1 + conePlus P A) (1 - conePlus P A) =
       (1 - conePlus P A) * invS P * (1 + conePlus P A) ∧
     anticomm (invS P)
         (peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P))
           (1 + conePlus P A) (1 - conePlus P A)) +
       peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P))
         (1 + conePlus P A) (1 - conePlus P A) *
         peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm (invS P))
           (1 + conePlus P A) (1 - conePlus P A) = 0) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (genPhi P A C) +
       genPhi P A C * genPhi P A C = genJ P A C + genV P A C ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (genJ P A C) +
       genJ P A C * genJ P A C = genPhi P A C - genV P A C ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (genSig P A C) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (genSig P A C) +
       genSig P A C * genSig P A C = genV P A C * genV P A C ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P (genV P A C * genV P A C) = 0 ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genV P A C * genV P A C) = 0) := by
  refine ⟨⟨by peirce_nf hP, by peirce_nf hP⟩,
    ⟨by unfold peirceMaurerCartanForm; peirce_nf hP,
     peirce_unipotent_maurer_cartan_curvature_eq_conePlus hP A,
     peirce_matrix_unipotent_maurer_cartan_nonflat⟩,
    ⟨by unfold peirceMaurerCartanForm; peirce_nf hP,
     by unfold peirceMaurerCartanForm; peirce_nf hP,
     by unfold peirceMaurerCartanForm; peirce_nf hP⟩,
    ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
     by peirce_nf hP, by peirce_nf hP, by peirce_nf hP⟩⟩

/-- **Non-Abelian Operator Maurer–Cartan Inverse/Curl Law, Peirce Operator Differential Forms,
Dually Flat Amari–Nagaoka QGT Connections, & Möbius–Bruhat 5-Graded Kantor Pullback Bridge:**
In any unital associative operator ring `B` with Peirce idempotent $P * P = P$:
1. **Non-Abelian Operator Maurer–Cartan Inverse Derivation, Flow Reconstruction, & Zero-Curl Identity (`Archetype XVI`):**
   For any inverse operator pair $(U, U_{\mathrm{inv}})$ ($U * U_{\mathrm{inv}} = 1$, $U_{\mathrm{inv}} * U = 1$)
   and derivation generators $H_1, H_2 \in B$:
   - **Inverse Derivation Law:**
     $\mathrm{comm}\,H_1\,U_{\mathrm{inv}} = -(U_{\mathrm{inv}} * \mathrm{comm}\,H_1\,U * U_{\mathrm{inv}})
     = -(\mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,H_1)\,U\,U_{\mathrm{inv}} * U_{\mathrm{inv}})$,
   - **Left Maurer–Cartan Flow Reconstruction:**
     $U * \mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,H_1)\,U\,U_{\mathrm{inv}} = \mathrm{comm}\,H_1\,U$,
   - **Operator Curl of Reconstructed Maurer–Cartan Flows (Jacobi Curvature Law):**
     $$\mathrm{comm}\,H_1\,\big(U * \mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,H_2)\,U\,U_{\mathrm{inv}}\big)
       - \mathrm{comm}\,H_2\,\big(U * \mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,H_1)\,U\,U_{\mathrm{inv}}\big)
       = \mathrm{comm}\,(\mathrm{comm}\,H_1\,H_2)\,U,$$
     which vanishes identically ($\dots = 0$) whenever $\mathrm{comm}\,H_1\,H_2 = 0$.
2. **All Differential Forms as Peirce Operator Derivations & Dually Flat Amari–Nagaoka QGT Connections (`A₂, A₄, A₂₆`):**
   - $\mathrm{comm}\,P\,(\mathrm{comm}\,P\,X) = \mathrm{oddGrade}\,P\,X$,
     $X - \mathrm{comm}\,P\,(\mathrm{comm}\,P\,X) = \mathrm{evenGrade}\,P\,X$,
     $\mathrm{comm}\,P\,(\mathrm{comm}\,P\,(\mathrm{comm}\,P\,X)) = \mathrm{comm}\,P\,X$, and
     $\mathrm{comm}\,P\,(\mathrm{comm}\,P\,A * \mathrm{comm}\,P\,C) = 0$;
   - $\mathrm{qgtPlus}\,P\,A\,C + \mathrm{qgtMinus}\,P\,A\,C = \mathrm{genV}\,P\,A\,C$,
     $\mathrm{qgtPlus}\,P\,A\,C - \mathrm{qgtMinus}\,P\,A\,C = \mathrm{genSig}\,P\,A\,C$,
     $\mathrm{connPlus}\,P\,A\,C\,X + \mathrm{connMinus}\,P\,A\,C\,X = \mathrm{connV}\,P\,A\,C\,X$,
     $\mathrm{connPlus}\,P\,A\,C\,X - \mathrm{connMinus}\,P\,A\,C\,X = \mathrm{connSig}\,P\,A\,C\,X$, and
     $\mathrm{connPlus}\,P\,A\,C\,(\mathrm{connMinus}\,P\,A\,C\,X) = \mathrm{connMinus}\,P\,A\,C\,(\mathrm{connPlus}\,P\,A\,C\,X)$.
3. **Two-Cone Möbius–Bruhat Maurer–Cartan Pullbacks & 5-Graded Kantor–Koecher–Tits Charge Spectrum (`A₅₁–A₅₃`):**
   - $\mathrm{comm}\,P\,\big((1 + \mathrm{conePlus}\,P\,A) * (1 - \mathrm{coneMinus}\,P\,C)\big) = \mathrm{genPhi}\,P\,A\,C$,
   - $\mathrm{peirceMaurerCartanForm}\,(\mathrm{comm}\,P)\,\big((1 + \mathrm{conePlus}\,P\,A) * (1 - \mathrm{coneMinus}\,P\,C)\big)\,\big((1 + \mathrm{coneMinus}\,P\,C) * (1 - \mathrm{conePlus}\,P\,A)\big)
     = \mathrm{genPhi}\,P\,A\,C - \mathrm{genSig}\,P\,A\,C - \mathrm{genV}\,P\,A\,C * \mathrm{coneMinus}\,P\,C$,
   - $\mathrm{comm}\,P\,\big((1 + \mathrm{conePlus}\,P\,A) * (1 - \mathrm{coneMinus}\,P\,C)\big) * \big((1 + \mathrm{coneMinus}\,P\,C) * (1 - \mathrm{conePlus}\,P\,A)\big)
     = \mathrm{genPhi}\,P\,A\,C + \mathrm{genSig}\,P\,A\,C - \mathrm{genV}\,P\,A\,C * \mathrm{conePlus}\,P\,A$,
   - $\mathrm{chargeIter}\,P\,(\mathrm{cornerOperatorSum}\,P\,A\,C)\,3\,X - \mathrm{chargeIter}\,P\,(\mathrm{cornerOperatorSum}\,P\,A\,C)\,1\,X = (6 : \mathbb{Z}) \bullet (\mathrm{sandwich}\,(\mathrm{conePlus}\,P\,A)\,(\mathrm{conePlus}\,P\,A)\,X - \mathrm{sandwich}\,(\mathrm{coneMinus}\,P\,C)\,(\mathrm{coneMinus}\,P\,C)\,X)$ and
     $\mathrm{chargeIter}\,P\,(\mathrm{cornerOperatorSum}\,P\,A\,C)\,5\,X - (5 : \mathbb{Z}) \bullet \mathrm{chargeIter}\,P\,(\mathrm{cornerOperatorSum}\,P\,A\,C)\,3\,X + (4 : \mathbb{Z}) \bullet \mathrm{chargeIter}\,P\,(\mathrm{cornerOperatorSum}\,P\,A\,C)\,1\,X = 0$. -/
theorem operator_maurer_cartan_galois_bruhat_pullback_amari_qgt_and_nonabelian_curl_bridge
    {B : Type*} [Ring B] {P : B} (hP : P * P = P)
    (H₁ H₂ U Uinv A C X : B)
    (hU_right : U * Uinv = 1) (hU_left : Uinv * U = 1) :
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ Uinv =
       -(Uinv * InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ U * Uinv) ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ Uinv =
       -(peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁) U Uinv * Uinv) ∧
     U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁) U Uinv =
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ U ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁
       (U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂) U Uinv) -
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂
       (U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁) U Uinv) =
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm
         (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ H₂) U ∧
     (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ H₂ = 0 →
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁
         (U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂) U Uinv) -
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂
         (U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁) U Uinv) = 0)) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
       (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X) = oddGrade P X ∧
     X - InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
       (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X) = evenGrade P X ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
       (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
         (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X)) =
       InfoGeometry.OperatorAlgebra.PeirceSpine.comm P X ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
       (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P A *
         InfoGeometry.OperatorAlgebra.PeirceSpine.comm P C) = 0 ∧
     qgtPlus P A C + qgtMinus P A C = genV P A C ∧
     qgtPlus P A C - qgtMinus P A C = genSig P A C ∧
     connPlus P A C X + connMinus P A C X = connV P A C X ∧
     connPlus P A C X - connMinus P A C X = connSig P A C X ∧
     connPlus P A C (connMinus P A C X) = connMinus P A C (connPlus P A C X) ∧
     connPlus P A C (connMinus P A C X) =
       -(qgtPlus P A C * X * qgtMinus P A C + qgtMinus P A C * X * qgtPlus P A C)) ∧
    (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
       ((1 + conePlus P A) * (1 - coneMinus P C)) = genPhi P A C ∧
     peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm P)
       ((1 + conePlus P A) * (1 - coneMinus P C))
       ((1 + coneMinus P C) * (1 - conePlus P A)) =
       genPhi P A C - genSig P A C - genV P A C * coneMinus P C ∧
     InfoGeometry.OperatorAlgebra.PeirceSpine.comm P
       ((1 + conePlus P A) * (1 - coneMinus P C)) *
       ((1 + coneMinus P C) * (1 - conePlus P A)) =
       genPhi P A C + genSig P A C - genV P A C * conePlus P A ∧
     chargeIter P (cornerOperatorSum P A C) 3 X -
       chargeIter P (cornerOperatorSum P A C) 1 X =
       (6 : ℤ) • (sandwich (conePlus P A) (conePlus P A) X -
         sandwich (coneMinus P C) (coneMinus P C) X) ∧
     chargeIter P (cornerOperatorSum P A C) 5 X -
       (5 : ℤ) • chargeIter P (cornerOperatorSum P A C) 3 X +
       (4 : ℤ) • chargeIter P (cornerOperatorSum P A C) 1 X = 0) := by
  have hinv_comm :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ Uinv =
        -(Uinv * InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ U * Uinv) := by
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    calc
      H₁ * Uinv - Uinv * H₁
        = (Uinv * U) * H₁ * Uinv - Uinv * H₁ * (U * Uinv) := by
            rw [hU_left, hU_right]; noncomm_ring
      _ = -(Uinv * (H₁ * U - U * H₁) * Uinv) := by noncomm_ring
  have hinv_mc :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ Uinv =
        -(peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁) U Uinv * Uinv) := by
    rw [hinv_comm]
    unfold peirceMaurerCartanForm
    noncomm_ring
  have hflow1 :
      U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁) U Uinv =
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ U := by
    unfold peirceMaurerCartanForm
    calc
      U * (Uinv * InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ U)
        = (U * Uinv) * InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ U := by noncomm_ring
      _ = 1 * InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ U := by rw [hU_right]
      _ = InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ U := one_mul _
  have hflow2 :
      U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂) U Uinv =
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂ U := by
    unfold peirceMaurerCartanForm
    calc
      U * (Uinv * InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂ U)
        = (U * Uinv) * InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂ U := by noncomm_ring
      _ = 1 * InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂ U := by rw [hU_right]
      _ = InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂ U := one_mul _
  have hcurl :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁
        (U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂) U Uinv) -
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂
        (U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁) U Uinv) =
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm
          (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ H₂) U := by
    rw [hflow1, hflow2]
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    noncomm_ring
  have hcurl_zero :
      InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁ H₂ = 0 →
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁
          (U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂) U Uinv) -
        InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₂
          (U * peirceMaurerCartanForm (InfoGeometry.OperatorAlgebra.PeirceSpine.comm H₁) U Uinv) = 0 := by
    intro hcomm0
    rw [hcurl, hcomm0]
    unfold InfoGeometry.OperatorAlgebra.PeirceSpine.comm
    noncomm_ring
  have hA26 := archetype_A26_qgt_inner_derivations hP A C X
  refine ⟨⟨hinv_comm, hinv_mc, hflow1, hcurl, hcurl_zero⟩,
    ⟨by peirce_nf hP, by peirce_nf hP, by peirce_nf hP, by peirce_nf hP,
     by simp only [qgtPlus, qgtMinus]; peirce_nf hP,
     by simp only [qgtPlus, qgtMinus]; peirce_nf hP,
     hA26.1, hA26.2.1, hA26.2.2.2.2.1, hA26.2.2.2.2.2.2.1⟩,
    ⟨comm_two_cone_product hP A C,
     by unfold peirceMaurerCartanForm; exact two_cone_left_pullback hP A C,
     two_cone_right_pullback hP A C,
     charge_iter_cubic_difference hP A C X,
     charge_iter_fifth_annihilator hP A C X⟩⟩

end InfoGeometry.Algebra.Zorn.TetractysZeemanZornAssociatorBridge
