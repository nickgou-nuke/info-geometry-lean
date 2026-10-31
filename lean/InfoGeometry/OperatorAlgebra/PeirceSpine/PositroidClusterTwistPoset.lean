/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.PhaseConjugateSteinberg
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset
import InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge

/-!
# Stage D₂₀: Non-Commutative Peirce Charts, Bicolored Shears,
# Corner-Product Identities, Conjugation, and Frozen-Factor Invertibility

This module formalizes operator identities over an arbitrary non-commutative ring
`B` and star-ring `B`. The local `P₁`–`P₁₀` labels order these identities by their
Lean dependencies; references to Grassmannian, positroid, plabic, cluster, and
Muller–Speyer constructions are motivation only. This file defines no classical
positroid or plabic graph object and proves no map to those structures. All formal
claims are the displayed identities in Peirce operator algebra:

* `P₁` (`opSchubertChart`, `opQuasiPlucker11`, `opQuasiPlucker00`):
  A conjugated Peirce chart expression, its idempotency, and its two Peirce corner
  readouts. Their names are mnemonic; no Grassmannian interpretation is asserted.
* `P₂` (`opPluckerBivector`, `nc_three_term_plucker_exchange`):
  A non-commutative operator difference-product
  `opPluckerBivector P X₁ X₂ Y₁ Y₂ = (projChartPlus P X₁ - projChartPlus P X₂) * (projChartMinus P Y₁ - projChartMinus P Y₂)`,
  with distributive difference-product expansions. No exterior-algebra or classical
  Plücker relation is claimed.
* `P₃` (`plabicWhiteShear`, `plabicBlackShear`, `plabicTripWB`, `plabicTripBW`):
  Bicolored white (`1 + N₊`) and black (`1 - N₋`) vertex shears, ordered rules-of-the-road
  trip operators `plabicTripWB` and `plabicTripBW`, exact non-commutativity witness
  `comm (plabicWhiteShear P A) (plabicBlackShear P C) = -genSig P A C`, and inverse
  trip cancellation.
* `P₄` (`plabicFrozenTarget`, `plabicFrozenSource`):
  Target-seed (`steinbergBraid`, `1 - Q₊`) versus source-seed (`steinbergBraidDual`, `1 - Q₋`)
  duality, exact frozen-unit discrepancy `plabicFrozenTarget - plabicFrozenSource = -genSig`,
  and joint factorization of `zetaFactor P A C = 1 - genV P A C`.
* `P₅` (`nc_cluster_mutation_exchange`):
  Non-commutative Peirce binomial identities:
  `(1 - genPhi P A C) * (1 + genPhi P A C) = (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C)`
  (splitting into two orthogonal Peirce-corner binomial summands) and the Cayley–Weyl
  exchange `weylJ P A C * weylJInv P A C = (1 - genV P A C) + idempotencyDefect (genV P A C)`.
* `P₆` (`relabeledConj`, `relabeled_plabic_conjugation_covariance`):
  Boundary-relabeled conjugation `U_inv * T * U` (`U_inv * U = 1`, `U * U_inv = 1`),
  preservation of idempotency, and covariant transport of `conePlus`, `coneMinus`,
  `plabicTripWB`, `plabicTripBW`, and `genV`.
* `P₇` (`quasi_coincidence_up_to_frozen_units`):
  Quasi-coincidence of target and source Steinberg braids up to left-multiplication by
  their respective frozen corner operators:
  `steinbergBraid P A C = weylJ P A C + plabicFrozenTarget P A C * conePlus P A`,
  `steinbergBraidDual P A C = weylJ P A C - plabicFrozenSource P A C * coneMinus P C`,
  and `steinbergBraid P A C - steinbergBraidDual P A C = plabicFrozenTarget P A C * conePlus P A + plabicFrozenSource P A C * coneMinus P C`.
* `P₈` (`peircePermutedTwist`, `peircePermutedTwistInv`):
  An intrinsic non-commutative conjugation map
  `peircePermutedTwist P A C X = steinbergBraid P A C * parityConj P X * steinbergBraidInv P A C`,
  its unconditional two-sided inverse, multiplicativity, invariance of `genV P A C`,
  and inversion of `steinbergBraid P A C`.
* `P₉` (`seedPositivityForm`, `seedPositivityForm_hermitian_squares_and_twist_transfer`):
  The operator `star X * genV P A (star A) * X`, its decomposition into two
  non-commutative Hermitian squares, its Peirce corner-projected Hermitian squares,
  and proper star-ring kernel characterization in `[Ring B] [StarRing B]`.
* `P₁₀` (`frozen_factor_invertibility_and_sheaf_bridge`):
  Conditional two-sided inverses for two factors when their product has a two-sided
  inverse, plus an exact identity with the existing sheaf Laplacian. This is an
  algebraic factorization, not a localization theorem.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Core.IdempotentGraphGrassmannian

/-! ### 1. The 10-Stage Peirce-Operator Dependency DAG (`P₁ → P₁₀`)

The stage labels record dependencies among the operator identities below. They do
not define positroid, cluster, or plabic combinatorial structures. -/

/-- Ten dependency stages for the operator identities below. -/
inductive PositroidClusterStage : Type
  | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10
  deriving DecidableEq, Repr

namespace PositroidClusterStage

/-- Topological rank (1 through 10) of each archetype stage in `D₂₀`. -/
def rank : PositroidClusterStage → ℕ
  | P1 => 1
  | P2 => 2
  | P3 => 3
  | P4 => 4
  | P5 => 5
  | P6 => 6
  | P7 => 7
  | P8 => 8
  | P9 => 9
  | P10 => 10

theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

instance : LinearOrder PositroidClusterStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed edges of the 10-stage causal DAG (`P₁ → P₁₀`). -/
def causalEdge : PositroidClusterStage → PositroidClusterStage → Prop
  | P1, P2 => True
  | P1, P3 => True
  | P2, P5 => True
  | P3, P4 => True
  | P3, P6 => True
  | P4, P5 => True
  | P4, P7 => True
  | P5, P7 => True
  | P6, P8 => True
  | P7, P8 => True
  | P8, P9 => True
  | P7, P10 => True
  | P8, P10 => True
  | P9, P10 => True
  | _, _ => False

/-- Every directed edge strictly increases the stage rank. -/
theorem causalEdge_strict_rank_mono {s t : PositroidClusterStage} (h : causalEdge s t) :
    rank s < rank t := by
  cases s <;> cases t <;> first | decide | cases h

/-- The ranked causal edge relation is irreflexive (acyclic). -/
theorem causalEdge_irrefl (s : PositroidClusterStage) : ¬ causalEdge s s := by
  intro h
  exact Nat.lt_irrefl (rank s) (causalEdge_strict_rank_mono h)

end PositroidClusterStage

/-! ### 2. Core Non-Commutative Operator Definitions (`P₁ → P₁₀`) -/

variable {B : Type*} [Ring B]

/-- **Archetype P₁**: A conjugated Peirce chart expression and its `(1,1)` and `(0,0)` corners.
The names are organizational; this is not a classical Grassmannian chart. -/
def opSchubertChart (P A C : B) : B :=
  conjMinus P C (projChartPlus P A)

def opQuasiPlucker11 (P A C : B) : B :=
  peirce11 P (opSchubertChart P A C)

def opQuasiPlucker00 (P A C : B) : B :=
  peirce00 P (opSchubertChart P A C)

/-- **Archetype P₂**: Difference-product of two Peirce chart differences. No exterior-algebra
or classical Plücker carrier is defined here. -/
def opPluckerBivector (P X₁ X₂ Y₁ Y₂ : B) : B :=
  (projChartPlus P X₁ - projChartPlus P X₂) * (projChartMinus P Y₁ - projChartMinus P Y₂)

/-- **Archetype P₃ (`plabicWhiteShear`, `plabicBlackShear`, `plabicTripWB`, `plabicTripBW`)**:
Bicolored plabic internal vertex shears (white upper shear `1 + N₊` and black lower shear
`1 - N₋`) and the two ordered two-turn trip operators `W * B` and `B * W`. -/
def plabicWhiteShear (P A : B) : B := 1 + conePlus P A
def plabicBlackShear (P C : B) : B := 1 - coneMinus P C
def plabicTripWB (P A C : B) : B := plabicWhiteShear P A * plabicBlackShear P C
def plabicTripBW (P A C : B) : B := plabicBlackShear P C * plabicWhiteShear P A

/-- **Archetype P₄ (`plabicFrozenTarget`, `plabicFrozenSource`)**:
Target-convention frozen corner operator `1 - Q₊` and source-convention frozen corner
operator `1 - Q₋`. -/
def plabicFrozenTarget (P A C : B) : B := 1 - qgtPlus P A C
def plabicFrozenSource (P A C : B) : B := 1 - qgtMinus P A C

/-- **Archetype P₆ (`relabeledConj`)**:
Boundary-relabeled conjugation action `U_inv * T * U` on an operator `T : B`. -/
def relabeledConj (U U_inv T : B) : B := U_inv * T * U

/-- **Archetype P₈**: Noncommutative conjugation combining the existing parity and Steinberg
operators. This name does not assert a classical Muller–Speyer twist construction. -/
def peircePermutedTwist (P A C X : B) : B :=
  steinbergBraid P A C * parityConj P X * steinbergBraidInv P A C

def peircePermutedTwistInv (P A C X : B) : B :=
  parityConj P (steinbergBraidInv P A C * X * steinbergBraid P A C)

/-! ### 3. Stage D₂₀ Lemmas & Theorems for Archetypes `P₁ → P₁₀` -/

/-- **Lemma P₁.1 (`opSchubertChart_idempotent_and_quasiPlucker_minors`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. `opSchubertChart P A C` is an idempotent in `B`;
2. Its `(1, 1)` Peirce minor is `opQuasiPlucker11 P A C = P + qgtPlus P A C`;
3. Its `(0, 0)` Peirce minor is `opQuasiPlucker00 P A C = -qgtMinus P A C`;
4. Their difference is `opQuasiPlucker11 P A C - opQuasiPlucker00 P A C = P + genV P A C`;
5. Their sum is `opQuasiPlucker11 P A C + opQuasiPlucker00 P A C = P + genSig P A C`. -/
theorem opSchubertChart_idempotent_and_quasiPlucker_minors
    {P : B} (hP : P * P = P) (A C : B) :
    opSchubertChart P A C * opSchubertChart P A C = opSchubertChart P A C ∧
    opQuasiPlucker11 P A C = P + qgtPlus P A C ∧
    opQuasiPlucker00 P A C = -qgtMinus P A C ∧
    opQuasiPlucker11 P A C - opQuasiPlucker00 P A C = P + genV P A C ∧
    opQuasiPlucker11 P A C + opQuasiPlucker00 P A C = P + genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [opSchubertChart, opQuasiPlucker11, opQuasiPlucker00,
      conjMinus, projChartPlus, qgtPlus, qgtMinus]; peirce_nf hP)

/-- **Lemma P₂.1 (`nc_three_term_plucker_exchange`)**:
For any idempotent `P` (`P * P = P`) and any parameters `X₁, X₂, X₃, X₄, Y₁, Y₂, Y₃, Y₄ : B`:
1. `opPluckerBivector P X₁ X₂ Y₁ Y₂ = qgtPlus P (X₁ - X₂) (Y₁ - Y₂)`;
2. **Non-Commutative Multiplicative Three-Term Plücker Subdivision in `P B P`:**
   `opPluckerBivector P X₁ X₃ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄ = opPluckerBivector P X₁ X₂ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄ + opPluckerBivector P X₂ X₃ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄`;
3. **Four-Point Non-Commutative Bilinear Plücker Expansion:**
   `opPluckerBivector P X₁ X₃ Y₁ Y₃ = opPluckerBivector P X₁ X₂ Y₁ Y₂ + opPluckerBivector P X₂ X₃ Y₂ Y₃ + opPluckerBivector P X₁ X₂ Y₂ Y₃ + opPluckerBivector P X₂ X₃ Y₁ Y₂`;
4. **Two-Sheeted Cross-Ratio Three-Term Subdivision:**
   `operatorCrossRatio P X₁ X₃ Y₁ Y₂ = operatorCrossRatio P X₁ X₂ Y₁ Y₂ + operatorCrossRatio P X₂ X₃ Y₁ Y₂`. -/
theorem nc_three_term_plucker_exchange
    {P : B} (hP : P * P = P) (X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : B) :
    opPluckerBivector P X₁ X₂ Y₁ Y₂ = qgtPlus P (X₁ - X₂) (Y₁ - Y₂) ∧
    opPluckerBivector P X₁ X₃ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄ =
      opPluckerBivector P X₁ X₂ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄ +
      opPluckerBivector P X₂ X₃ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄ ∧
    opPluckerBivector P X₁ X₃ Y₁ Y₃ =
      opPluckerBivector P X₁ X₂ Y₁ Y₂ + opPluckerBivector P X₂ X₃ Y₂ Y₃ +
      opPluckerBivector P X₁ X₂ Y₂ Y₃ + opPluckerBivector P X₂ X₃ Y₁ Y₂ ∧
    operatorCrossRatio P X₁ X₃ Y₁ Y₂ =
      operatorCrossRatio P X₁ X₂ Y₁ Y₂ + operatorCrossRatio P X₂ X₃ Y₁ Y₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [opPluckerBivector, operatorCrossRatio, projChartPlus, projChartMinus,
      qgtPlus];
      peirce_nf hP)

/-- **Lemma P₃.1 (`plabic_bicolored_trip_identities_and_nc_witness`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. `plabicTripWB P A C = 1 + genJ P A C - qgtPlus P A C`;
2. `plabicTripBW P A C = 1 + genJ P A C - qgtMinus P A C`;
3. **Exact Trip Commutator:** `comm (plabicWhiteShear P A) (plabicBlackShear P C) = -genSig P A C`
   and `plabicTripWB P A C - plabicTripBW P A C = -genSig P A C`;
4. **Two-Sided Trip Invertibility:**
   `plabicTripWB P A C * plabicTripBW P (-A) (-C) = 1` and
   `plabicTripBW P (-A) (-C) * plabicTripWB P A C = 1`;
5. **Explicit Non-Commutativity Witness:** Whenever `genSig P A C ≠ 0`, the white and black
   plabic vertex shears do not commute:
   `plabicWhiteShear P A * plabicBlackShear P C ≠ plabicBlackShear P C * plabicWhiteShear P A`. -/
theorem plabic_bicolored_trip_identities_and_nc_witness
    {P : B} (hP : P * P = P) (A C : B) :
    plabicTripWB P A C = 1 + genJ P A C - qgtPlus P A C ∧
    plabicTripBW P A C = 1 + genJ P A C - qgtMinus P A C ∧
    comm (plabicWhiteShear P A) (plabicBlackShear P C) = -genSig P A C ∧
    plabicTripWB P A C - plabicTripBW P A C = -genSig P A C ∧
    plabicTripWB P A C * plabicTripBW P (-A) (-C) = 1 ∧
    plabicTripBW P (-A) (-C) * plabicTripWB P A C = 1 ∧
    (genSig P A C ≠ 0 →
      plabicWhiteShear P A * plabicBlackShear P C ≠
        plabicBlackShear P C * plabicWhiteShear P A) := by
  have hComm : comm (plabicWhiteShear P A) (plabicBlackShear P C) = -genSig P A C := by
    simp only [plabicWhiteShear, plabicBlackShear]
    peirce_nf hP
  refine ⟨?_, ?_, hComm, ?_, ?_, ?_, ?_⟩
  · simp only [plabicTripWB, plabicWhiteShear, plabicBlackShear]; peirce_nf hP
  · simp only [plabicTripBW, plabicWhiteShear, plabicBlackShear]; peirce_nf hP
  · simp only [plabicTripWB, plabicTripBW, plabicWhiteShear, plabicBlackShear]; peirce_nf hP
  · simp only [plabicTripWB, plabicTripBW, plabicWhiteShear, plabicBlackShear]; peirce_nf hP
  · simp only [plabicTripWB, plabicTripBW, plabicWhiteShear, plabicBlackShear]; peirce_nf hP
  · intro hSig hEq
    have hZero : comm (plabicWhiteShear P A) (plabicBlackShear P C) = 0 := by
      unfold comm
      rw [hEq, sub_self]
    rw [hComm, neg_eq_zero] at hZero
    exact hSig hZero

/-- **Lemma P₄.1 (`plabic_target_source_seed_duality`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. The target and source frozen operators differ by `-genSig P A C`:
   `plabicFrozenTarget P A C - plabicFrozenSource P A C = -genSig P A C`;
2. Their sum is `plabicFrozenTarget P A C + plabicFrozenSource P A C = (2 : ℤ) • 1 - genV P A C`;
3. Both ordered products of the target and source frozen operators reconstruct the same
   two-sheeted coordinate factor `zetaFactor P A C = 1 - genV P A C`:
   `plabicFrozenTarget P A C * plabicFrozenSource P A C = zetaFactor P A C` and
   `plabicFrozenSource P A C * plabicFrozenTarget P A C = zetaFactor P A C`;
4. The target and source frozen operators commute (`comm (plabicFrozenTarget P A C) (plabicFrozenSource P A C) = 0`). -/
theorem plabic_target_source_seed_duality
    {P : B} (hP : P * P = P) (A C : B) :
    plabicFrozenTarget P A C - plabicFrozenSource P A C = -genSig P A C ∧
    plabicFrozenTarget P A C + plabicFrozenSource P A C = (2 : ℤ) • (1 : B) - genV P A C ∧
    plabicFrozenTarget P A C * plabicFrozenSource P A C = zetaFactor P A C ∧
    plabicFrozenSource P A C * plabicFrozenTarget P A C = zetaFactor P A C ∧
    comm (plabicFrozenTarget P A C) (plabicFrozenSource P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [plabicFrozenTarget, plabicFrozenSource, zetaFactor,
      qgtPlus, qgtMinus]; peirce_nf hP)

/-- **Lemma P₅.1 (`nc_cluster_mutation_exchange`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Orthogonal Peirce-Corner Binomial Cluster Exchange:**
   `(1 - genPhi P A C) * (1 + genPhi P A C) = (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C)`,
   where the two binomial summands `M₊ = P - qgtPlus P A C` and
   `M₋ = (1 - P) - qgtMinus P A C = (1 - P) + opQuasiPlucker00 P A C` are mutually orthogonal
   (`M₊ * M₋ = 0` and `M₋ * M₊ = 0`);
2. **Skew-Generator Binomial Cluster Exchange:**
   `(1 - genJ P A C) * (1 + genJ P A C) = (P + qgtPlus P A C) + ((1 - P) + qgtMinus P A C)`;
3. **Cayley–Weyl Cluster Exchange:**
   `weylJ P A C * weylJInv P A C = 1 + idempotencyDefect (genV P A C)`. -/
theorem nc_cluster_mutation_exchange
    {P : B} (hP : P * P = P) (A C : B) :
    (1 - genPhi P A C) * (1 + genPhi P A C) =
      (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C) ∧
    (P - qgtPlus P A C) * ((1 - P) - qgtMinus P A C) = 0 ∧
    ((1 - P) - qgtMinus P A C) * (P - qgtPlus P A C) = 0 ∧
    (1 - genJ P A C) * (1 + genJ P A C) =
      (P + qgtPlus P A C) + ((1 - P) + qgtMinus P A C) ∧
    weylJ P A C * weylJInv P A C =
      1 + idempotencyDefect (genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [weylJ, weylJInv, qgtPlus, qgtMinus, idempotencyDefect]; peirce_nf hP)

/-- **Lemma P₆.1 (`relabeled_plabic_conjugation_covariance`)**:
Under an invertible boundary-relabeling operator `U` with two-sided inverse `U_inv`
(`U_inv * U = 1`, `U * U_inv = 1`):
1. `relabeledConj U U_inv` is multiplicative:
   `relabeledConj U U_inv (X * Y) = relabeledConj U U_inv X * relabeledConj U U_inv Y`;
2. If `P * P = P`, the relabeled idempotent `P_U = relabeledConj U U_inv P` satisfies `P_U * P_U = P_U`;
3. The Peirce cones, bicolored trips, and metric generator transport covariantly:
   - `conePlus (relabeledConj U U_inv P) (relabeledConj U U_inv A) = relabeledConj U U_inv (conePlus P A)`,
   - `coneMinus (relabeledConj U U_inv P) (relabeledConj U U_inv C) = relabeledConj U U_inv (coneMinus P C)`,
   - `plabicTripWB (relabeledConj U U_inv P) (relabeledConj U U_inv A) (relabeledConj U U_inv C) = relabeledConj U U_inv (plabicTripWB P A C)`,
   - `genV (relabeledConj U U_inv P) (relabeledConj U U_inv A) (relabeledConj U U_inv C) = relabeledConj U U_inv (genV P A C)`. -/
theorem relabeled_plabic_conjugation_covariance
    {P U U_inv : B} (hP : P * P = P) (hLeft : U_inv * U = 1) (hRight : U * U_inv = 1)
    (A C X Y : B) :
    relabeledConj U U_inv (X * Y) = relabeledConj U U_inv X * relabeledConj U U_inv Y ∧
    relabeledConj U U_inv P * relabeledConj U U_inv P = relabeledConj U U_inv P ∧
    conePlus (relabeledConj U U_inv P) (relabeledConj U U_inv A) =
      relabeledConj U U_inv (conePlus P A) ∧
    coneMinus (relabeledConj U U_inv P) (relabeledConj U U_inv C) =
      relabeledConj U U_inv (coneMinus P C) ∧
    plabicTripWB (relabeledConj U U_inv P) (relabeledConj U U_inv A) (relabeledConj U U_inv C) =
      relabeledConj U U_inv (plabicTripWB P A C) ∧
    genV (relabeledConj U U_inv P) (relabeledConj U U_inv A) (relabeledConj U U_inv C) =
      relabeledConj U U_inv (genV P A C) := by
  have hMul : ∀ S T : B,
      relabeledConj U U_inv (S * T) = relabeledConj U U_inv S * relabeledConj U U_inv T := by
    intro S T
    unfold relabeledConj
    calc
      U_inv * (S * T) * U = U_inv * S * (U * U_inv) * T * U := by
        rw [hRight]; noncomm_ring
      _ = (U_inv * S * U) * (U_inv * T * U) := by noncomm_ring
  have hOne : relabeledConj U U_inv 1 = 1 := by
    unfold relabeledConj
    rw [mul_one, hLeft]
  have hSub : ∀ S T : B,
      relabeledConj U U_inv (S - T) = relabeledConj U U_inv S - relabeledConj U U_inv T := by
    intro S T
    unfold relabeledConj
    noncomm_ring
  have hAdd : ∀ S T : B,
      relabeledConj U U_inv (S + T) = relabeledConj U U_inv S + relabeledConj U U_inv T := by
    intro S T
    unfold relabeledConj
    noncomm_ring
  have hConeP :
      conePlus (relabeledConj U U_inv P) (relabeledConj U U_inv A) =
        relabeledConj U U_inv (conePlus P A) := by
    unfold conePlus
    rw [hMul, hMul, hSub, hOne]
  have hConeM :
      coneMinus (relabeledConj U U_inv P) (relabeledConj U U_inv C) =
        relabeledConj U U_inv (coneMinus P C) := by
    unfold coneMinus
    rw [hMul, hMul, hSub, hOne]
  refine ⟨hMul X Y, ?_, hConeP, hConeM, ?_, ?_⟩
  · rw [← hMul P P, hP]
  · unfold plabicTripWB plabicWhiteShear plabicBlackShear
    rw [hMul, hAdd, hSub, hOne, hConeP, hConeM]
  · unfold genV anticomm
    rw [hAdd, hMul, hMul, hConeP, hConeM]

/-- **Lemma P₇.1 (`quasi_coincidence_up_to_frozen_units`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. The upper cone is rescaled by the target frozen operator exactly as by `zetaFactor`:
   `plabicFrozenTarget P A C * conePlus P A = zetaFactor P A C * conePlus P A`;
2. The lower cone is rescaled by the source frozen operator exactly as by `zetaFactor`:
   `plabicFrozenSource P A C * coneMinus P C = zetaFactor P A C * coneMinus P C`;
3. **Target and Source Steinberg Braids Rescaled by Frozen Corner Operators:**
   `steinbergBraid P A C = weylJ P A C + plabicFrozenTarget P A C * conePlus P A` and
   `steinbergBraidDual P A C = weylJ P A C - plabicFrozenSource P A C * coneMinus P C`;
4. **Frozen-Weighted Decomposition of the Seed Braid Difference:**
   `steinbergBraid P A C - steinbergBraidDual P A C = plabicFrozenTarget P A C * conePlus P A + plabicFrozenSource P A C * coneMinus P C`. -/
theorem quasi_coincidence_up_to_frozen_units
    {P : B} (hP : P * P = P) (A C : B) :
    plabicFrozenTarget P A C * conePlus P A = zetaFactor P A C * conePlus P A ∧
    plabicFrozenSource P A C * coneMinus P C = zetaFactor P A C * coneMinus P C ∧
    steinbergBraid P A C = weylJ P A C + plabicFrozenTarget P A C * conePlus P A ∧
    steinbergBraidDual P A C = weylJ P A C - plabicFrozenSource P A C * coneMinus P C ∧
    steinbergBraid P A C - steinbergBraidDual P A C =
      plabicFrozenTarget P A C * conePlus P A + plabicFrozenSource P A C * coneMinus P C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [plabicFrozenTarget, plabicFrozenSource, zetaFactor,
      steinbergBraid, steinbergBraidDual, weylJ, qgtPlus, qgtMinus]; peirce_nf hP)

/-- **Lemma P₈.1 (`peircePermutedTwist_automorphism_and_seed_transport`)**:
For any idempotent `P` (`P * P = P`) and any `A, C, X, Y : B` (with zero extra invertibility
assumptions):
1. `peircePermutedTwist P A C (peircePermutedTwistInv P A C X) = X` and
   `peircePermutedTwistInv P A C (peircePermutedTwist P A C X) = X`;
2. `peircePermutedTwist P A C (X * Y) = peircePermutedTwist P A C X * peircePermutedTwist P A C Y`;
3. `peircePermutedTwist P A C (genV P A C) = genV P A C` (invariance of the metric operator `V`);
4. `peircePermutedTwist P A C (steinbergBraid P A C) = steinbergBraidInv P A C`
   (the permuted twist maps the Steinberg braid to its exact inverse). -/
theorem peircePermutedTwist_automorphism_and_seed_transport
    {P : B} (hP : P * P = P) (A C X Y : B) :
    peircePermutedTwist P A C (peircePermutedTwistInv P A C X) = X ∧
    peircePermutedTwistInv P A C (peircePermutedTwist P A C X) = X ∧
    peircePermutedTwist P A C (X * Y) =
      peircePermutedTwist P A C X * peircePermutedTwist P A C Y ∧
    peircePermutedTwist P A C (genV P A C) = genV P A C ∧
    peircePermutedTwist P A C (steinbergBraid P A C) = steinbergBraidInv P A C := by
  rcases steinbergBraid_mul_inv hP A C with ⟨hBrR, hBrL⟩
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold peircePermutedTwist peircePermutedTwistInv parityConj
    calc
      steinbergBraid P A C *
          (invS P * (invS P * (steinbergBraidInv P A C * X * steinbergBraid P A C) * invS P) *
            invS P) *
          steinbergBraidInv P A C =
        (steinbergBraid P A C *
          ((invS P * invS P) * (steinbergBraidInv P A C * X * steinbergBraid P A C) *
            (invS P * invS P))) *
          steinbergBraidInv P A C := by noncomm_ring
      _ = (steinbergBraid P A C * steinbergBraidInv P A C) * X *
          (steinbergBraid P A C * steinbergBraidInv P A C) := by
        rw [hS2]; noncomm_ring
      _ = X := by rw [hBrR]; noncomm_ring
  · unfold peircePermutedTwist peircePermutedTwistInv parityConj
    calc
      invS P *
          (steinbergBraidInv P A C *
            (steinbergBraid P A C * (invS P * X * invS P) * steinbergBraidInv P A C) *
            steinbergBraid P A C) *
          invS P =
        invS P *
          ((steinbergBraidInv P A C * steinbergBraid P A C) * (invS P * X * invS P) *
            (steinbergBraidInv P A C * steinbergBraid P A C)) *
          invS P := by noncomm_ring
      _ = (invS P * invS P) * X * (invS P * invS P) := by
        rw [hBrL]; noncomm_ring
      _ = X := by rw [hS2]; noncomm_ring
  · unfold peircePermutedTwist parityConj
    calc
      steinbergBraid P A C * (invS P * (X * Y) * invS P) * steinbergBraidInv P A C =
        steinbergBraid P A C * (invS P * X * (invS P * invS P) * Y * invS P) *
          steinbergBraidInv P A C := by
        rw [hS2]; noncomm_ring
      _ = steinbergBraid P A C * (invS P * X * invS P) *
          (steinbergBraidInv P A C * steinbergBraid P A C) *
          (invS P * Y * invS P) * steinbergBraidInv P A C := by
        rw [hBrL]; noncomm_ring
      _ = (steinbergBraid P A C * (invS P * X * invS P) * steinbergBraidInv P A C) *
          (steinbergBraid P A C * (invS P * Y * invS P) * steinbergBraidInv P A C) := by
        noncomm_ring
  · simp only [peircePermutedTwist, parityConj, steinbergBraid, steinbergBraidInv]
    peirce_nf hP
  · simp only [peircePermutedTwist, parityConj, steinbergBraid, steinbergBraidInv]
    peirce_nf hP

variable [StarRing B]

/-- **Archetype P₉ (`seedPositivityForm`)**:
Operator-valued positivity test quadratic form `star X * genV P A (star A) * X` associated
to a self-adjoint Peirce seed `(P, A)`. -/
def seedPositivityForm (P A X : B) : B :=
  star X * genV P A (star A) * X

/-- **Lemma P₉.1 (`seedPositivityForm_hermitian_squares_and_twist_transfer`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A, X : B` in
`[Ring B] [StarRing B]`:
1. **Subtraction-Free Sum of Two Non-Commutative Hermitian Squares & Self-Adjointness:**
   `seedPositivityForm P A X = star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) + star (conePlus P A * X) * (conePlus P A * X)`
   and `star (seedPositivityForm P A X) = seedPositivityForm P A X`;
2. **Peirce Corner-Projected Single Hermitian Squares & Twist Transfer:**
   `seedPositivityForm P A (P * X) = star (coneMinus P (star A) * X) * (coneMinus P (star A) * X)`,
   `seedPositivityForm P A ((1 - P) * X) = star (conePlus P A * X) * (conePlus P A * X)`,
   and `seedPositivityForm P A (peircePermutedTwist P A (star A) X)` decomposes identically into
   the sum of two Hermitian squares in `B`;
3. **Proper Star-Ring Kernel Equivalence:**
   Under proper star-ring cancellation (`∀ Z : B, star Z * Z = 0 → Z = 0`),
   `(seedPositivityForm P A (P * X) = 0 ∧ seedPositivityForm P A ((1 - P) * X) = 0) ↔ (coneMinus P (star A) * X = 0 ∧ conePlus P A * X = 0)`;
4. **Horizon Star-Duality of the Bicolored Trip Operators:**
   `star (plabicTripWB P A (star A)) = plabicTripWB P (-A) (-star A)` and
   `plabicTripBW P A (star A) * star (plabicTripWB P A (star A)) = 1` and
   `star (plabicTripWB P A (star A)) * plabicTripBW P A (star A) = 1`. -/
theorem seedPositivityForm_hermitian_squares_and_twist_transfer
    (hProper : ∀ Z : B, star Z * Z = 0 → Z = 0)
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A X : B) :
    seedPositivityForm P A X =
      star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) +
      star (conePlus P A * X) * (conePlus P A * X) ∧
    star (seedPositivityForm P A X) = seedPositivityForm P A X ∧
    seedPositivityForm P A (P * X) =
      star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) ∧
    seedPositivityForm P A ((1 - P) * X) =
      star (conePlus P A * X) * (conePlus P A * X) ∧
    seedPositivityForm P A (peircePermutedTwist P A (star A) X) =
      star (coneMinus P (star A) * peircePermutedTwist P A (star A) X) *
        (coneMinus P (star A) * peircePermutedTwist P A (star A) X) +
      star (conePlus P A * peircePermutedTwist P A (star A) X) *
        (conePlus P A * peircePermutedTwist P A (star A) X) ∧
    ((seedPositivityForm P A (P * X) = 0 ∧ seedPositivityForm P A ((1 - P) * X) = 0) ↔
      (coneMinus P (star A) * X = 0 ∧ conePlus P A * X = 0)) ∧
    star (plabicTripWB P A (star A)) = plabicTripWB P (-A) (-star A) ∧
    plabicTripBW P A (star A) * star (plabicTripWB P A (star A)) = 1 ∧
    star (plabicTripWB P A (star A)) * plabicTripBW P A (star A) = 1 := by
  have hSq : ∀ W : B,
      seedPositivityForm P A W =
        star (coneMinus P (star A) * W) * (coneMinus P (star A) * W) +
        star (conePlus P A * W) * (conePlus P A * W) := by
    intro W
    unfold seedPositivityForm genV anticomm
    rw [star_mul, star_mul, star_conePlus hPsym, star_coneMinus hPsym, star_star]
    noncomm_ring
  have hSym : star (seedPositivityForm P A X) = seedPositivityForm P A X := by
    calc
      star (seedPositivityForm P A X) =
          star (star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) +
            star (conePlus P A * X) * (conePlus P A * X)) := congrArg star (hSq X)
      _ = seedPositivityForm P A X := by
        simp only [star_add, star_mul, star_star]
        calc
          star X * star (coneMinus P (star A)) * (coneMinus P (star A) * X) +
              star X * star (conePlus P A) * (conePlus P A * X) =
            star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) +
              star (conePlus P A * X) * (conePlus P A * X) := by
                simp only [star_mul]
          _ = seedPositivityForm P A X := (hSq X).symm
  have hConeM_PX : coneMinus P (star A) * (P * X) = coneMinus P (star A) * X := by
    simp only [coneMinus]; peirce_nf hP
  have hConeP_PX : conePlus P A * (P * X) = 0 := by
    simp only [conePlus]; peirce_nf hP
  have hSqPX :
      seedPositivityForm P A (P * X) =
        star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) := by
    rw [hSq (P * X), hConeM_PX, hConeP_PX, star_zero, zero_mul, add_zero]
  have hConeM_QX : coneMinus P (star A) * ((1 - P) * X) = 0 := by
    simp only [coneMinus]; peirce_nf hP
  have hConeP_QX : conePlus P A * ((1 - P) * X) = conePlus P A * X := by
    simp only [conePlus]; peirce_nf hP
  have hSqQX :
      seedPositivityForm P A ((1 - P) * X) =
        star (conePlus P A * X) * (conePlus P A * X) := by
    rw [hSq ((1 - P) * X), hConeM_QX, hConeP_QX, star_zero, zero_mul, zero_add]
  have hKer :
      (seedPositivityForm P A (P * X) = 0 ∧ seedPositivityForm P A ((1 - P) * X) = 0) ↔
        (coneMinus P (star A) * X = 0 ∧ conePlus P A * X = 0) := by
    rw [hSqPX, hSqQX]
    exact ⟨fun ⟨h1, h2⟩ => ⟨hProper _ h1, hProper _ h2⟩,
      fun ⟨h1, h2⟩ => ⟨by rw [h1, star_zero, zero_mul], by rw [h2, star_zero, zero_mul]⟩⟩
  have hStarTrip : star (plabicTripWB P A (star A)) = plabicTripWB P (-A) (-star A) := by
    unfold plabicTripWB plabicWhiteShear plabicBlackShear
    rw [star_mul, star_add, star_sub, star_one, star_conePlus hPsym,
      star_coneMinus hPsym, star_star]
    peirce_nf hP
  rcases plabic_bicolored_trip_identities_and_nc_witness hP (-A) (-star A) with
    ⟨_, _, _, _, hInvR, hInvL, _⟩
  simp only [neg_neg] at hInvR hInvL
  refine ⟨hSq X, hSym, hSqPX, hSqQX, hSq (peircePermutedTwist P A (star A) X),
    hKer, hStarTrip, ?_, ?_⟩
  · rw [hStarTrip]
    exact hInvL
  · rw [hStarTrip]
    exact hInvR

/-- **Lemma P₁₀.1 (conditional inverse-factor identities and a sheaf-operator identity)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A, C, Z_inv : B`:
1. **Conditional two-sided inverse-factor identities:**
   If `zetaFactor P A C * Z_inv = 1` and `Z_inv * zetaFactor P A C = 1`, then
   - `plabicFrozenTarget P A C * (plabicFrozenSource P A C * Z_inv) = 1` and
     `(Z_inv * plabicFrozenSource P A C) * plabicFrozenTarget P A C = 1`,
   - `plabicFrozenSource P A C * (plabicFrozenTarget P A C * Z_inv) = 1` and
     `(Z_inv * plabicFrozenTarget P A C) * plabicFrozenSource P A C = 1`;
2. **Horizon identity with the cellular sheaf operator:**
   At the horizon `C = star A`, the product of the two defined corner factors equals
   `1 - sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)`:
   `plabicFrozenTarget P A (star A) * plabicFrozenSource P A (star A) = 1 - sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)`. -/
theorem frozen_factor_invertibility_and_sheaf_bridge
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A C Z_inv : B) :
    (zetaFactor P A C * Z_inv = 1 → Z_inv * zetaFactor P A C = 1 →
      plabicFrozenTarget P A C * (plabicFrozenSource P A C * Z_inv) = 1 ∧
      (Z_inv * plabicFrozenSource P A C) * plabicFrozenTarget P A C = 1 ∧
      plabicFrozenSource P A C * (plabicFrozenTarget P A C * Z_inv) = 1 ∧
      (Z_inv * plabicFrozenTarget P A C) * plabicFrozenSource P A C = 1) ∧
    plabicFrozenTarget P A (star A) * plabicFrozenSource P A (star A) =
      1 - sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A) := by
  rcases plabic_target_source_seed_duality hP A C with ⟨_, _, hProdTS, hProdST, _⟩
  refine ⟨fun hZR hZL => ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← mul_assoc, hProdTS, hZR]
    · rw [mul_assoc, hProdST, hZL]
    · rw [← mul_assoc, hProdST, hZR]
    · rw [mul_assoc, hProdTS, hZL]
  · rcases plabic_target_source_seed_duality hP A (star A) with ⟨_, _, hTS_star, _, _⟩
    rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨_, _, hLapV⟩
    rw [hTS_star, hLapV]
    rfl

/-! ### 4. Pre-Existing Codebase Deduplication & Connection Bridges -/

omit [StarRing B] in
/-- **Pre-Existing Codebase Bridge 1 (`plabic_frozen_and_trip_spine_bridge`)**:
Connects `plabicFrozenTarget`, `plabicFrozenSource`, `plabicTripWB`, and `plabicTripBW`
directly to the pre-existing `PeirceSpine` owners `bergmanOp` (`Bergman.lean`),
`chartBruhatConj` (`TwoStateSandwich.lean`), `chiralEuler_factorizations`
(`ChiralEulerFactors.lean`), and `parityConj_steinbergBraidDual_and_bruhat_factors`
(`PhaseConjugateSteinberg.lean`). -/
theorem plabic_frozen_and_trip_spine_bridge
    {P : B} (hP : P * P = P) (A C X : B) :
    bergmanOp P A C X = plabicFrozenTarget P A C * X * plabicFrozenSource P A C ∧
    chartBruhatConj P A C X = plabicTripWB P A C * X * plabicTripBW P (-A) (-C) ∧
    plabicFrozenTarget P A C = (1 - genV P A C) + (1 - P) * qgtMinus P A C * (1 - P) ∧
    plabicFrozenSource P A C = (1 - genV P A C) + P * qgtPlus P A C * P ∧
    parityConj P (steinbergBraidDual P A C) =
      plabicBlackShear P (-C) * plabicWhiteShear P (-A) * plabicBlackShear P (-C) := by
  rcases parityConj_steinbergBraidDual_and_bruhat_factors hP A C with ⟨hDual, _, _⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · unfold chartBruhatConj plabicTripWB plabicTripBW plabicWhiteShear plabicBlackShear
    simp only [conePlus_neg, coneMinus_neg]
    noncomm_ring
  · simp only [plabicFrozenTarget, qgtPlus, qgtMinus]
    peirce_nf hP
  · simp only [plabicFrozenSource, qgtPlus, qgtMinus]
    peirce_nf hP
  · rw [hDual]
    unfold steinbergBraidDualInv plabicBlackShear plabicWhiteShear
    simp only [conePlus_neg, coneMinus_neg]
    noncomm_ring

omit [StarRing B] in
/-- **Pre-Existing Codebase Bridge 2 (`peircePermutedTwist_bridge_to_steinberg`)**:
Connects `peircePermutedTwist` directly to `parityConj` (`Basic.lean`),
`parityConj_steinberg_round_trip` (`PhaseConjugateSteinberg.lean`), and
`steinbergBraid_conj` (`Unipotent.lean`). -/
theorem peircePermutedTwist_bridge_to_steinberg
    {P : B} (hP : P * P = P) (A C X : B) :
    peircePermutedTwist P A C X =
      steinbergBraid P A C * parityConj P X * steinbergBraidInv P A C ∧
    peircePermutedTwist P A C X =
      conjPlus P A (conjMinusInv P C (conjPlus P A (parityConj P X))) ∧
    parityConj P (steinbergBraidInv P A C * peircePermutedTwist P A C X * steinbergBraid P A C) =
      X ∧
    parityConj P
      (peircePermutedTwist P A C (steinbergBraid P A C * X * steinbergBraidInv P A C)) = X := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa only [peircePermutedTwist] using steinbergBraid_conj A C (parityConj P X)
  · exact (peircePermutedTwist_automorphism_and_seed_transport hP A C X X).2.1
  · exact parityConj_steinberg_round_trip hP A C X

/-- **Pre-Existing Codebase Bridge 3 (`seedPositivityForm_bridge_to_sheafDirichlet_and_bergman`)**:
Connects `seedPositivityForm` directly to `sheafDirichletForm`
(`CellularSheafOperatorPoset.lean`), `zetaFactor`, and `bergmanOp` (`Bergman.lean`). -/
theorem seedPositivityForm_bridge_to_sheafDirichlet_and_bergman
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A X : B) :
    seedPositivityForm P A X =
      sheafDirichletForm P (coneMinus P (star A)) (conePlus P A) X ∧
    seedPositivityForm P A X + star X * zetaFactor P A (star A) * X = star X * X ∧
    star X * bergmanOp P A (star A) 1 * X = star X * X - seedPositivityForm P A X := by
  rcases sheaf_to_tetraktys_bridge hP hPsym A (star A) with ⟨_, _, hLapV⟩
  have hDir :
      seedPositivityForm P A X =
        sheafDirichletForm P (coneMinus P (star A)) (conePlus P A) X := by
    unfold seedPositivityForm sheafDirichletForm
    rw [hLapV]
  refine ⟨hDir, ?_, ?_⟩
  · unfold seedPositivityForm zetaFactor
    noncomm_ring
  · rw [(archetype_A23_bergman_operator hP A (star A)).1]
    unfold seedPositivityForm
    noncomm_ring

/-! ### 5. Master Theorem D₂₀: Complete Synthesis of Archetypes `P₁ → P₁₀` -/

/-- **Stage D₂₀ (`stage_D20_positroid_cluster_twist_master_synthesis`)**:
Packages the ten displayed Peirce-operator identities (`P₁ → P₁₀`): chart idempotency,
corner expressions, an operator exchange identity, bridge products, conjugation covariance,
conditional inverse-factor identities, and pure star-ring positivity-form Hermitian square
and proper-kernel consequences in `[Ring B] [StarRing B]`. The labels are organizational;
this theorem does not define classical Grassmannian or positroid carriers. -/
theorem stage_D20_positroid_cluster_twist_master_synthesis
    (hProper : ∀ Z : B, star Z * Z = 0 → Z = 0)
    {P U U_inv : B} (hP : P * P = P) (hPsym : star P = P)
    (hLeft : U_inv * U = 1) (hRight : U * U_inv = 1)
    (A C X X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : B) :
    -- P₁: Operator chart idempotency and two corner expressions
    (opSchubertChart P A C * opSchubertChart P A C = opSchubertChart P A C ∧
     opQuasiPlucker11 P A C = P + qgtPlus P A C ∧
     opQuasiPlucker00 P A C = -qgtMinus P A C) ∧
    -- P₂: A non-commutative three-term operator exchange identity
    (opPluckerBivector P X₁ X₃ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄ =
      opPluckerBivector P X₁ X₂ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄ +
      opPluckerBivector P X₂ X₃ Y₁ Y₂ * opPluckerBivector P X₃ X₄ Y₃ Y₄) ∧
    -- P₃: Bicolored plabic trip commutator & horizon star-duality
    (comm (plabicWhiteShear P A) (plabicBlackShear P C) = -genSig P A C ∧
     plabicTripBW P A (star A) * star (plabicTripWB P A (star A)) = 1 ∧
     star (plabicTripWB P A (star A)) * plabicTripBW P A (star A) = 1) ∧
    -- P₄ & P₁₀: Target-source frozen duality & cellular sheaf Laplacian bridge
    (plabicFrozenTarget P A C - plabicFrozenSource P A C = -genSig P A C ∧
     plabicFrozenTarget P A C * plabicFrozenSource P A C = zetaFactor P A C ∧
     plabicFrozenTarget P A (star A) * plabicFrozenSource P A (star A) =
       1 - sheafLaplacian0 P (coneMinus P (star A)) (conePlus P A)) ∧
    -- P₅: Non-commutative cluster mutation exchange into orthogonal corner summands
    ((1 - genPhi P A C) * (1 + genPhi P A C) =
      (P - qgtPlus P A C) + ((1 - P) - qgtMinus P A C) ∧
     (P - qgtPlus P A C) * ((1 - P) - qgtMinus P A C) = 0 ∧
     weylJ P A C * weylJInv P A C = 1 + idempotencyDefect (genV P A C)) ∧
    -- P₆: Boundary-relabeled plabic conjugation covariance
    (plabicTripWB (relabeledConj U U_inv P) (relabeledConj U U_inv A) (relabeledConj U U_inv C) =
      relabeledConj U U_inv (plabicTripWB P A C)) ∧
    -- P₇: Quasi-coincidence of target and source Steinberg braids up to frozen corner operators
    (steinbergBraid P A C - steinbergBraidDual P A C =
      plabicFrozenTarget P A C * conePlus P A + plabicFrozenSource P A C * coneMinus P C) ∧
    -- P₈ & P₉: Permuted twist bijection, V-invariance, and pure operator Hermitian-square/kernel laws
    (peircePermutedTwist P A C (peircePermutedTwistInv P A C X) = X ∧
     peircePermutedTwist P A C (genV P A C) = genV P A C ∧
     peircePermutedTwist P A C (steinbergBraid P A C) = steinbergBraidInv P A C ∧
     seedPositivityForm P A X =
       star (coneMinus P (star A) * X) * (coneMinus P (star A) * X) +
       star (conePlus P A * X) * (conePlus P A * X) ∧
     ((seedPositivityForm P A (P * X) = 0 ∧ seedPositivityForm P A ((1 - P) * X) = 0) ↔
       (coneMinus P (star A) * X = 0 ∧ conePlus P A * X = 0))) := by
  rcases opSchubertChart_idempotent_and_quasiPlucker_minors hP A C with
    ⟨hP1_idem, hP1_11, hP1_00, _, _⟩
  rcases nc_three_term_plucker_exchange hP X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ with
    ⟨_, hP2_exch, _, _⟩
  rcases plabic_bicolored_trip_identities_and_nc_witness hP A C with
    ⟨_, _, hP3_comm, _, _, _, _⟩
  rcases plabic_target_source_seed_duality hP A C with
    ⟨hP4_diff, _, hP4_prod, _, _⟩
  rcases nc_cluster_mutation_exchange hP A C with
    ⟨hP5_phi, hP5_orth, _, _, hP5_weyl⟩
  rcases relabeled_plabic_conjugation_covariance hP hLeft hRight A C X X with
    ⟨_, _, _, _, hP6_trip, _⟩
  rcases quasi_coincidence_up_to_frozen_units hP A C with
    ⟨_, _, _, _, hP7_diff⟩
  rcases peircePermutedTwist_automorphism_and_seed_transport hP A C X X with
    ⟨hP8_inv, _, _, hP8_V, hP8_braid⟩
  rcases seedPositivityForm_hermitian_squares_and_twist_transfer hProper hP hPsym A X with
    ⟨hP9_sq, _, _, _, _, hP9_ker, _, hP9_unit1, hP9_unit2⟩
  rcases frozen_factor_invertibility_and_sheaf_bridge hP hPsym A C 1 with
    ⟨_, hP10_sheaf⟩
  exact ⟨⟨hP1_idem, hP1_11, hP1_00⟩,
         hP2_exch,
         ⟨hP3_comm, hP9_unit1, hP9_unit2⟩,
         ⟨hP4_diff, hP4_prod, hP10_sheaf⟩,
         ⟨hP5_phi, hP5_orth, hP5_weyl⟩,
         hP6_trip,
         hP7_diff,
         ⟨hP8_inv, hP8_V, hP8_braid, hP9_sq, hP9_ker⟩⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
