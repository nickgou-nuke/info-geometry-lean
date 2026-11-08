/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Unipotent
import InfoGeometry.OperatorAlgebra.PeirceSpine.PhaseConjugateSteinberg
import InfoGeometry.OperatorAlgebra.PeirceSpine.ChiralEulerFactors
import InfoGeometry.OperatorAlgebra.PeirceSpine.CyclotomicBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.TwoStateSandwich
import InfoGeometry.OperatorAlgebra.PeirceSpine.CellularSheafOperatorPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading
import InfoGeometry.OperatorAlgebra.PeirceSpine.ConeSheetBraiding
import InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge
import InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge
import InfoGeometry.Algebra.FibonacciParafermion
import InfoGeometry.Algebra.FibonacciGrothendieckRing
import InfoGeometry.Canonical.FiniteFibonacciFusionMatrix
import InfoGeometry.Canonical.SplitComplex
import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Projective.SplitQuaternionMatrix

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

instance positroidClusterStageLinearOrder : LinearOrder PositroidClusterStage :=
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

/-! ### 6. Stage D₂₃ (`V₁ → V₅`): Non-Commutative Symbol Alphabet, Plabic Boundary Constraint
`P_plabic * Z_sol = 0`, and Operator Square-Root Letters `√(1 ± 4V)`

Deduplicated against `peirceTransfer`, `peirceTransferJ` (`TransferDefect.lean`),
`idempotencyDefect`, `idempotencyDefectBar` (`IdempotentGraphGrassmannian.lean`),
`chartBruhatConj` (`TwoStateSandwich.lean`), and `archetype_A58_operator_cyclotomic_roots_and_discriminants`
(`CyclotomicBridge.lean`). -/

omit [StarRing B] in
/-- **Archetype V₂ (`plabicBoundaryOp`)**:
The two-sided plabic-trip-conjugated boundary operator
`P_plabic = plabicTripWB P A C * P * plabicTripBW P (-A) (-C) = chartBruhatConj P A C P`. -/
def plabicBoundaryOp (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C) * P * (1 + coneMinus P C) * (1 - conePlus P A)

omit [StarRing B] in
/-- **Archetype V₂ (`plabicTwistorSol`)**:
The complementary boundary-annihilated operator solution
`Z_sol(Z) = plabicTripWB P A C * (1 - P) * plabicTripBW P (-A) (-C) * Z = chartBruhatConj P A C (1 - P) * Z`. -/
def plabicTwistorSol (P A C Z : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C) * (1 - P) * (1 + coneMinus P C) * (1 - conePlus P A) * Z

omit [StarRing B] in
/-- **Archetype V₃ (`radicalLetterPlus`)**:
The non-commutative operator square-root letter `R₊ = 2 • peirceTransfer P A C - 1 = S + 2 • Φ`
whose square in `B` is `1 + 4 • V`. -/
def radicalLetterPlus (P A C : B) : B :=
  (2 : ℤ) • peirceTransfer P A C - 1

omit [StarRing B] in
/-- **Archetype V₃ (`radicalLetterMinus`)**:
The complementary operator square-root letter `R₋ = 2 • peirceTransferJ P A C - 1 = S + 2 • J`
whose square in `B` is `1 - 4 • V`. -/
def radicalLetterMinus (P A C : B) : B :=
  (2 : ℤ) • peirceTransferJ P A C - 1

omit [StarRing B] in
/-- **Lemma V₁.1 (`goncharov_duplication_and_defect_alphabet`)**:
For any `X : B` and any idempotent `P` (`P * P = P`):
1. **Binomial / Duplication Factorization:** `(1 - X) * (1 + X) = 1 - X * X` and
   `(1 + X) * (1 - X) = 1 - X * X`;
2. **Polylogarithmic Defect Duplication:**
   `idempotencyDefect (X * X) = idempotencyDefect X * idempotencyDefectBar X` and
   `(X + 1) * idempotencyDefect X = X * X * X - X`;
3. **Peirce-Tetraktys Alphabet Duplication & Defect Alphabet Factorization:**
   `(1 - genPhi P A C) * (1 + genPhi P A C) = 1 - genV P A C`,
   `(1 - genJ P A C) * (1 + genJ P A C) = 1 + genV P A C`,
   `idempotencyDefectBar (genPhi P A C) * idempotencyDefect (genPhi P A C) = idempotencyDefect (genV P A C)`,
   and `idempotencyDefectBar (genJ P A C) * idempotencyDefect (genJ P A C) = idempotencyDefectBar (genV P A C)`;
4. **Iterated Defect on Peirce Transfer Elements (`peirceTransfer`, `peirceTransferJ`):**
   `idempotencyDefect (peirceTransfer P A C) = genV P A C`,
   `idempotencyDefect (peirceTransferJ P A C) = -genV P A C`,
   `idempotencyDefect (idempotencyDefect (peirceTransfer P A C)) = idempotencyDefect (genV P A C)`,
   and `idempotencyDefect (idempotencyDefect (peirceTransferJ P A C)) = idempotencyDefectBar (genV P A C)`. -/
theorem goncharov_duplication_and_defect_alphabet
    {P : B} (hP : P * P = P) (A C X : B) :
    (1 - X) * (1 + X) = 1 - X * X ∧
    (1 + X) * (1 - X) = 1 - X * X ∧
    idempotencyDefect (X * X) = idempotencyDefect X * idempotencyDefectBar X ∧
    (X + 1) * idempotencyDefect X = X * X * X - X ∧
    (1 - genPhi P A C) * (1 + genPhi P A C) = 1 - genV P A C ∧
    (1 - genJ P A C) * (1 + genJ P A C) = 1 + genV P A C ∧
    idempotencyDefectBar (genPhi P A C) * idempotencyDefect (genPhi P A C) =
      idempotencyDefect (genV P A C) ∧
    idempotencyDefectBar (genJ P A C) * idempotencyDefect (genJ P A C) =
      idempotencyDefectBar (genV P A C) ∧
    idempotencyDefect (peirceTransfer P A C) = genV P A C ∧
    idempotencyDefect (peirceTransferJ P A C) = -genV P A C ∧
    idempotencyDefect (idempotencyDefect (peirceTransfer P A C)) =
      idempotencyDefect (genV P A C) ∧
    idempotencyDefect (idempotencyDefect (peirceTransferJ P A C)) =
      idempotencyDefectBar (genV P A C) := by
  rcases transfer_second_defect_iterates hP A C with ⟨hDef2Phi, hDef2J⟩
  refine ⟨by noncomm_ring, by noncomm_ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDef2Phi, hDef2J⟩
  · unfold idempotencyDefect idempotencyDefectBar; noncomm_ring
  · unfold idempotencyDefect; noncomm_ring
  · peirce_nf hP
  · peirce_nf hP
  · unfold idempotencyDefect idempotencyDefectBar; peirce_nf hP
  · unfold idempotencyDefect idempotencyDefectBar; peirce_nf hP
  · unfold idempotencyDefect peirceTransfer; peirce_nf hP
  · unfold idempotencyDefect peirceTransferJ; peirce_nf hP

omit [StarRing B] in
/-- **Lemma V₂.1 (`plabic_boundary_constraint_and_twistor_solution`)**:
For any idempotent `P` (`P * P = P`) and any `A, C, Z : B`:
1. **Deduplication with `chartBruhatConj` (`TwoStateSandwich.lean`):**
   `plabicBoundaryOp P A C = chartBruhatConj P A C P` and
   `plabicTwistorSol P A C Z = chartBruhatConj P A C (1 - P) * Z`;
2. **Idempotency of `P_plabic`:** `plabicBoundaryOp P A C * plabicBoundaryOp P A C = plabicBoundaryOp P A C`;
3. **Explicit Tetraktys Expansion of `P_plabic`:**
   `plabicBoundaryOp P A C = P - genPhi P A C - genSig P A C + genV P A C * conePlus P A`;
4. **Universal Plabic Boundary Constraint `P_plabic * Z_sol(Z) = 0`:**
   For every operator `Z : B`, `plabicBoundaryOp P A C * plabicTwistorSol P A C Z = 0`;
5. **Complementary Reproduction & Partition of Unity:**
   `(1 - plabicBoundaryOp P A C) * plabicTwistorSol P A C Z = plabicTwistorSol P A C Z` and
   `plabicBoundaryOp P A C * Z + plabicTwistorSol P A C Z = Z`. -/
theorem plabic_boundary_constraint_and_twistor_solution
    {P : B} (hP : P * P = P) (A C Z : B) :
    plabicBoundaryOp P A C = chartBruhatConj P A C P ∧
    plabicTwistorSol P A C Z = chartBruhatConj P A C (1 - P) * Z ∧
    plabicBoundaryOp P A C * plabicBoundaryOp P A C = plabicBoundaryOp P A C ∧
    plabicBoundaryOp P A C = P - genPhi P A C - genSig P A C + genV P A C * conePlus P A ∧
    plabicBoundaryOp P A C * plabicTwistorSol P A C Z = 0 ∧
    (1 - plabicBoundaryOp P A C) * plabicTwistorSol P A C Z = plabicTwistorSol P A C Z ∧
    plabicBoundaryOp P A C * Z + plabicTwistorSol P A C Z = Z := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold plabicBoundaryOp chartBruhatConj; noncomm_ring
  · unfold plabicTwistorSol chartBruhatConj; noncomm_ring
  · unfold plabicBoundaryOp; peirce_nf hP
  · unfold plabicBoundaryOp; peirce_nf hP
  · unfold plabicBoundaryOp plabicTwistorSol; peirce_nf hP
  · unfold plabicBoundaryOp plabicTwistorSol; peirce_nf hP
  · unfold plabicBoundaryOp plabicTwistorSol; peirce_nf hP

omit [StarRing B] in
/-- **Lemma V₃.1 (`operator_square_root_symbol_letters`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Grading Decomposition:**
   `radicalLetterPlus P A C = invS P + (2 : ℤ) • genPhi P A C` and
   `radicalLetterMinus P A C = invS P + (2 : ℤ) • genJ P A C`;
2. **Exact Operator Square-Root Realization of `1 ± 4 • V`:**
   `radicalLetterPlus P A C * radicalLetterPlus P A C = 1 + (4 : ℤ) • genV P A C` and
   `radicalLetterMinus P A C * radicalLetterMinus P A C = 1 - (4 : ℤ) • genV P A C`;
3. **Difference, Sum, Quadratic Equations & 5-Step `A₂` Fibonacci–Lyness Recurrence:**
   `radicalLetterPlus P A C - radicalLetterMinus P A C = (2 : ℤ) • (genPhi P A C - genJ P A C)`,
   `radicalLetterPlus P A C + radicalLetterMinus P A C = (2 : ℤ) • (invS P + genPhi P A C + genJ P A C)`,
   `peirceTransfer P A C * peirceTransfer P A C - peirceTransfer P A C - genV P A C = 0`,
   `peirceTransferJ P A C * peirceTransferJ P A C - peirceTransferJ P A C + genV P A C = 0`,
   `(peirceTransfer P A C) ^ 3 = (1 + genV P A C) * peirceTransfer P A C + genV P A C`, and
   `(peirceTransfer P A C) ^ 5 = (1 + (3 : ℤ) • genV P A C + genV P A C * genV P A C) * peirceTransfer P A C + genV P A C * (1 + (2 : ℤ) • genV P A C)`. -/
theorem operator_square_root_symbol_letters
    {P : B} (hP : P * P = P) (A C : B) :
    radicalLetterPlus P A C = invS P + (2 : ℤ) • genPhi P A C ∧
    radicalLetterMinus P A C = invS P + (2 : ℤ) • genJ P A C ∧
    radicalLetterPlus P A C * radicalLetterPlus P A C = 1 + (4 : ℤ) • genV P A C ∧
    radicalLetterMinus P A C * radicalLetterMinus P A C = 1 - (4 : ℤ) • genV P A C ∧
    radicalLetterPlus P A C - radicalLetterMinus P A C =
      (2 : ℤ) • (genPhi P A C - genJ P A C) ∧
    radicalLetterPlus P A C + radicalLetterMinus P A C =
      (2 : ℤ) • (invS P + genPhi P A C + genJ P A C) ∧
    peirceTransfer P A C * peirceTransfer P A C - peirceTransfer P A C - genV P A C = 0 ∧
    peirceTransferJ P A C * peirceTransferJ P A C - peirceTransferJ P A C + genV P A C = 0 ∧
    (peirceTransfer P A C) ^ 3 =
      (1 + genV P A C) * peirceTransfer P A C + genV P A C ∧
    (peirceTransfer P A C) ^ 5 =
      (1 + (3 : ℤ) • genV P A C + genV P A C * genV P A C) * peirceTransfer P A C +
        genV P A C * (1 + (2 : ℤ) • genV P A C) := by
  rcases archetype_A58_operator_cyclotomic_roots_and_discriminants hP A C with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hSqPlus, hSqMinus⟩
  refine ⟨?_, ?_, hSqPlus, hSqMinus, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [radicalLetterPlus, radicalLetterMinus, peirceTransfer, peirceTransferJ,
      pow_succ, pow_zero, one_mul];
     peirce_nf hP)

omit [StarRing B] in
/-- **Lemma V₄.1 (`radical_letter_rationalization_and_adjacency`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Rationalization of `1 ± R₊` and `1 ± R₋`:**
   `(1 - radicalLetterPlus P A C) * (1 + radicalLetterPlus P A C) = -((4 : ℤ) • genV P A C)`,
   `(1 + radicalLetterPlus P A C) * (1 - radicalLetterPlus P A C) = -((4 : ℤ) • genV P A C)`,
   `(1 - radicalLetterMinus P A C) * (1 + radicalLetterMinus P A C) = (4 : ℤ) • genV P A C`, and
   `(1 + radicalLetterMinus P A C) * (1 - radicalLetterMinus P A C) = (4 : ℤ) • genV P A C`;
2. **Non-Commutative Radical Commutator and Anticommutator (`{R₊, R₋} = 2`):**
   `comm (radicalLetterPlus P A C) (radicalLetterMinus P A C) =
     (4 : ℤ) • (genPhi P A C - genJ P A C - (2 : ℤ) • genSig P A C)` and
   `anticomm (radicalLetterPlus P A C) (radicalLetterMinus P A C) =
     (2 : ℤ) • (1 : B)`;
3. **Exact Centrality with the Scale Sector `V`:**
   `comm (radicalLetterPlus P A C) (genV P A C) = 0` and
   `comm (radicalLetterMinus P A C) (genV P A C) = 0`. -/
theorem radical_letter_rationalization_and_adjacency
    {P : B} (hP : P * P = P) (A C : B) :
    (1 - radicalLetterPlus P A C) * (1 + radicalLetterPlus P A C) =
      -((4 : ℤ) • genV P A C) ∧
    (1 + radicalLetterPlus P A C) * (1 - radicalLetterPlus P A C) =
      -((4 : ℤ) • genV P A C) ∧
    (1 - radicalLetterMinus P A C) * (1 + radicalLetterMinus P A C) =
      (4 : ℤ) • genV P A C ∧
    (1 + radicalLetterMinus P A C) * (1 - radicalLetterMinus P A C) =
      (4 : ℤ) • genV P A C ∧
    comm (radicalLetterPlus P A C) (radicalLetterMinus P A C) =
      (4 : ℤ) • (genPhi P A C - genJ P A C - (2 : ℤ) • genSig P A C) ∧
    anticomm (radicalLetterPlus P A C) (radicalLetterMinus P A C) =
      (2 : ℤ) • (1 : B) ∧
    comm (radicalLetterPlus P A C) (genV P A C) = 0 ∧
    comm (radicalLetterMinus P A C) (genV P A C) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [radicalLetterPlus, radicalLetterMinus, peirceTransfer, peirceTransferJ];
     peirce_nf hP)

/-- **Lemma V₅.1 (`radical_biquadratic_and_star_reality`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A, C : B`:
1. **Biquadratic Product `(1 + 4V)(1 - 4V) = 1 - 16V²`:**
   `(radicalLetterPlus P A C * radicalLetterPlus P A C) *
     (radicalLetterMinus P A C * radicalLetterMinus P A C) =
     1 - (16 : ℤ) • (genV P A C * genV P A C)` and
   `(radicalLetterMinus P A C * radicalLetterMinus P A C) *
     (radicalLetterPlus P A C * radicalLetterPlus P A C) =
     1 - (16 : ℤ) • (genV P A C * genV P A C)`;
2. **Horizon Star-Reality of `R₊`, `R₋`, and `R₋²` at `C = star A`:**
   `star (radicalLetterPlus P A (star A)) = radicalLetterPlus P A (star A)`,
   `star (radicalLetterMinus P A (star A)) = invS P - (2 : ℤ) • genJ P A (star A)`, and
   `star (radicalLetterMinus P A (star A) * radicalLetterMinus P A (star A)) =
     radicalLetterMinus P A (star A) * radicalLetterMinus P A (star A)`. -/
theorem radical_biquadratic_and_star_reality
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A C : B) :
    (radicalLetterPlus P A C * radicalLetterPlus P A C) *
      (radicalLetterMinus P A C * radicalLetterMinus P A C) =
      1 - (16 : ℤ) • (genV P A C * genV P A C) ∧
    (radicalLetterMinus P A C * radicalLetterMinus P A C) *
      (radicalLetterPlus P A C * radicalLetterPlus P A C) =
      1 - (16 : ℤ) • (genV P A C * genV P A C) ∧
    star (radicalLetterPlus P A (star A)) = radicalLetterPlus P A (star A) ∧
    star (radicalLetterMinus P A (star A)) = invS P - (2 : ℤ) • genJ P A (star A) ∧
    star (radicalLetterMinus P A (star A) * radicalLetterMinus P A (star A)) =
      radicalLetterMinus P A (star A) * radicalLetterMinus P A (star A) := by
  rcases operator_square_root_symbol_letters hP A C with ⟨_, _, hSqP, hSqM, _, _, _, _, _, _⟩
  rcases operator_square_root_symbol_letters hP A (star A) with
    ⟨hPlusStar, hMinusStar, _, hSqMStar, _, _, _, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hSqP, hSqM]; noncomm_ring
  · rw [hSqM, hSqP]; noncomm_ring
  · rw [hPlusStar, star_add, star_zsmul,
        star_invS hPsym, star_genPhi hPsym A]
  · rw [hMinusStar, star_add, star_zsmul,
        star_invS hPsym, star_genJ hPsym A, zsmul_neg, ← sub_eq_add_neg]
  · rw [hSqMStar, star_sub, star_one, star_zsmul,
        star_genV hPsym A]

/-- **Stage D₂₃ Master Synthesis (`stage_D23_symbol_alphabet_plabic_constraint_and_square_root_letters_master_synthesis`)**:
Unifies the five archetypes `V₁ → V₅` of Stage `D₂₃` over `[Ring B] [StarRing B]`:
1. `V₁`: Goncharov duplication and iterated defect alphabet (`(1 - Φ)(1 + Φ) = 1 - V`,
   `idempotencyDefectBar (genPhi P A C) * idempotencyDefect (genPhi P A C) = idempotencyDefect (genV P A C)`,
   `idempotencyDefect (X * X) = idempotencyDefect X * idempotencyDefectBar X`,
   `idempotencyDefect (peirceTransfer P A C) = genV P A C`);
2. `V₂`: Plabic boundary operator `plabicBoundaryOp = chartBruhatConj P A C P`, its idempotency,
   and universal annihilation of `plabicTwistorSol P A C Z`;
3. `V₃`: Operator square-root letters `radicalLetterPlus² = 1 + 4 • V` and `radicalLetterMinus² = 1 - 4 • V`,
   plus the 5-step `A₂` cluster Fibonacci–Lyness recurrence;
4. `V₄`: Rationalization `(1 ± R_±)(1 ∓ R_±) = ∓ 4 • V`, Jordan cluster adjacency `{R₊, R₋} = 2`,
   and centrality with `genV P A C`;
5. `V₅`: Biquadratic identity `R₊² * R₋² = 1 - 16 • V²` and horizon star-reality. -/
theorem stage_D23_symbol_alphabet_plabic_constraint_and_square_root_letters_master_synthesis
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A C X Z : B) :
    -- V₁: Goncharov duplication & iterated defect alphabet
    ((1 - genPhi P A C) * (1 + genPhi P A C) = 1 - genV P A C ∧
     idempotencyDefectBar (genPhi P A C) * idempotencyDefect (genPhi P A C) =
       idempotencyDefect (genV P A C) ∧
     idempotencyDefect (X * X) = idempotencyDefect X * idempotencyDefectBar X ∧
     idempotencyDefect (peirceTransfer P A C) = genV P A C ∧
     idempotencyDefect (peirceTransferJ P A C) = -genV P A C ∧
     idempotencyDefect (idempotencyDefect (peirceTransfer P A C)) =
       idempotencyDefect (genV P A C)) ∧
    -- V₂: Plabic boundary idempotency & universal annihilation P_plabic * Z_sol(Z) = 0
    (plabicBoundaryOp P A C = chartBruhatConj P A C P ∧
     plabicBoundaryOp P A C * plabicBoundaryOp P A C = plabicBoundaryOp P A C ∧
     plabicBoundaryOp P A C * plabicTwistorSol P A C Z = 0 ∧
     plabicBoundaryOp P A C * Z + plabicTwistorSol P A C Z = Z) ∧
    -- V₃ & V₄: Operator square-root letters R_±² = 1 ± 4V, 5-step recurrence, rationalization, {R₊, R₋} = 2, and V-centrality
    (radicalLetterPlus P A C * radicalLetterPlus P A C = 1 + (4 : ℤ) • genV P A C ∧
     radicalLetterMinus P A C * radicalLetterMinus P A C = 1 - (4 : ℤ) • genV P A C ∧
     (peirceTransfer P A C) ^ 5 =
       (1 + (3 : ℤ) • genV P A C + genV P A C * genV P A C) * peirceTransfer P A C +
         genV P A C * (1 + (2 : ℤ) • genV P A C) ∧
     (1 - radicalLetterPlus P A C) * (1 + radicalLetterPlus P A C) = -((4 : ℤ) • genV P A C) ∧
     (1 + radicalLetterPlus P A C) * (1 - radicalLetterPlus P A C) = -((4 : ℤ) • genV P A C) ∧
     (1 - radicalLetterMinus P A C) * (1 + radicalLetterMinus P A C) = (4 : ℤ) • genV P A C ∧
     anticomm (radicalLetterPlus P A C) (radicalLetterMinus P A C) = (2 : ℤ) • (1 : B) ∧
     comm (radicalLetterPlus P A C) (genV P A C) = 0 ∧
     comm (radicalLetterMinus P A C) (genV P A C) = 0) ∧
    -- V₅: Biquadratic product & horizon star-reality
    ((radicalLetterPlus P A C * radicalLetterPlus P A C) *
       (radicalLetterMinus P A C * radicalLetterMinus P A C) =
       1 - (16 : ℤ) • (genV P A C * genV P A C) ∧
     star (radicalLetterPlus P A (star A)) = radicalLetterPlus P A (star A) ∧
     star (radicalLetterMinus P A (star A)) = invS P - (2 : ℤ) • genJ P A (star A)) := by
  rcases goncharov_duplication_and_defect_alphabet hP A C X with
    ⟨_, _, hV1_dup, _, hV1_lin, _, hV1_bar, _, hV1_phi, hV1_j, hV1_iter, _⟩
  rcases plabic_boundary_constraint_and_twistor_solution hP A C Z with
    ⟨hV2_bruhat, _, hV2_idem, _, hV2_zero, _, hV2_part⟩
  rcases operator_square_root_symbol_letters hP A C with
    ⟨_, _, hV3_plus, hV3_minus, _, _, _, _, _, hV3_pow5⟩
  rcases radical_letter_rationalization_and_adjacency hP A C with
    ⟨hV4_ratP1, hV4_ratP2, hV4_ratM, _, _, hV4_anti, hV4_commP, hV4_commM⟩
  rcases radical_biquadratic_and_star_reality hP hPsym A C with
    ⟨hV5_biq, _, hV5_starR, hV5_starRM, _⟩
  exact ⟨⟨hV1_lin, hV1_bar, hV1_dup, hV1_phi, hV1_j, hV1_iter⟩,
         ⟨hV2_bruhat, hV2_idem, hV2_zero, hV2_part⟩,
         ⟨hV3_plus, hV3_minus, hV3_pow5, hV4_ratP1, hV4_ratP2, hV4_ratM, hV4_anti, hV4_commP, hV4_commM⟩,
         ⟨hV5_biq, hV5_starR, hV5_starRM⟩⟩

/-! ### 7. Stage M₁₁ & Stage D₂₄ (`W₁ → W₅`): Bipartite Plabic Incidence `C · Z = 0`,
Square-Move Mutation, Multiplicative Symbol Kernel Duplication, 5-Step `A₂` Pentagon
Trace Invariants, and Universal Four-Mass Quadratic Discriminant Law

Deduplicated against `chartMinus`, `chartPlus`, `chartBruhatConj` (`TwoStateSandwich.lean`),
`peirceTransfer`, `peirceTransferComplement` (`TransferDefect.lean`), and
`idempotencyDefect`, `idempotencyDefectBar` (`IdempotentGraphGrassmannian.lean`). -/

omit [StarRing B] in
/-- **Stage M₁₁ (`twistorNullZ`)**:
Momentum-twistor right null-space operator `(1 + conePlus P A) * (1 - P) * X` annihilated on the
left by the bipartite plabic boundary chart `chartMinus P A = P - conePlus P A`. -/
def twistorNullZ (P A X : B) : B :=
  (1 + conePlus P A) * (1 - P) * X

omit [StarRing B] in
/-- **Stage M₁₁ (`twistorNullZDual`)**:
Dual momentum-twistor left null-space operator `X * (1 - P) * (1 - coneMinus P C)` annihilated on
the right by the dual bipartite plabic boundary chart `chartPlus P C = P + coneMinus P C`. -/
def twistorNullZDual (P C X : B) : B :=
  X * (1 - P) * (1 - coneMinus P C)

omit [StarRing B] in
/-- **Stage M₁₁ (`clusterNum3`, `clusterNum4`, `clusterNum5`)**:
Cleared-denominator non-commutative `A₂` pentagon numerators `1 + A₂`, `1 + A₁ + A₂`, and `1 + A₁`. -/
def clusterNum3 (A₂ : B) : B := 1 + A₂

omit [StarRing B] in
def clusterNum4 (A₁ A₂ : B) : B := 1 + A₁ + A₂

omit [StarRing B] in
def clusterNum5 (A₁ : B) : B := 1 + A₁

omit [StarRing B] in
/-- **Stage M₁₁ (`quadraticDiscriminant`)**:
Universal quadratic-root discriminant operator `((2 : ℤ) • X - 1) * ((2 : ℤ) • X - 1)`. -/
def quadraticDiscriminant (X : B) : B :=
  ((2 : ℤ) • X - 1) * ((2 : ℤ) • X - 1)

omit [StarRing B] in
/-- **Archetype W₁ (`symbolKernel`, `symbolKernelBar`)**:
Multiplicative dilogarithm symbol kernels `symbolKernel X = (1 - X) * X = -idempotencyDefect X`
and `symbolKernelBar X = (1 + X) * X = idempotencyDefectBar X`. -/
def symbolKernel (X : B) : B := (1 - X) * X

omit [StarRing B] in
def symbolKernelBar (X : B) : B := (1 + X) * X

omit [StarRing B] in
/-- **Archetype W₃ (`plabicNullSpaceProj`)**:
Complementary twistor null-space idempotent projector
`plabicNullSpaceProj P A C = (1 + conePlus P A) * (1 - coneMinus P C) * (1 - P) * (1 + coneMinus P C) * (1 - conePlus P A) = chartBruhatConj P A C (1 - P)`. -/
def plabicNullSpaceProj (P A C : B) : B :=
  (1 + conePlus P A) * (1 - coneMinus P C) * (1 - P) * (1 + coneMinus P C) * (1 - conePlus P A)

omit [StarRing B] in
/-- **Theorem M₁₁.1 (`stage_M11_plabic_incidence_square_move_cluster_pentagon_and_discriminant`)**:
For any idempotent `P` and arbitrary operators, this packages the existing operator-level
plabic incidence/reconstruction identities, the two-chart transition, a noncommutative
polynomial rearrangement, and the universal quadratic discriminant. The names do not
assert a classical Grassmannian or cluster-algebra construction. -/
theorem stage_M11_plabic_incidence_square_move_cluster_pentagon_and_discriminant
    {P : B} (hP : P * P = P) (A C X A₁ A₂ : B) :
    chartBruhatConj P A C (P + coneMinus P C) = P - conePlus P A ∧
    plabicBoundaryOp P A C * plabicTwistorSol P A C X = 0 ∧
    plabicBoundaryOp P A C * X + plabicTwistorSol P A C X = X ∧
    clusterNum3 A₂ * clusterNum5 A₁ - A₁ * A₂ = clusterNum4 A₁ A₂ + comm A₂ A₁ ∧
    (1 + conePlus P A) * (1 + coneMinus P C) + (1 - coneMinus P C) * (1 - conePlus P A) =
      (2 : ℤ) • (1 : B) + genV P A C ∧
    quadraticDiscriminant X = (4 : ℤ) • idempotencyDefect X + 1 ∧
    quadraticDiscriminant (qgtPlus P A C) = (4 : ℤ) • idempotencyDefect (qgtPlus P A C) + 1 ∧
    quadraticDiscriminant (peirceTransfer P A C) =
      radicalLetterPlus P A C * radicalLetterPlus P A C := by
  refine ⟨(chart_bruhat_conjugation_transition hP A C).1, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · exact (plabic_boundary_constraint_and_twistor_solution hP A C X).2.2.2.2.1
  · exact (plabic_boundary_constraint_and_twistor_solution hP A C X).2.2.2.2.2.2
  · unfold clusterNum3 clusterNum4 clusterNum5 comm; noncomm_ring
  · peirce_nf hP
  · unfold quadraticDiscriminant idempotencyDefect; noncomm_ring
  · unfold quadraticDiscriminant idempotencyDefect; noncomm_ring

omit [StarRing B] in
/-- **Lemma W₁.1 (`symbol_kernel_duplication_and_horizon`)**:
For any `X : B` and any idempotent `P` (`P * P = P`) with `A, C : B`:
1. `symbolKernel X = -idempotencyDefect X` and `symbolKernelBar X = idempotencyDefectBar X`;
2. **Universal Duplication Law (`(1 + X)X * (1 - X)X = (1 - X²)X²`):**
   `symbolKernelBar X * symbolKernel X = symbolKernel (X * X)`;
3. **Horizon Symbol Duplication (`S̄₂(Φ) * S₂(Φ) = S₂(V) = -δ(V)`):**
   `symbolKernelBar (genPhi P A C) * symbolKernel (genPhi P A C) = symbolKernel (genV P A C)`. -/
theorem symbol_kernel_duplication_and_horizon {P : B} (hP : P * P = P) (X A C : B) :
    symbolKernel X = -idempotencyDefect X ∧
    symbolKernelBar X = idempotencyDefectBar X ∧
    symbolKernelBar X * symbolKernel X = symbolKernel (X * X) ∧
    symbolKernelBar (genPhi P A C) * symbolKernel (genPhi P A C) =
      symbolKernel (genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold symbolKernel idempotencyDefect; noncomm_ring
  · unfold symbolKernelBar idempotencyDefectBar; noncomm_ring
  · unfold symbolKernel symbolKernelBar; noncomm_ring
  · unfold symbolKernel symbolKernelBar; peirce_nf hP

omit [StarRing B] in
/-- **Lemma W₂.1 (`pentagon_cluster_recurrence_and_invariants`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`, let `T = peirceTransfer P A C` and
`T_bar = peirceTransferComplement P A C`:
1. **Trace and Exchange Product:**
   `T + T_bar = 1` and `T * T_bar = -genV P A C`;
2. **Exact 2-Step and 3-Step Fibonacci–Pentagon Reductions:**
   - `T * T = T + genV P A C`,
   - `T * T * T = (1 + genV P A C) * T + genV P A C`;
3. **3-Step and 5-Step Symmetric Pentagon Trace Invariants (Independent of `P` and `Φ`):**
   - `T * T * T + T_bar * T_bar * T_bar = 1 + (3 : ℤ) • genV P A C`,
   - `T * T * T * T * T + T_bar * T_bar * T_bar * T_bar * T_bar =
      1 + (5 : ℤ) • genV P A C + (5 : ℤ) • (genV P A C * genV P A C)`. -/
theorem pentagon_cluster_recurrence_and_invariants {P : B} (hP : P * P = P) (A C : B) :
    peirceTransfer P A C + peirceTransferComplement P A C = 1 ∧
    peirceTransfer P A C * peirceTransferComplement P A C = -genV P A C ∧
    peirceTransfer P A C * peirceTransfer P A C = peirceTransfer P A C + genV P A C ∧
    peirceTransfer P A C * peirceTransfer P A C * peirceTransfer P A C =
      (1 + genV P A C) * peirceTransfer P A C + genV P A C ∧
    (peirceTransfer P A C * peirceTransfer P A C * peirceTransfer P A C) +
      (peirceTransferComplement P A C * peirceTransferComplement P A C * peirceTransferComplement P A C) =
      1 + (3 : ℤ) • genV P A C ∧
    (peirceTransfer P A C * peirceTransfer P A C * peirceTransfer P A C *
       peirceTransfer P A C * peirceTransfer P A C) +
      (peirceTransferComplement P A C * peirceTransferComplement P A C *
       peirceTransferComplement P A C * peirceTransferComplement P A C *
       peirceTransferComplement P A C) =
      1 + (5 : ℤ) • genV P A C + (5 : ℤ) • (genV P A C * genV P A C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirceTransfer, peirceTransferComplement]; peirce_nf hP)

omit [StarRing B] in
/-- **Lemma W₃.1 (`plabic_boundary_and_null_space_projectors`)**:
For any idempotent `P` (`P * P = P`) and any `A, C, Z : B`:
1. `plabicBoundaryOp P A C` and `plabicNullSpaceProj P A C` are mutually orthogonal idempotents
   summing to `1`, with `plabicTwistorSol P A C Z = plabicNullSpaceProj P A C * Z`;
2. Consequently, `plabicBoundaryOp P A C * (plabicNullSpaceProj P A C * Z) = 0`. -/
theorem plabic_boundary_and_null_space_projectors {P : B} (hP : P * P = P) (A C Z : B) :
    plabicBoundaryOp P A C * plabicBoundaryOp P A C = plabicBoundaryOp P A C ∧
    plabicNullSpaceProj P A C * plabicNullSpaceProj P A C = plabicNullSpaceProj P A C ∧
    plabicBoundaryOp P A C * plabicNullSpaceProj P A C = 0 ∧
    plabicNullSpaceProj P A C * plabicBoundaryOp P A C = 0 ∧
    plabicBoundaryOp P A C + plabicNullSpaceProj P A C = 1 ∧
    plabicTwistorSol P A C Z = plabicNullSpaceProj P A C * Z ∧
    plabicBoundaryOp P A C * (plabicNullSpaceProj P A C * Z) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩ <;>
    (simp only [plabicBoundaryOp, plabicNullSpaceProj]; peirce_nf hP)

/-- **Lemma W₄.1 & W₅.1 (`square_root_letters_and_cluster_adjacency`)**:
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A, C : B`:
1. **Exact Square-Root Discriminant Identities:**
   `radicalLetterPlus P A C * radicalLetterPlus P A C = 1 + (4 : ℤ) • genV P A C` and
   `radicalLetterMinus P A C * radicalLetterMinus P A C = 1 - (4 : ℤ) • genV P A C`;
2. **Cluster Adjacency Commutativity with the Horizon Metric `V` & Frozen Minors:**
   - `comm (peirceTransfer P A C) (genV P A C) = 0`,
   - `comm (radicalLetterPlus P A C) (genV P A C) = 0`,
   - `comm (radicalLetterMinus P A C) (genV P A C) = 0`,
   - `comm (1 - qgtPlus P A C) (1 - qgtMinus P A C) = 0`;
3. **Incompatible / Mutated Radical Anticommutator & Star Reality:**
   - `anticomm (radicalLetterPlus P A C) (radicalLetterMinus P A C) = (2 : ℤ) • (1 : B)`,
   - `star (radicalLetterPlus P A (star A)) = radicalLetterPlus P A (star A)`. -/
theorem square_root_letters_and_cluster_adjacency
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A C : B) :
    radicalLetterPlus P A C * radicalLetterPlus P A C = 1 + (4 : ℤ) • genV P A C ∧
    radicalLetterMinus P A C * radicalLetterMinus P A C = 1 - (4 : ℤ) • genV P A C ∧
    comm (peirceTransfer P A C) (genV P A C) = 0 ∧
    comm (radicalLetterPlus P A C) (genV P A C) = 0 ∧
    comm (radicalLetterMinus P A C) (genV P A C) = 0 ∧
    comm (1 - qgtPlus P A C) (1 - qgtMinus P A C) = 0 ∧
    anticomm (radicalLetterPlus P A C) (radicalLetterMinus P A C) = (2 : ℤ) • (1 : B) ∧
    star (radicalLetterPlus P A (star A)) = radicalLetterPlus P A (star A) := by
  rcases operator_square_root_symbol_letters hP A C with ⟨_, _, hSqP, hSqM, _, _, _, _, _, _⟩
  rcases radical_letter_rationalization_and_adjacency hP A C with
    ⟨_, _, _, _, _, hAnti, hCommP, hCommM⟩
  rcases radical_biquadratic_and_star_reality hP hPsym A C with
    ⟨_, _, hStarP, _, _⟩
  refine ⟨hSqP, hSqM, ?_, hCommP, hCommM, ?_, hAnti, hStarP⟩
  · unfold peirceTransfer; peirce_nf hP
  · unfold qgtPlus qgtMinus; peirce_nf hP

/-- **Stage D₂₄ Master Synthesis (`stage_D24_pentagon_cluster_symbol_duplication_and_radical_adjacency_master_synthesis`)**:
Unifies Archetypes `W₁ → W₅` of Stage `D₂₄` over `[Ring B] [StarRing B]`. -/
theorem stage_D24_pentagon_cluster_symbol_duplication_and_radical_adjacency_master_synthesis
    {P X A C Z : B} (hP : P * P = P) (hPsym : star P = P) :
    -- 1. Multiplicative Symbol Kernel Duplication (`S̄₂(X) S₂(X) = S₂(X²)`) (W₁):
    symbolKernelBar X * symbolKernel X = symbolKernel (X * X) ∧
    symbolKernelBar (genPhi P A C) * symbolKernel (genPhi P A C) = symbolKernel (genV P A C) ∧
    -- 2. A₂ Pentagon 5-Step Operator Recurrence & Symmetric Trace Invariant (W₂):
    peirceTransfer P A C * peirceTransferComplement P A C = -genV P A C ∧
    (peirceTransfer P A C * peirceTransfer P A C * peirceTransfer P A C *
       peirceTransfer P A C * peirceTransfer P A C) +
      (peirceTransferComplement P A C * peirceTransferComplement P A C *
       peirceTransferComplement P A C * peirceTransferComplement P A C *
       peirceTransferComplement P A C) =
      1 + (5 : ℤ) • genV P A C + (5 : ℤ) • (genV P A C * genV P A C) ∧
    -- 3. Plabic Boundary & Null-Space Orthogonal Projector Decomposition (`C * Z_sol = 0`) (W₃):
    plabicBoundaryOp P A C * plabicNullSpaceProj P A C = 0 ∧
    plabicBoundaryOp P A C + plabicNullSpaceProj P A C = 1 ∧
    plabicBoundaryOp P A C * (plabicNullSpaceProj P A C * Z) = 0 ∧
    -- 4. Operator Square-Root Discriminants `(Δ_rad^+)² = 1 + 4V` & `(Δ_rad^-)² = 1 - 4V` (W₄):
    radicalLetterPlus P A C * radicalLetterPlus P A C = 1 + (4 : ℤ) • genV P A C ∧
    radicalLetterMinus P A C * radicalLetterMinus P A C = 1 - (4 : ℤ) • genV P A C ∧
    -- 5. Cluster Adjacency Commutators (`[Δ_rad^±, V] = 0`) & Star Reality (W₅):
    comm (peirceTransfer P A C) (genV P A C) = 0 ∧
    comm (radicalLetterPlus P A C) (genV P A C) = 0 ∧
    comm (radicalLetterMinus P A C) (genV P A C) = 0 ∧
    comm (1 - qgtPlus P A C) (1 - qgtMinus P A C) = 0 ∧
    anticomm (radicalLetterPlus P A C) (radicalLetterMinus P A C) = (2 : ℤ) • (1 : B) ∧
    star (radicalLetterPlus P A (star A)) = radicalLetterPlus P A (star A) := by
  rcases symbol_kernel_duplication_and_horizon hP X A C with ⟨_, _, hS3, hS4⟩
  rcases pentagon_cluster_recurrence_and_invariants hP A C with ⟨_, hP2, _, _, _, hP6⟩
  rcases plabic_boundary_and_null_space_projectors hP A C Z with ⟨_, _, hN3, _, hN5, _, hN6⟩
  rcases square_root_letters_and_cluster_adjacency hP hPsym A C with
    ⟨hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8⟩
  exact ⟨hS3, hS4, hP2, hP6, hN3, hN5, hN6, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8⟩

/-! ### 8. Stage D₂₅ (`X₁ → X₅`): Non-Commutative Pentagon, Hexagon, and Heptagon Braiding &
Klein-Bottle Penrose Tiling Operator Lift

Lifts the scalar golden-ratio pentagon/hexagon identities (`FibonacciPentagonEquationBridge`,
`FibonacciHexagonEquationBridge`), the 5/6/7-gon Lucas/Fibonacci recurrences, the Artin/Steinberg
hexagon braid relations (`Unipotent`), and Penrose rhomb (Kite/Dart) inflation-deflation on a
non-orientable Klein bottle (`KleinBottleNonsymmorphicOperatorLift`, `KleinBottleCyclotomicChiralLift`)
to pure operator identities over an arbitrary non-commutative ring `[Ring B]`. -/

omit [StarRing B] in
/-- **Archetype X₁ (`opGoldenInverse`)**:
The non-commutative operator lift `T - 1 = -peirceTransferComplement P A C` of the inverse
golden ratio `ϕ⁻¹ = ϕ - 1`, satisfying `T * opGoldenInverse = V` and `opGoldenInverse² + opGoldenInverse = V`. -/
def opGoldenInverse (P A C : B) : B :=
  peirceTransfer P A C - 1

omit [StarRing B] in
/-- **Archetype X₂ (`polygonLucas5`, `polygonLucas6`, `polygonLucas7`)**:
The symmetric 5-step (Pentagon), 6-step (Hexagon), and 7-step (Heptagon) Lucas trace operators
`Tⁿ + T_barⁿ` in the non-commutative ring `B`. -/
def polygonLucas5 (P A C : B) : B :=
  (peirceTransfer P A C) ^ 5 + (peirceTransferComplement P A C) ^ 5

omit [StarRing B] in
def polygonLucas6 (P A C : B) : B :=
  (peirceTransfer P A C) ^ 6 + (peirceTransferComplement P A C) ^ 6

omit [StarRing B] in
def polygonLucas7 (P A C : B) : B :=
  (peirceTransfer P A C) ^ 7 + (peirceTransferComplement P A C) ^ 7

omit [StarRing B] in
/-- **Archetype X₂ (`polygonFib5`, `polygonFib6`, `polygonFib7`)**:
The 5-step (Pentagon), 6-step (Hexagon), and 7-step (Heptagon) Fibonacci operator polynomials
in `V = genV P A C` governing `Tⁿ - T_barⁿ = polygonFib_n * radicalLetterPlus`. -/
def polygonFib5 (P A C : B) : B :=
  1 + (3 : ℤ) • genV P A C + genV P A C * genV P A C

omit [StarRing B] in
def polygonFib6 (P A C : B) : B :=
  1 + (4 : ℤ) • genV P A C + (3 : ℤ) • (genV P A C * genV P A C)

omit [StarRing B] in
def polygonFib7 (P A C : B) : B :=
  1 + (5 : ℤ) • genV P A C + (6 : ℤ) • (genV P A C * genV P A C) +
    genV P A C * genV P A C * genV P A C

omit [StarRing B] in
/-- **Archetype X₄ (`penroseKiteOp`, `penroseDartOp`)**:
The non-commutative Penrose rhomb prototile operators in `B`:
- `penroseKiteOp P A C := peirceTransfer P A C` (Thick Rhomb / Kite operator),
- `penroseDartOp P A C := genV P A C` (Thin Rhomb / Dart operator). -/
def penroseKiteOp (P A C : B) : B :=
  peirceTransfer P A C

omit [StarRing B] in
def penroseDartOp (P A C : B) : B :=
  genV P A C

omit [StarRing B] in
/-- **Lemma X₁.1 (`operator_golden_inverse_and_pentagon_all_tau_lift`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. `opGoldenInverse P A C = -peirceTransferComplement P A C`;
2. **Product with `peirceTransfer` (`ϕ · ϕ⁻¹ = V`):**
   `peirceTransfer P A C * opGoldenInverse P A C = genV P A C` and
   `opGoldenInverse P A C * peirceTransfer P A C = genV P A C`;
3. **Non-Commutative Lift of `golden_ratio_inverse_sum_identity` (`(1/ϕ)² + 1/ϕ = 1`):**
   `opGoldenInverse P A C * opGoldenInverse P A C + opGoldenInverse P A C = genV P A C`;
4. **Non-Commutative Lift of `pentagon_equation_all_tau` (`(1/√ϕ)² - (1/ϕ)³ = (-1/ϕ)²`):**
   `genV P A C * opGoldenInverse P A C -
      opGoldenInverse P A C * opGoldenInverse P A C * opGoldenInverse P A C =
    peirceTransferComplement P A C * peirceTransferComplement P A C`. -/
theorem operator_golden_inverse_and_pentagon_all_tau_lift
    {P : B} (hP : P * P = P) (A C : B) :
    opGoldenInverse P A C = -peirceTransferComplement P A C ∧
    peirceTransfer P A C * opGoldenInverse P A C = genV P A C ∧
    opGoldenInverse P A C * peirceTransfer P A C = genV P A C ∧
    opGoldenInverse P A C * opGoldenInverse P A C + opGoldenInverse P A C = genV P A C ∧
    genV P A C * opGoldenInverse P A C -
        opGoldenInverse P A C * opGoldenInverse P A C * opGoldenInverse P A C =
      peirceTransferComplement P A C * peirceTransferComplement P A C := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [opGoldenInverse, peirceTransfer, peirceTransferComplement]; peirce_nf hP)

omit [StarRing B] in
/-- **Lemma X₂.1 (`pentagon_hexagon_heptagon_lucas_and_fibonacci_hierarchy`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Pentagon (`n = 5`), Hexagon (`n = 6`), and Heptagon (`n = 7`) Lucas Operator Expansions:**
   - `polygonLucas5 P A C = 1 + (5 : ℤ) • genV P A C + (5 : ℤ) • (genV P A C * genV P A C)` and
     `polygonLucas5 P A C - 1 = (5 : ℤ) • (genV P A C * (1 + genV P A C))`,
   - `polygonLucas6 P A C = 1 + (6 : ℤ) • genV P A C + (9 : ℤ) • (genV P A C * genV P A C) +
       (2 : ℤ) • (genV P A C * genV P A C * genV P A C)`,
   - `polygonLucas7 P A C = 1 + (7 : ℤ) • genV P A C + (14 : ℤ) • (genV P A C * genV P A C) +
       (7 : ℤ) • (genV P A C * genV P A C * genV P A C)` and
     `polygonLucas7 P A C - 1 = (7 : ℤ) • (genV P A C * ((1 + genV P A C) * (1 + genV P A C)))`;
2. **Cross-Polygon Recurrence Uniting Pentagon (`n = 5`), Hexagon (`n = 6`), and Heptagon (`n = 7`):**
   - `polygonLucas7 P A C = polygonLucas6 P A C + genV P A C * polygonLucas5 P A C`,
   - `polygonFib7 P A C = polygonFib6 P A C + genV P A C * polygonFib5 P A C`;
3. **Hexagon (`n = 6`) and Heptagon (`n = 7`) Transfer Powers & Radical Difference Factorizations:**
   - `(peirceTransfer P A C) ^ 6 = polygonFib6 P A C * peirceTransfer P A C + genV P A C * polygonFib5 P A C`,
   - `(peirceTransfer P A C) ^ 7 = polygonFib7 P A C * peirceTransfer P A C + genV P A C * polygonFib6 P A C`,
   - `(peirceTransfer P A C) ^ 5 - (peirceTransferComplement P A C) ^ 5 = polygonFib5 P A C * radicalLetterPlus P A C`,
   - `(peirceTransfer P A C) ^ 6 - (peirceTransferComplement P A C) ^ 6 = polygonFib6 P A C * radicalLetterPlus P A C`,
   - `(peirceTransfer P A C) ^ 7 - (peirceTransferComplement P A C) ^ 7 = polygonFib7 P A C * radicalLetterPlus P A C`. -/
theorem pentagon_hexagon_heptagon_lucas_and_fibonacci_hierarchy
    {P : B} (hP : P * P = P) (A C : B) :
    polygonLucas5 P A C =
      1 + (5 : ℤ) • genV P A C + (5 : ℤ) • (genV P A C * genV P A C) ∧
    polygonLucas5 P A C - 1 = (5 : ℤ) • (genV P A C * (1 + genV P A C)) ∧
    polygonLucas6 P A C =
      1 + (6 : ℤ) • genV P A C + (9 : ℤ) • (genV P A C * genV P A C) +
        (2 : ℤ) • (genV P A C * genV P A C * genV P A C) ∧
    polygonLucas7 P A C =
      1 + (7 : ℤ) • genV P A C + (14 : ℤ) • (genV P A C * genV P A C) +
        (7 : ℤ) • (genV P A C * genV P A C * genV P A C) ∧
    polygonLucas7 P A C - 1 =
      (7 : ℤ) • (genV P A C * ((1 + genV P A C) * (1 + genV P A C))) ∧
    polygonLucas7 P A C = polygonLucas6 P A C + genV P A C * polygonLucas5 P A C ∧
    polygonFib7 P A C = polygonFib6 P A C + genV P A C * polygonFib5 P A C ∧
    (peirceTransfer P A C) ^ 6 =
      polygonFib6 P A C * peirceTransfer P A C + genV P A C * polygonFib5 P A C ∧
    (peirceTransfer P A C) ^ 7 =
      polygonFib7 P A C * peirceTransfer P A C + genV P A C * polygonFib6 P A C ∧
    (peirceTransfer P A C) ^ 5 - (peirceTransferComplement P A C) ^ 5 =
      polygonFib5 P A C * radicalLetterPlus P A C ∧
    (peirceTransfer P A C) ^ 6 - (peirceTransferComplement P A C) ^ 6 =
      polygonFib6 P A C * radicalLetterPlus P A C ∧
    (peirceTransfer P A C) ^ 7 - (peirceTransferComplement P A C) ^ 7 =
      polygonFib7 P A C * radicalLetterPlus P A C := by
  have hT2 : peirceTransfer P A C * peirceTransfer P A C =
      peirceTransfer P A C + genV P A C := by
    unfold peirceTransfer; peirce_nf hP
  have hTbar2 : peirceTransferComplement P A C * peirceTransferComplement P A C =
      peirceTransferComplement P A C + genV P A C := by
    unfold peirceTransferComplement; peirce_nf hP
  have hSum : peirceTransfer P A C + peirceTransferComplement P A C = 1 := by
    unfold peirceTransfer peirceTransferComplement; noncomm_ring
  have hDiff : peirceTransfer P A C - peirceTransferComplement P A C =
      radicalLetterPlus P A C := by
    unfold radicalLetterPlus peirceTransfer peirceTransferComplement; noncomm_ring
  have hT5 : (peirceTransfer P A C) ^ 5 =
      polygonFib5 P A C * peirceTransfer P A C +
        genV P A C * (1 + (2 : ℤ) • genV P A C) :=
    (operator_square_root_symbol_letters hP A C).2.2.2.2.2.2.2.2.2
  have hTbar5 : (peirceTransferComplement P A C) ^ 5 =
      polygonFib5 P A C * peirceTransferComplement P A C +
        genV P A C * (1 + (2 : ℤ) • genV P A C) := by
    simp only [polygonFib5, peirceTransferComplement, pow_succ, pow_zero, one_mul]
    peirce_nf hP
  have hT6 : (peirceTransfer P A C) ^ 6 =
      polygonFib6 P A C * peirceTransfer P A C + genV P A C * polygonFib5 P A C := by
    rw [pow_succ, hT5]
    calc
      (polygonFib5 P A C * peirceTransfer P A C + genV P A C * (1 + (2 : ℤ) • genV P A C)) *
          peirceTransfer P A C =
        polygonFib5 P A C * (peirceTransfer P A C * peirceTransfer P A C) +
          genV P A C * (1 + (2 : ℤ) • genV P A C) * peirceTransfer P A C := by noncomm_ring
      _ = polygonFib5 P A C * (peirceTransfer P A C + genV P A C) +
          genV P A C * (1 + (2 : ℤ) • genV P A C) * peirceTransfer P A C := by rw [hT2]
      _ = polygonFib6 P A C * peirceTransfer P A C + genV P A C * polygonFib5 P A C := by
        unfold polygonFib5 polygonFib6
        noncomm_ring
  have hTbar6 : (peirceTransferComplement P A C) ^ 6 =
      polygonFib6 P A C * peirceTransferComplement P A C +
        genV P A C * polygonFib5 P A C := by
    rw [pow_succ, hTbar5]
    calc
      (polygonFib5 P A C * peirceTransferComplement P A C +
          genV P A C * (1 + (2 : ℤ) • genV P A C)) *
          peirceTransferComplement P A C =
        polygonFib5 P A C *
            (peirceTransferComplement P A C * peirceTransferComplement P A C) +
          genV P A C * (1 + (2 : ℤ) • genV P A C) *
            peirceTransferComplement P A C := by noncomm_ring
      _ = polygonFib5 P A C * (peirceTransferComplement P A C + genV P A C) +
          genV P A C * (1 + (2 : ℤ) • genV P A C) *
            peirceTransferComplement P A C := by rw [hTbar2]
      _ = polygonFib6 P A C * peirceTransferComplement P A C +
          genV P A C * polygonFib5 P A C := by
        unfold polygonFib5 polygonFib6
        noncomm_ring
  have hT7 : (peirceTransfer P A C) ^ 7 =
      polygonFib7 P A C * peirceTransfer P A C + genV P A C * polygonFib6 P A C := by
    rw [pow_succ, hT6]
    calc
      (polygonFib6 P A C * peirceTransfer P A C + genV P A C * polygonFib5 P A C) *
          peirceTransfer P A C =
        polygonFib6 P A C * (peirceTransfer P A C * peirceTransfer P A C) +
          genV P A C * polygonFib5 P A C * peirceTransfer P A C := by noncomm_ring
      _ = polygonFib6 P A C * (peirceTransfer P A C + genV P A C) +
          genV P A C * polygonFib5 P A C * peirceTransfer P A C := by rw [hT2]
      _ = (polygonFib6 P A C + genV P A C * polygonFib5 P A C) * peirceTransfer P A C +
          polygonFib6 P A C * genV P A C := by noncomm_ring
      _ = polygonFib7 P A C * peirceTransfer P A C + genV P A C * polygonFib6 P A C := by
        unfold polygonFib5 polygonFib6 polygonFib7
        noncomm_ring
  have hTbar7 : (peirceTransferComplement P A C) ^ 7 =
      polygonFib7 P A C * peirceTransferComplement P A C +
        genV P A C * polygonFib6 P A C := by
    rw [pow_succ, hTbar6]
    calc
      (polygonFib6 P A C * peirceTransferComplement P A C +
          genV P A C * polygonFib5 P A C) *
          peirceTransferComplement P A C =
        polygonFib6 P A C *
            (peirceTransferComplement P A C * peirceTransferComplement P A C) +
          genV P A C * polygonFib5 P A C *
            peirceTransferComplement P A C := by noncomm_ring
      _ = polygonFib6 P A C * (peirceTransferComplement P A C + genV P A C) +
          genV P A C * polygonFib5 P A C *
            peirceTransferComplement P A C := by rw [hTbar2]
      _ = (polygonFib6 P A C + genV P A C * polygonFib5 P A C) *
            peirceTransferComplement P A C +
          polygonFib6 P A C * genV P A C := by noncomm_ring
      _ = polygonFib7 P A C * peirceTransferComplement P A C +
          genV P A C * polygonFib6 P A C := by
        unfold polygonFib5 polygonFib6 polygonFib7
        noncomm_ring
  have hL5 : polygonLucas5 P A C =
      1 + (5 : ℤ) • genV P A C + (5 : ℤ) • (genV P A C * genV P A C) := by
    unfold polygonLucas5
    rw [hT5, hTbar5]
    calc
      (polygonFib5 P A C * peirceTransfer P A C + genV P A C * (1 + (2 : ℤ) • genV P A C)) +
          (polygonFib5 P A C * peirceTransferComplement P A C +
            genV P A C * (1 + (2 : ℤ) • genV P A C)) =
        polygonFib5 P A C * (peirceTransfer P A C + peirceTransferComplement P A C) +
          (2 : ℤ) • (genV P A C * (1 + (2 : ℤ) • genV P A C)) := by noncomm_ring
      _ = 1 + (5 : ℤ) • genV P A C + (5 : ℤ) • (genV P A C * genV P A C) := by
        rw [hSum]; unfold polygonFib5; noncomm_ring
  have hL6 : polygonLucas6 P A C =
      1 + (6 : ℤ) • genV P A C + (9 : ℤ) • (genV P A C * genV P A C) +
        (2 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
    unfold polygonLucas6
    rw [hT6, hTbar6]
    calc
      (polygonFib6 P A C * peirceTransfer P A C + genV P A C * polygonFib5 P A C) +
          (polygonFib6 P A C * peirceTransferComplement P A C +
            genV P A C * polygonFib5 P A C) =
        polygonFib6 P A C * (peirceTransfer P A C + peirceTransferComplement P A C) +
          (2 : ℤ) • (genV P A C * polygonFib5 P A C) := by noncomm_ring
      _ = 1 + (6 : ℤ) • genV P A C + (9 : ℤ) • (genV P A C * genV P A C) +
          (2 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
        rw [hSum]; unfold polygonFib5 polygonFib6; noncomm_ring
  have hL7 : polygonLucas7 P A C =
      1 + (7 : ℤ) • genV P A C + (14 : ℤ) • (genV P A C * genV P A C) +
        (7 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
    unfold polygonLucas7
    rw [hT7, hTbar7]
    calc
      (polygonFib7 P A C * peirceTransfer P A C + genV P A C * polygonFib6 P A C) +
          (polygonFib7 P A C * peirceTransferComplement P A C +
            genV P A C * polygonFib6 P A C) =
        polygonFib7 P A C * (peirceTransfer P A C + peirceTransferComplement P A C) +
          (2 : ℤ) • (genV P A C * polygonFib6 P A C) := by noncomm_ring
      _ = 1 + (7 : ℤ) • genV P A C + (14 : ℤ) • (genV P A C * genV P A C) +
          (7 : ℤ) • (genV P A C * genV P A C * genV P A C) := by
        rw [hSum]; unfold polygonFib6 polygonFib7; noncomm_ring
  refine ⟨hL5, ?_, hL6, hL7, ?_, ?_, ?_, hT6, hT7, ?_, ?_, ?_⟩
  · rw [hL5]; noncomm_ring
  · rw [hL7]; noncomm_ring
  · rw [hL7, hL6, hL5]; noncomm_ring
  · unfold polygonFib5 polygonFib6 polygonFib7; noncomm_ring
  · rw [hT5, hTbar5, ← hDiff]; noncomm_ring
  · rw [hT6, hTbar6, ← hDiff]; noncomm_ring
  · rw [hT7, hTbar7, ← hDiff]; noncomm_ring

omit [StarRing B] in
/-- **Lemma X₃.1 (`hexagon_braid_defect_and_polygon_twist_invariance`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Universal Non-Commutative Hexagon Braid Defect (Yang–Baxter / Artin Braid):**
   - For the unipotent shears `1 + conePlus P A` and `1 + coneMinus P C`,
     `(1 + conePlus P A) * (1 + coneMinus P C) * (1 + conePlus P A) -
      (1 + coneMinus P C) * (1 + conePlus P A) * (1 + coneMinus P C) =
      (1 + genV P A C) * genJ P A C`;
   - For the bicolored plabic shears `plabicWhiteShear P A = 1 + N₊` and `plabicBlackShear P C = 1 - N₋`,
     `plabicWhiteShear P A * plabicBlackShear P C * plabicWhiteShear P A -
      plabicBlackShear P C * plabicWhiteShear P A * plabicBlackShear P C =
      (1 - genV P A C) * genPhi P A C`;
2. **Braided Twist Invariance of Pentagon (`L₅`), Hexagon (`L₆`), and Heptagon (`L₇`) Operators:**
   The permuted Steinberg-braid twist `peircePermutedTwist P A C` fixes `polygonLucas5`,
   `polygonLucas6`, `polygonLucas7`, `polygonFib5`, `polygonFib6`, and `polygonFib7`. -/
theorem hexagon_braid_defect_and_polygon_twist_invariance
    {P : B} (hP : P * P = P) (A C : B) :
    (1 + conePlus P A) * (1 + coneMinus P C) * (1 + conePlus P A) -
        (1 + coneMinus P C) * (1 + conePlus P A) * (1 + coneMinus P C) =
      (1 + genV P A C) * genJ P A C ∧
    plabicWhiteShear P A * plabicBlackShear P C * plabicWhiteShear P A -
        plabicBlackShear P C * plabicWhiteShear P A * plabicBlackShear P C =
      (1 - genV P A C) * genPhi P A C ∧
    peircePermutedTwist P A C (polygonLucas5 P A C) = polygonLucas5 P A C ∧
    peircePermutedTwist P A C (polygonLucas6 P A C) = polygonLucas6 P A C ∧
    peircePermutedTwist P A C (polygonLucas7 P A C) = polygonLucas7 P A C ∧
    peircePermutedTwist P A C (polygonFib5 P A C) = polygonFib5 P A C ∧
    peircePermutedTwist P A C (polygonFib6 P A C) = polygonFib6 P A C ∧
    peircePermutedTwist P A C (polygonFib7 P A C) = polygonFib7 P A C := by
  rcases pentagon_hexagon_heptagon_lucas_and_fibonacci_hierarchy hP A C with
    ⟨hL5, _, hL6, hL7, _, _, _, _, _, _, _, _⟩
  have hTwAdd : ∀ X Y : B,
      peircePermutedTwist P A C (X + Y) =
        peircePermutedTwist P A C X + peircePermutedTwist P A C Y := by
    intro X Y
    unfold peircePermutedTwist parityConj
    noncomm_ring
  have hTwZsmul : ∀ (n : ℤ) (X : B),
      peircePermutedTwist P A C (n • X) = n • peircePermutedTwist P A C X := by
    intro n X
    unfold peircePermutedTwist parityConj
    noncomm_ring
  have hTwMul : ∀ X Y : B,
      peircePermutedTwist P A C (X * Y) =
        peircePermutedTwist P A C X * peircePermutedTwist P A C Y :=
    fun X Y => (peircePermutedTwist_automorphism_and_seed_transport hP A C X Y).2.2.1
  have hTwV : peircePermutedTwist P A C (genV P A C) = genV P A C :=
    (peircePermutedTwist_automorphism_and_seed_transport hP A C 1 1).2.2.2.1
  have hTwOne : peircePermutedTwist P A C 1 = 1 := by
    unfold peircePermutedTwist steinbergBraid steinbergBraidInv parityConj
    peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · peirce_nf hP
  · unfold plabicWhiteShear plabicBlackShear; peirce_nf hP
  · rw [hL5]; simp only [hTwAdd, hTwZsmul, hTwMul, hTwV, hTwOne]
  · rw [hL6]; simp only [hTwAdd, hTwZsmul, hTwMul, hTwV, hTwOne]
  · rw [hL7]; simp only [hTwAdd, hTwZsmul, hTwMul, hTwV, hTwOne]
  · unfold polygonFib5; simp only [hTwAdd, hTwZsmul, hTwMul, hTwV, hTwOne]
  · unfold polygonFib6; simp only [hTwAdd, hTwZsmul, hTwMul, hTwV, hTwOne]
  · unfold polygonFib7; simp only [hTwAdd, hTwZsmul, hTwMul, hTwV, hTwOne]

omit [StarRing B] in
/-- **Lemma X₄.1 & X₅.1 (`klein_bottle_penrose_tiling_inflation_and_meridian_intertwining`)**:
For any idempotent `P` (`P * P = P`) and any `A, C : B`:
1. **Non-Commutative Penrose Rhomb Inflation & Deflation (`Kite = T`, `Dart = V`):**
   - Inflation by `peirceTransfer P A C`:
     `peirceTransfer P A C * penroseKiteOp P A C = penroseKiteOp P A C + penroseDartOp P A C` and
     `peirceTransfer P A C * penroseDartOp P A C = penroseDartOp P A C * penroseKiteOp P A C`;
   - Deflation by `opGoldenInverse P A C`:
     `opGoldenInverse P A C * penroseKiteOp P A C = penroseDartOp P A C` and
     `opGoldenInverse P A C * penroseDartOp P A C =
       penroseDartOp P A C * penroseKiteOp P A C - penroseDartOp P A C`;
2. **Klein-Bottle Meridian Reflection (`parityConj P X = invS P * X * invS P`):**
   - `parityConj P (penroseKiteOp P A C) = penroseKiteOp P (-A) (-C)`,
   - `parityConj P (penroseDartOp P A C) = penroseDartOp P A C`,
   - `penroseKiteOp P A C + parityConj P (penroseKiteOp P A C) = (2 : ℤ) • P`;
3. **Exact Klein-Bottle–Penrose Chiral Sheet Intertwining via `genPhi P A C`:**
   - `genPhi P A C * parityConj P (penroseKiteOp P A C) =
      peirceTransferComplement P A C * genPhi P A C`,
   - `parityConj P (penroseKiteOp P A C) * genPhi P A C =
      genPhi P A C * peirceTransferComplement P A C`;
4. **Descent of Pentagon (`L₅`), Hexagon (`L₆`), and Heptagon (`L₇`) Penrose Traces to the Klein Bottle:**
   - `parityConj P (polygonLucas5 P A C) = polygonLucas5 P A C`,
   - `parityConj P (polygonLucas6 P A C) = polygonLucas6 P A C`,
   - `parityConj P (polygonLucas7 P A C) = polygonLucas7 P A C`,
   - `parityConj P (radicalLetterPlus P A C) = radicalLetterPlus P (-A) (-C)`. -/
theorem klein_bottle_penrose_tiling_inflation_and_meridian_intertwining
    {P : B} (hP : P * P = P) (A C : B) :
    peirceTransfer P A C * penroseKiteOp P A C =
      penroseKiteOp P A C + penroseDartOp P A C ∧
    peirceTransfer P A C * penroseDartOp P A C =
      penroseDartOp P A C * penroseKiteOp P A C ∧
    opGoldenInverse P A C * penroseKiteOp P A C = penroseDartOp P A C ∧
    opGoldenInverse P A C * penroseDartOp P A C =
      penroseDartOp P A C * penroseKiteOp P A C - penroseDartOp P A C ∧
    parityConj P (penroseKiteOp P A C) = penroseKiteOp P (-A) (-C) ∧
    parityConj P (penroseDartOp P A C) = penroseDartOp P A C ∧
    penroseKiteOp P A C + parityConj P (penroseKiteOp P A C) = (2 : ℤ) • P ∧
    genPhi P A C * parityConj P (penroseKiteOp P A C) =
      peirceTransferComplement P A C * genPhi P A C ∧
    parityConj P (penroseKiteOp P A C) * genPhi P A C =
      genPhi P A C * peirceTransferComplement P A C ∧
    parityConj P (polygonLucas5 P A C) = polygonLucas5 P A C ∧
    parityConj P (polygonLucas6 P A C) = polygonLucas6 P A C ∧
    parityConj P (polygonLucas7 P A C) = polygonLucas7 P A C ∧
    parityConj P (radicalLetterPlus P A C) = radicalLetterPlus P (-A) (-C) := by
  rcases pentagon_hexagon_heptagon_lucas_and_fibonacci_hierarchy hP A C with
    ⟨hL5, _, hL6, hL7, _, _, _, _, _, _, _, _⟩
  have hS2 : invS P * invS P = 1 := by peirce_nf hP
  have hParAdd : ∀ X Y : B, parityConj P (X + Y) = parityConj P X + parityConj P Y := by
    intro X Y; unfold parityConj; noncomm_ring
  have hParZsmul : ∀ (n : ℤ) (X : B), parityConj P (n • X) = n • parityConj P X := by
    intro n X; unfold parityConj; noncomm_ring
  have hParMul : ∀ X Y : B, parityConj P (X * Y) = parityConj P X * parityConj P Y := by
    intro X Y
    unfold parityConj
    calc
      invS P * (X * Y) * invS P =
          invS P * X * (invS P * invS P) * Y * invS P := by
        rw [hS2]; noncomm_ring
      _ = (invS P * X * invS P) * (invS P * Y * invS P) := by noncomm_ring
  have hParOne : parityConj P 1 = 1 := by
    unfold parityConj; peirce_nf hP
  have hParV : parityConj P (genV P A C) = genV P A C := by
    unfold parityConj; peirce_nf hP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold penroseKiteOp penroseDartOp peirceTransfer; peirce_nf hP
  · unfold penroseKiteOp penroseDartOp peirceTransfer; peirce_nf hP
  · unfold opGoldenInverse penroseKiteOp penroseDartOp peirceTransfer; peirce_nf hP
  · unfold opGoldenInverse penroseKiteOp penroseDartOp peirceTransfer; peirce_nf hP
  · unfold parityConj penroseKiteOp peirceTransfer genPhi
    simp only [conePlus_neg, coneMinus_neg]
    peirce_nf hP
  · exact hParV
  · unfold parityConj penroseKiteOp peirceTransfer; peirce_nf hP
  · unfold parityConj penroseKiteOp peirceTransfer peirceTransferComplement; peirce_nf hP
  · unfold parityConj penroseKiteOp peirceTransfer peirceTransferComplement; peirce_nf hP
  · rw [hL5]; simp only [hParAdd, hParZsmul, hParMul, hParV, hParOne]
  · rw [hL6]; simp only [hParAdd, hParZsmul, hParMul, hParV, hParOne]
  · rw [hL7]; simp only [hParAdd, hParZsmul, hParMul, hParV, hParOne]
  · unfold parityConj radicalLetterPlus peirceTransfer genPhi
    simp only [conePlus_neg, coneMinus_neg]
    peirce_nf hP

omit [StarRing B] in
/-- **Stage D₂₅ Master Synthesis (`stage_D25_pentagon_hexagon_heptagon_braiding_and_klein_penrose_master_synthesis`)**:
Unifies Archetypes `X₁ → X₅` of Stage `D₂₅` over `[Ring B]`:
1. `X₁`: Non-commutative operator lift of `ϕ⁻¹ = ϕ - 1`, `(1/ϕ)² + 1/ϕ = 1`, and the all-`τ`
   pentagon recoupling identity `V * T_inv - T_inv³ = T_bar²`;
2. `X₂`: Pentagon (`n = 5`), Hexagon (`n = 6`), and Heptagon (`n = 7`) Lucas/Fibonacci operator
   expansions, their cross-polygon recurrence `L₇ = L₆ + V * L₅`, and radical factorizations
   `Tⁿ - T_barⁿ = F_n * R₊`;
3. `X₃`: Universal non-commutative Hexagon Braid defect `(1 + V) * J` and Steinberg-braid twist
   invariance of `L₅`, `L₆`, and `L₇`;
4. `X₄` & `X₅`: Penrose Kite/Dart operator inflation-deflation laws, Klein-bottle meridian
   intertwining `Φ * parityConj P T = T_bar * Φ`, and Klein-bottle quotient invariance of
   `L₅`, `L₆`, and `L₇`. -/
theorem stage_D25_pentagon_hexagon_heptagon_braiding_and_klein_penrose_master_synthesis
    {P : B} (hP : P * P = P) (A C : B) :
    -- 1. Operator Golden Inverse & Pentagon All-τ Lift (X₁):
    opGoldenInverse P A C * opGoldenInverse P A C + opGoldenInverse P A C = genV P A C ∧
    genV P A C * opGoldenInverse P A C -
        opGoldenInverse P A C * opGoldenInverse P A C * opGoldenInverse P A C =
      peirceTransferComplement P A C * peirceTransferComplement P A C ∧
    -- 2. Pentagon (n=5), Hexagon (n=6), Heptagon (n=7) Recurrence & Divisibility (X₂):
    polygonLucas5 P A C - 1 = (5 : ℤ) • (genV P A C * (1 + genV P A C)) ∧
    polygonLucas6 P A C =
      1 + (6 : ℤ) • genV P A C + (9 : ℤ) • (genV P A C * genV P A C) +
        (2 : ℤ) • (genV P A C * genV P A C * genV P A C) ∧
    polygonLucas7 P A C - 1 =
      (7 : ℤ) • (genV P A C * ((1 + genV P A C) * (1 + genV P A C))) ∧
    polygonLucas7 P A C = polygonLucas6 P A C + genV P A C * polygonLucas5 P A C ∧
    (peirceTransfer P A C) ^ 7 - (peirceTransferComplement P A C) ^ 7 =
      polygonFib7 P A C * radicalLetterPlus P A C ∧
    -- 3. Hexagon Braid Anomaly & Braided Twist Invariance of L₅, L₆, L₇ (X₃):
    (1 + conePlus P A) * (1 + coneMinus P C) * (1 + conePlus P A) -
        (1 + coneMinus P C) * (1 + conePlus P A) * (1 + coneMinus P C) =
      (1 + genV P A C) * genJ P A C ∧
    peircePermutedTwist P A C (polygonLucas5 P A C) = polygonLucas5 P A C ∧
    peircePermutedTwist P A C (polygonLucas6 P A C) = polygonLucas6 P A C ∧
    peircePermutedTwist P A C (polygonLucas7 P A C) = polygonLucas7 P A C ∧
    -- 4. Klein-Bottle Penrose Kite/Dart Inflation & Meridian Intertwining (X₄, X₅):
    peirceTransfer P A C * penroseKiteOp P A C =
      penroseKiteOp P A C + penroseDartOp P A C ∧
    peirceTransfer P A C * penroseDartOp P A C =
      penroseDartOp P A C * penroseKiteOp P A C ∧
    genPhi P A C * parityConj P (penroseKiteOp P A C) =
      peirceTransferComplement P A C * genPhi P A C ∧
    parityConj P (polygonLucas5 P A C) = polygonLucas5 P A C ∧
    parityConj P (polygonLucas6 P A C) = polygonLucas6 P A C ∧
    parityConj P (polygonLucas7 P A C) = polygonLucas7 P A C := by
  rcases operator_golden_inverse_and_pentagon_all_tau_lift hP A C with
    ⟨_, _, _, hG1, hG2⟩
  rcases pentagon_hexagon_heptagon_lucas_and_fibonacci_hierarchy hP A C with
    ⟨_, hP5, hP6, _, hP7, hRec, _, _, _, _, _, hDiff7⟩
  rcases hexagon_braid_defect_and_polygon_twist_invariance hP A C with
    ⟨hHex, _, hTw5, hTw6, hTw7, _, _, _⟩
  rcases klein_bottle_penrose_tiling_inflation_and_meridian_intertwining hP A C with
    ⟨hInfK, hInfD, _, _, _, _, _, hInter, _, hKl5, hKl6, hKl7, _⟩
  exact ⟨hG1, hG2, hP5, hP6, hP7, hRec, hDiff7, hHex, hTw5, hTw6, hTw7,
         hInfK, hInfD, hInter, hKl5, hKl6, hKl7⟩

omit [StarRing B] in
/-- **Operator Braiding Conjugation (`operatorBraidConj`)**:
In any non-commutative ring `B`, conjugates a twist operator `R_op` by a fusion operator `F_op`:
`operatorBraidConj F_op R_op = F_op * R_op * F_op`, lifting `B = F R F` (`FibonacciBraiding.lean`). -/
def operatorBraidConj (F_op R_op : B) : B :=
  F_op * R_op * F_op

omit [StarRing B] in
/-- **Universal Artin / Yang–Baxter Hexagon Braid Defect (`artinBraidDefect`)**:
In any non-commutative ring `B`, `artinBraidDefect X Y = X * Y * X - Y * X * Y`. -/
def artinBraidDefect (X Y : B) : B :=
  X * Y * X - Y * X * Y

omit [StarRing B] in
/-- **Klein-Bottle White and Black Glide Reflections (`kleinGlideWhite`, `kleinGlideBlack`)**:
Composites of the Peirce meridian reflection `invS P` with the white (`1 + N₊`) and black (`1 - N₋`)
horocycle shears in `B`. -/
def kleinGlideWhite (P A : B) : B :=
  invS P * plabicWhiteShear P A

omit [StarRing B] in
def kleinGlideBlack (P C : B) : B :=
  invS P * plabicBlackShear P C

omit [StarRing B] in
/-- **Odd Peirce Generator Carrier (`peirceOddGeneratorSet`)**:
The 4-element subset `{conePlus P A, coneMinus P C, genPhi P A C, genJ P A C}` of `B` on which
`parityConjRingEquiv hP` acts by `-1`. -/
def peirceOddGeneratorSet (P A C : B) : Set B :=
  {conePlus P A, coneMinus P C, genPhi P A C, genJ P A C}

omit [StarRing B] in
/-- **Theorem X₆.1 (`peirceBdG_penrose_fusion_and_s3_artin_braid_bridge`)**:
Connects the non-commutative Peirce–BdG fusion operator `peirceBdGHamiltonian P D A C`
(`OperatorZornPeirceTetraktysBridge.lean`), `operatorBraidConj`, and `artinBraidDefect`
to `FibonacciParafermion.F_matrix`, `FiniteFibonacciFusionMatrix.fibonacciFusionMatrix`,
and the `S₃` cyclotomic reflections `s3Refl0, s3Refl1, s3Refl2` (`CyclotomicBridge.lean`):
1. Over `ℝ` and `ℂ`, `FibonacciParafermion.F_matrix a b = massiveBdGHamiltonian a b` and
   `FiniteFibonacciFusionMatrix.fibonacciFusionMatrix τ s = massiveBdGHamiltonian τ s`;
2. Under the operator Penrose/Fibonacci golden relation `evenGrade P D * evenGrade P D + genV P A C = 1`
   and `comm (evenGrade P D) (genJ P A C) = 0`, `F_op = peirceBdGHamiltonian P D A C` is an exact
   involution (`F_op * F_op = 1`), so `operatorBraidConj F_op` is involutive and multiplicative:
   `operatorBraidConj F_op (operatorBraidConj F_op R_op) = R_op` and
   `operatorBraidConj F_op R_op * operatorBraidConj F_op S_op = operatorBraidConj F_op (R_op * S_op)`;
3. For the `S₃` cyclotomic reflections `s3Refl0, s3Refl1, s3Refl2`, the Artin / Yang–Baxter
   braid defects are controlled by `idempotencyDefect (genV P A C)`:
   `artinBraidDefect (s3Refl0 P A C) (s3Refl1 P A C) = idempotencyDefect (genV P A C) * s3Refl0 P A C` and
   `artinBraidDefect (s3Refl0 P A C) (s3Refl2 P A C) = idempotencyDefect (genV P A C) * s3Refl0 P A C`;
4. Furthermore, `(peirceTransfer P A C) ^ 3 + 1 = cyclotomicSix (peirceTransfer P A C) * (peirceTransfer P A C + 1)`. -/
theorem peirceBdG_penrose_fusion_and_s3_artin_braid_bridge
    {P : B} (hP : P * P = P) (D A C R_op S_op : B) (a b : ℝ) (τ s : ℂ) :
    InfoGeometry.Canonical.FibonacciParafermionAtoms.F_matrix a b =
      InfoGeometry.Physics.massiveBdGHamiltonian a b ∧
    InfoGeometry.Canonical.FiniteFibonacciFusionMatrix.fibonacciFusionMatrix τ s =
      InfoGeometry.Physics.massiveBdGHamiltonian τ s ∧
    (comm (evenGrade P D) (genJ P A C) = 0 →
      evenGrade P D * evenGrade P D + genV P A C = 1 →
      let F_op := InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceBdGHamiltonian P D A C
      F_op * F_op = 1 ∧
      operatorBraidConj F_op (operatorBraidConj F_op R_op) = R_op ∧
      operatorBraidConj F_op R_op * operatorBraidConj F_op S_op =
        operatorBraidConj F_op (R_op * S_op)) ∧
    artinBraidDefect (s3Refl0 P A C) (s3Refl1 P A C) =
      idempotencyDefect (genV P A C) * s3Refl0 P A C ∧
    artinBraidDefect (s3Refl0 P A C) (s3Refl2 P A C) =
      idempotencyDefect (genV P A C) * s3Refl0 P A C ∧
    (peirceTransfer P A C) ^ 3 + 1 =
      cyclotomicSix (peirceTransfer P A C) * (peirceTransfer P A C + 1) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro hComm hGold
    dsimp only
    let F_op := InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceBdGHamiltonian P D A C
    have hSq : F_op * F_op = 1 := by
      rw [InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceBdGHamiltonian_sq_of_comm_genJ
        hP D A C hComm, hGold]
    refine ⟨hSq, ?_, ?_⟩
    · unfold operatorBraidConj
      calc
        F_op * (F_op * R_op * F_op) * F_op = (F_op * F_op) * R_op * (F_op * F_op) := by noncomm_ring
        _ = R_op := by rw [hSq]; noncomm_ring
    · unfold operatorBraidConj
      calc
        (F_op * R_op * F_op) * (F_op * S_op * F_op) =
            F_op * R_op * (F_op * F_op) * S_op * F_op := by noncomm_ring
        _ = F_op * (R_op * S_op) * F_op := by rw [hSq]; noncomm_ring
  · unfold artinBraidDefect s3Refl0 s3Refl1 cubeRootOp idempotencyDefect
    peirce_nf hP
  · unfold artinBraidDefect s3Refl0 s3Refl2 cubeRootOpConj idempotencyDefect
    peirce_nf hP
  · simp only [cyclotomicSix, peirceTransfer, pow_succ, pow_zero, one_mul]
    peirce_nf hP

omit [StarRing B] in
/-- **Theorem X₇.1 (`klein_bottle_twisted_commutant_and_glide_reflection_bridge`)**:
Connects the Peirce spine directly to `KleinBottleTwistedCommutantBridge`
(`ordinaryCommutant`, `twistedCommutant`) via `parityConjRingEquiv hP : B ≃+* B`:
1. `Function.Involutive (parityConjRingEquiv hP)`;
2. On `peirceOddGeneratorSet P A C = {N₊, N₋, Φ, J}`:
   - `genV P A C` and every Mandelbrot cycle sum `δ^[n](Q₊) + δ^[n](Q₋)` lie in
     `ordinaryCommutant (peirceOddGeneratorSet P A C)`,
   - `invS P`, `genSig P A C`, and every chiral cycle difference `qgtDefectDiff P A C n` lie in
     `twistedCommutant (peirceOddGeneratorSet P A C) (parityConjRingEquiv hP)`,
   - Their product `genSig P A C * qgtDefectDiff P A C n` lies in
     `ordinaryCommutant (peirceOddGeneratorSet P A C)`;
3. **Non-Commutative Klein-Bottle Presentation `U T_± U = T_±⁻¹` and Glide Reflections:**
   `invS P * plabicWhiteShear P A * invS P = plabicWhiteShear P (-A)`,
   `invS P * plabicBlackShear P C * invS P = plabicBlackShear P (-C)`,
   `kleinGlideWhite P A * kleinGlideWhite P A = 1`,
   `kleinGlideBlack P C * kleinGlideBlack P C = 1`, and
   `kleinGlideWhite P A * kleinGlideBlack P C = plabicTripWB P (-A) C`. -/
theorem klein_bottle_twisted_commutant_and_glide_reflection_bridge
    {P : B} (hP : P * P = P) (A C : B) (n : ℕ) :
    Function.Involutive (parityConjRingEquiv hP) ∧
    genV P A C ∈ InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.ordinaryCommutant
      (peirceOddGeneratorSet P A C) ∧
    (idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C)) ∈
      InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.ordinaryCommutant
        (peirceOddGeneratorSet P A C) ∧
    invS P ∈ InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant
      (peirceOddGeneratorSet P A C) (parityConjRingEquiv hP) ∧
    genSig P A C ∈ InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant
      (peirceOddGeneratorSet P A C) (parityConjRingEquiv hP) ∧
    qgtDefectDiff P A C n ∈ InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant
      (peirceOddGeneratorSet P A C) (parityConjRingEquiv hP) ∧
    (genSig P A C * qgtDefectDiff P A C n) ∈
      InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.ordinaryCommutant
        (peirceOddGeneratorSet P A C) ∧
    invS P * plabicWhiteShear P A * invS P = plabicWhiteShear P (-A) ∧
    invS P * plabicBlackShear P C * invS P = plabicBlackShear P (-C) ∧
    kleinGlideWhite P A * kleinGlideWhite P A = 1 ∧
    kleinGlideBlack P C * kleinGlideBlack P C = 1 ∧
    kleinGlideWhite P A * kleinGlideBlack P C = plabicTripWB P (-A) C := by
  have hInv : Function.Involutive (parityConjRingEquiv hP) :=
    (parityConjRingEquiv hP).left_inv
  have hV_ord : genV P A C ∈
      InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.ordinaryCommutant
        (peirceOddGeneratorSet P A C) := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl <;> peirce_nf hP
  have hSum_ord :
      (idempotencyDefect^[n] (qgtPlus P A C) + idempotencyDefect^[n] (qgtMinus P A C)) ∈
        InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.ordinaryCommutant
          (peirceOddGeneratorSet P A C) := by
    rcases qgt_defect_iterate_sum_commutes_with_cones hP A C n with ⟨hCP, hCM⟩
    rcases qgt_defect_iterate_sum_commutes_with_generators hP A C n with ⟨hPhi, hJ⟩
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact (sub_eq_zero.mp hCP).symm
    · exact (sub_eq_zero.mp hCM).symm
    · exact (sub_eq_zero.mp hPhi).symm
    · exact (sub_eq_zero.mp hJ).symm
  have hS_tw : invS P ∈
      InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant
        (peirceOddGeneratorSet P A C) (parityConjRingEquiv hP) := by
    intro a _
    change invS P * a = (invS P * a * invS P) * invS P
    peirce_nf hP
  have hSig_tw : genSig P A C ∈
      InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant
        (peirceOddGeneratorSet P A C) (parityConjRingEquiv hP) := by
    intro a ha
    change genSig P A C * a = parityConj P a * genSig P A C
    rcases ha with rfl | rfl | rfl | rfl <;>
      (unfold parityConj; peirce_nf hP)
  have hOdd : ∀ a ∈ peirceOddGeneratorSet P A C, parityConj P a = -a := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl <;> (unfold parityConj; peirce_nf hP)
  have hDiff_tw : qgtDefectDiff P A C n ∈
      InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.twistedCommutant
        (peirceOddGeneratorSet P A C) (parityConjRingEquiv hP) := by
    rcases qgtDefectDiff_anticomm_cones hP A C n with ⟨hAP, hAM⟩
    rcases qgtDefectDiff_anticomm_generators hP A C n with ⟨hAPhi, hAJ⟩
    intro a ha
    change qgtDefectDiff P A C n * a = parityConj P a * qgtDefectDiff P A C n
    rw [hOdd a ha, neg_mul, ← sub_eq_zero]
    rcases ha with rfl | rfl | rfl | rfl
    · unfold anticomm at hAP
      calc
        qgtDefectDiff P A C n * conePlus P A - -(conePlus P A * qgtDefectDiff P A C n) =
            conePlus P A * qgtDefectDiff P A C n + qgtDefectDiff P A C n * conePlus P A := by abel
        _ = 0 := hAP
    · unfold anticomm at hAM
      calc
        qgtDefectDiff P A C n * coneMinus P C - -(coneMinus P C * qgtDefectDiff P A C n) =
            coneMinus P C * qgtDefectDiff P A C n + qgtDefectDiff P A C n * coneMinus P C := by abel
        _ = 0 := hAM
    · unfold anticomm at hAPhi
      calc
        qgtDefectDiff P A C n * genPhi P A C - -(genPhi P A C * qgtDefectDiff P A C n) =
            genPhi P A C * qgtDefectDiff P A C n + qgtDefectDiff P A C n * genPhi P A C := by abel
        _ = 0 := hAPhi
    · unfold anticomm at hAJ
      calc
        qgtDefectDiff P A C n * genJ P A C - -(genJ P A C * qgtDefectDiff P A C n) =
            genJ P A C * qgtDefectDiff P A C n + qgtDefectDiff P A C n * genJ P A C := by abel
        _ = 0 := hAJ
  have hProd_ord : (genSig P A C * qgtDefectDiff P A C n) ∈
      InfoGeometry.Algebra.KleinBottleTwistedCommutantBridge.ordinaryCommutant
        (peirceOddGeneratorSet P A C) := by
    intro a ha
    have h1 : genSig P A C * a = -a * genSig P A C := by
      have h := hSig_tw a ha
      change genSig P A C * a = parityConj P a * genSig P A C at h
      rw [hOdd a ha] at h
      exact h
    have h2 : qgtDefectDiff P A C n * a = -a * qgtDefectDiff P A C n := by
      have h := hDiff_tw a ha
      change qgtDefectDiff P A C n * a = parityConj P a * qgtDefectDiff P A C n at h
      rw [hOdd a ha] at h
      exact h
    calc
      (genSig P A C * qgtDefectDiff P A C n) * a =
          genSig P A C * (qgtDefectDiff P A C n * a) := by rw [mul_assoc]
      _ = genSig P A C * (-a * qgtDefectDiff P A C n) := by rw [h2]
      _ = -(genSig P A C * a) * qgtDefectDiff P A C n := by noncomm_ring
      _ = -(-a * genSig P A C) * qgtDefectDiff P A C n := by rw [h1]
      _ = a * (genSig P A C * qgtDefectDiff P A C n) := by noncomm_ring
  refine ⟨hInv, hV_ord, hSum_ord, hS_tw, hSig_tw, hDiff_tw, hProd_ord,
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold plabicWhiteShear; simp only [conePlus_neg]; peirce_nf hP
  · unfold plabicBlackShear; simp only [coneMinus_neg]; peirce_nf hP
  · unfold kleinGlideWhite plabicWhiteShear; peirce_nf hP
  · unfold kleinGlideBlack plabicBlackShear; peirce_nf hP
  · unfold kleinGlideWhite kleinGlideBlack plabicTripWB plabicWhiteShear plabicBlackShear
    simp only [conePlus_neg]
    peirce_nf hP

/-!
## 18. Archetype X₈: Operator-Ring Lift of Log-CFT Virasoro Jordan Cell & Monodromy (`Clifford.LogCftMonodromy`)

In any non-commutative ring `B`, an idempotent `P` and generators `A, C` define an
operator-valued Virasoro Jordan cell `opVirasoroL0Cell P A C := genV P A C + conePlus P A`
and operator logarithmic monodromy `opLogMonodromy P A C := genV P A C * plabicWhiteShear P A`.
Because `conePlus P A * conePlus P A = 0` and `comm (conePlus P A) (genV P A C) = 0`,
their powers truncate after the linear nilpotent term in any non-commutative ring `B`,
and specialize via `OperatorZornPeirceTetraktysBridge.peirceSheetProj` to
`Clifford.LogCftMonodromy.virasoroL0Cell` and `Clifford.LogCftMonodromy.hadjiivanovMonodromy`.
-/

omit [StarRing B] in
/-- **Operator-Valued Virasoro `L₀` Jordan Cell (`opVirasoroL0Cell`)**:
`L₀_op = V + N₊ = genV P A C + conePlus P A`. -/
def opVirasoroL0Cell (P A C : B) : B :=
  genV P A C + conePlus P A

omit [StarRing B] in
/-- **Operator-Valued Logarithmic Monodromy (`opLogMonodromy`)**:
`M_op = V * (1 + N₊) = genV P A C * plabicWhiteShear P A`. -/
def opLogMonodromy (P A C : B) : B :=
  genV P A C * plabicWhiteShear P A

omit [StarRing B] in
/-- **Theorem X₈.1 (`plabicWhiteShear_pow_and_opVirasoroL0Cell_binomial_pow`)**:
In any non-commutative ring `B` with idempotent `P` (`P * P = P`):
1. The unipotent horocycle shear `plabicWhiteShear P A = 1 + N₊` satisfies the exact
   winding power law `(plabicWhiteShear P A) ^ m = 1 + (m : ℤ) • conePlus P A` for all `m : ℕ`;
2. The operator Virasoro Jordan cell `opVirasoroL0Cell P A C = V + N₊` satisfies the
   truncated binomial power law
   `(opVirasoroL0Cell P A C) ^ (m + 1) = (genV P A C) ^ (m + 1) + ((m + 1 : ℕ) : ℤ) • ((genV P A C) ^ m * conePlus P A)`;
3. The operator logarithmic monodromy `opLogMonodromy P A C = V * (1 + N₊)` satisfies
   `(opLogMonodromy P A C) ^ m = (genV P A C) ^ m * (1 + (m : ℤ) • conePlus P A)`. -/
theorem plabicWhiteShear_pow_and_opVirasoroL0Cell_binomial_pow
    {P : B} (hP : P * P = P) (A C : B) (m : ℕ) :
    (plabicWhiteShear P A) ^ m = 1 + (m : ℤ) • conePlus P A ∧
    (opVirasoroL0Cell P A C) ^ (m + 1) =
      (genV P A C) ^ (m + 1) +
        ((m + 1 : ℕ) : ℤ) • ((genV P A C) ^ m * conePlus P A) ∧
    (opLogMonodromy P A C) ^ m =
      (genV P A C) ^ m * (1 + (m : ℤ) • conePlus P A) := by
  have hN2 : conePlus P A * conePlus P A = 0 := conePlus_mul_conePlus hP A A
  have hNV : conePlus P A * genV P A C = genV P A C * conePlus P A := by peirce_nf hP
  refine ⟨?_, ?_, ?_⟩
  · induction m with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ih]
        unfold plabicWhiteShear
        push_cast
        rw [add_smul, one_smul]
        calc
          (1 + (k : ℤ) • conePlus P A) * (1 + conePlus P A) =
              1 + ((k : ℤ) • conePlus P A + conePlus P A) +
                (k : ℤ) • (conePlus P A * conePlus P A) := by noncomm_ring
          _ = 1 + ((k : ℤ) • conePlus P A + conePlus P A) := by rw [hN2, smul_zero, add_zero]
  · induction m with
    | zero =>
        simp [opVirasoroL0Cell]
    | succ k ih =>
        rw [pow_succ (opVirasoroL0Cell P A C) (k + 1), ih]
        unfold opVirasoroL0Cell
        have hExpand :
            ((genV P A C) ^ (k + 1) + ((k + 1 : ℕ) : ℤ) • ((genV P A C) ^ k * conePlus P A)) *
              (genV P A C + conePlus P A) =
            (genV P A C) ^ (k + 1) * genV P A C +
              (genV P A C) ^ (k + 1) * conePlus P A +
              ((k + 1 : ℕ) : ℤ) • ((genV P A C) ^ k * (conePlus P A * genV P A C)) +
              ((k + 1 : ℕ) : ℤ) • ((genV P A C) ^ k * (conePlus P A * conePlus P A)) := by
          noncomm_ring
        rw [hExpand, hNV, hN2, mul_zero, smul_zero, add_zero,
            ← mul_assoc ((genV P A C) ^ k) (genV P A C) (conePlus P A),
            ← pow_succ (genV P A C) k, ← pow_succ (genV P A C) (k + 1)]
        simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
        abel
  · induction m with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ih]
        unfold opLogMonodromy plabicWhiteShear
        have hStep :
            (genV P A C) ^ k * (1 + (k : ℤ) • conePlus P A) *
              (genV P A C * (1 + conePlus P A)) =
            (genV P A C) ^ k * genV P A C * (1 + conePlus P A) +
              (k : ℤ) • ((genV P A C) ^ k * (conePlus P A * genV P A C)) +
              (k : ℤ) • ((genV P A C) ^ k * (conePlus P A * genV P A C) * conePlus P A) := by
          noncomm_ring
        rw [hStep, hNV, ← mul_assoc ((genV P A C) ^ k) (genV P A C) (conePlus P A),
            mul_assoc ((genV P A C) ^ k * genV P A C) (conePlus P A) (conePlus P A),
            hN2, mul_zero, smul_zero, add_zero, ← pow_succ (genV P A C) k]
        push_cast
        rw [add_smul, one_smul]
        noncomm_ring

omit [StarRing B] in
/-- **Theorem X₈.2 (`opVirasoroL0Cell_and_hadjiivanovMonodromy_matrix_carrier_bridge`)**:
Level-3 Cross-Lane Carrier Compatibility between the non-commutative Peirce spine
(`opVirasoroL0Cell`, `plabicWhiteShear`) and `Clifford.LogCftMonodromy`:
In `Matrix (Fin 2) (Fin 2) ℂ` equipped with the canonical upper-sheet Peirce idempotent
`P = OperatorZornPeirceTetraktysBridge.peirceSheetProj` (`!![1, 0; 0, 0]`):
1. `conePlus P !![0, 1; 0, 0] = LogCftMonodromy.jordanNilpotent`;
2. `genV P !![0, 1; 0, 0] !![0, 0; h, 0] = h • 1`;
3. `opVirasoroL0Cell P !![0, 1; 0, 0] !![0, 0; h, 0] = LogCftMonodromy.virasoroL0Cell h`;
4. `LogCftMonodromy.lcftPhase h • plabicWhiteShear P !![0, LogCftMonodromy.logShearBase; 0, 0] = LogCftMonodromy.hadjiivanovMonodromy h`. -/
theorem opVirasoroL0Cell_and_hadjiivanovMonodromy_matrix_carrier_bridge (h : ℂ) :
    let P : Matrix (Fin 2) (Fin 2) ℂ :=
      InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj
    let A₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
    let C_h : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; h, 0]
    let A_log : Matrix (Fin 2) (Fin 2) ℂ :=
      !![0, InfoGeometry.Clifford.LogCftMonodromy.logShearBase; 0, 0]
    conePlus P A₁ = InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent ∧
    genV P A₁ C_h = h • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    opVirasoroL0Cell P A₁ C_h = InfoGeometry.Clifford.LogCftMonodromy.virasoroL0Cell h ∧
    InfoGeometry.Clifford.LogCftMonodromy.lcftPhase h • plabicWhiteShear P A_log =
      InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy h := by
  dsimp only
  have hCP : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      conePlus
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℂ)) M =
      !![(0 : ℂ), M 0 1; 0, 0] := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conePlus,
        InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj,
        Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Fin.sum_univ_two]
  have hCM : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
      coneMinus
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℂ)) M =
      !![(0 : ℂ), 0; M 1 0, 0] := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coneMinus,
        InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hCone :
      conePlus
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℂ))
        !![(0 : ℂ), 1; 0, 0] =
      InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent := by
    rw [hCP]
    rfl
  have hV :
      genV
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℂ))
        !![(0 : ℂ), 1; 0, 0] !![(0 : ℂ), 0; h, 0] =
      h • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [genV, anticomm, hCP, hCM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨hCone, hV, ?_, ?_⟩
  · unfold opVirasoroL0Cell
    rw [hV, hCone, ← InfoGeometry.Clifford.LogCftMonodromy.l0_cell_decomposition]
  · rw [InfoGeometry.Clifford.LogCftMonodromy.hadjiivanovMonodromy_phase_nilpotent]
    congr 1
    unfold plabicWhiteShear
    rw [hCP]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Clifford.LogCftMonodromy.jordanNilpotent]

/-!
## 19. Archetype X₉: Universal `FibonacciGrothendieckRing` (`K₀(Fib)`) Representation on the Operator Penrose Spine

Connects `InfoGeometry.Algebra.FibonacciGrothendieckRing` (`FibonacciRingModel`, `FibonacciK0`,
`k0ToModel`, `k0Mul`, `tensorTauK0`) to the non-commutative Peirce Penrose Kite/Dart operators
(`penroseKiteOp`, `penroseDartOp`) in any associative ring `B`.
-/

omit [StarRing B] in
/-- **Operator-Ring Evaluation of `FibonacciRingModel` (`fibModelToPeirceOp`)**:
Maps `(a, b) ∈ ℤ × ℤ` (`a · 1 + b · τ`) to `a • 1 + b • penroseKiteOp P A C` in `B`. -/
def fibModelToPeirceOp (P A C : B)
    (x : InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciRingModel) : B :=
  x.1 • (1 : B) + x.2 • penroseKiteOp P A C

omit [StarRing B] in
/-- **Universal `K₀(Fib)` Evaluation in an Associative Operator Ring (`fibK0ToPeirceOp`)**:
Maps any Grothendieck class `z : FibonacciK0` to `B` via `k0ToModel`. -/
noncomputable def fibK0ToPeirceOp (P A C : B)
    (z : InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciK0) : B :=
  fibModelToPeirceOp P A C (InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel z)

omit [StarRing B] in
/-- **Theorem X₉.1 (`fibonacciK0_peirce_penrose_representation_bridge`)**:
In any non-commutative ring `B` with idempotent `P` (`P * P = P`):
1. `fibK0ToPeirceOp P A C` maps `fibOneK0` to `1`, `fibTauK0` to `penroseKiteOp P A C`,
   and is additive: `fibK0ToPeirceOp P A C (z₁ + z₂) = fibK0ToPeirceOp P A C z₁ + fibK0ToPeirceOp P A C z₂`;
2. **Exact Off-Shell Multiplication Defect Law (with zero shell assumptions):**
   For all `z₁, z₂ : FibonacciK0`,
   `fibK0ToPeirceOp P A C z₁ * fibK0ToPeirceOp P A C z₂ - fibK0ToPeirceOp P A C (k0Mul z₁ z₂) = ((k0ToModel z₁).2 * (k0ToModel z₂).2) • (penroseDartOp P A C - 1)`,
   and for `tensorTauK0`,
   `fibK0ToPeirceOp P A C z₁ * penroseKiteOp P A C - fibK0ToPeirceOp P A C (tensorTauK0 z₁) = (k0ToModel z₁).2 • (penroseDartOp P A C - 1)`;
3. **Golden/Penrose Shell Multiplicative Homomorphism (`genV P A C = 1`):**
   Whenever `genV P A C = 1`, `fibK0ToPeirceOp P A C (k0Mul z₁ z₂) = fibK0ToPeirceOp P A C z₁ * fibK0ToPeirceOp P A C z₂`
   and `fibK0ToPeirceOp P A C (tensorTauK0 z₁) = fibK0ToPeirceOp P A C z₁ * penroseKiteOp P A C`;
4. **Ring-Homomorphism Naturality:**
   For any ring homomorphism `f : B →+* D`, `f (fibK0ToPeirceOp P A C z₁) = fibK0ToPeirceOp (f P) (f A) (f C) z₁`. -/
theorem fibonacciK0_peirce_penrose_representation_bridge
    {D : Type*} [Ring D] (f : B →+* D)
    {P : B} (hP : P * P = P) (A C : B)
    (z₁ z₂ : InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciK0) :
    let k0ToModel := InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel
    let fibOneK0 := InfoGeometry.Algebra.FibonacciGrothendieckRing.fibOneK0
    let fibTauK0 := InfoGeometry.Algebra.FibonacciGrothendieckRing.fibTauK0
    let k0Mul := InfoGeometry.Algebra.FibonacciGrothendieckRing.k0Mul
    let tensorTauK0 := InfoGeometry.Algebra.FibonacciGrothendieckRing.tensorTauK0
    fibK0ToPeirceOp P A C fibOneK0 = 1 ∧
    fibK0ToPeirceOp P A C fibTauK0 = penroseKiteOp P A C ∧
    fibK0ToPeirceOp P A C (z₁ + z₂) =
      fibK0ToPeirceOp P A C z₁ + fibK0ToPeirceOp P A C z₂ ∧
    fibK0ToPeirceOp P A C z₁ * fibK0ToPeirceOp P A C z₂ -
        fibK0ToPeirceOp P A C (k0Mul z₁ z₂) =
      ((k0ToModel z₁).2 * (k0ToModel z₂).2) • (penroseDartOp P A C - 1) ∧
    fibK0ToPeirceOp P A C z₁ * penroseKiteOp P A C -
        fibK0ToPeirceOp P A C (tensorTauK0 z₁) =
      (k0ToModel z₁).2 • (penroseDartOp P A C - 1) ∧
    (genV P A C = 1 →
      fibK0ToPeirceOp P A C (k0Mul z₁ z₂) =
        fibK0ToPeirceOp P A C z₁ * fibK0ToPeirceOp P A C z₂ ∧
      fibK0ToPeirceOp P A C (tensorTauK0 z₁) =
        fibK0ToPeirceOp P A C z₁ * penroseKiteOp P A C) ∧
    f (fibK0ToPeirceOp P A C z₁) = fibK0ToPeirceOp (f P) (f A) (f C) z₁ := by
  dsimp only
  have hKiteSq :
      penroseKiteOp P A C * penroseKiteOp P A C =
        penroseKiteOp P A C + penroseDartOp P A C := by
    unfold penroseKiteOp penroseDartOp peirceTransfer
    peirce_nf hP
  have hLinearMul : ∀ (a₁ b₁ a₂ b₂ : ℤ),
      (a₁ • (1 : B) + b₁ • penroseKiteOp P A C) *
        (a₂ • (1 : B) + b₂ • penroseKiteOp P A C) -
        ((a₁ * a₂ + b₁ * b₂) • (1 : B) +
          (a₁ * b₂ + b₁ * a₂ + b₁ * b₂) • penroseKiteOp P A C) =
      (b₁ * b₂) • (penroseDartOp P A C - 1) := by
    intro a₁ b₁ a₂ b₂
    let T := penroseKiteOp P A C
    calc
      (a₁ • (1 : B) + b₁ • T) * (a₂ • (1 : B) + b₂ • T) -
          ((a₁ * a₂ + b₁ * b₂) • (1 : B) + (a₁ * b₂ + b₁ * a₂ + b₁ * b₂) • T) =
        (a₁ • (1 : B)) * (a₂ • (1 : B)) + (a₁ • (1 : B)) * (b₂ • T) +
          (b₁ • T) * (a₂ • (1 : B)) + (b₁ • T) * (b₂ • T) -
          ((a₁ * a₂ + b₁ * b₂) • (1 : B) + (a₁ * b₂ + b₁ * a₂ + b₁ * b₂) • T) := by
        simp only [mul_add, add_mul]
        abel
      _ = (a₁ * a₂) • (1 : B) + (a₁ * b₂) • T + (b₁ * a₂) • T + (b₁ * b₂) • (T * T) -
          ((a₁ * a₂) • (1 : B) + (b₁ * b₂) • (1 : B) +
            ((a₁ * b₂) • T + (b₁ * a₂) • T + (b₁ * b₂) • T)) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, add_smul,
          mul_comm a₂ a₁, mul_comm b₂ a₁, mul_comm a₂ b₁, mul_comm b₂ b₁]
      _ = (b₁ * b₂) • (T * T) - (b₁ * b₂) • T - (b₁ * b₂) • (1 : B) := by
        abel
      _ = (b₁ * b₂) • (T * T - T - 1) := by
        rw [← smul_sub, ← smul_sub]
      _ = (b₁ * b₂) • (penroseDartOp P A C - 1) := by
        dsimp [T]
        rw [hKiteSq, add_sub_cancel_left]
  have hMulDefect :
      fibK0ToPeirceOp P A C z₁ * fibK0ToPeirceOp P A C z₂ -
        fibK0ToPeirceOp P A C (InfoGeometry.Algebra.FibonacciGrothendieckRing.k0Mul z₁ z₂) =
      ((InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel z₁).2 *
        (InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel z₂).2) •
        (penroseDartOp P A C - 1) := by
    unfold fibK0ToPeirceOp fibModelToPeirceOp
    rw [InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel_k0Mul]
    exact hLinearMul _ _ _ _
  have hTauDefect :
      fibK0ToPeirceOp P A C z₁ * penroseKiteOp P A C -
        fibK0ToPeirceOp P A C (InfoGeometry.Algebra.FibonacciGrothendieckRing.tensorTauK0 z₁) =
      (InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel z₁).2 •
        (penroseDartOp P A C - 1) := by
    rw [InfoGeometry.Algebra.FibonacciGrothendieckRing.tensorTauK0_eq_k0Mul_tau]
    have hTauOp :
        fibK0ToPeirceOp P A C InfoGeometry.Algebra.FibonacciGrothendieckRing.fibTauK0 =
          penroseKiteOp P A C := by
      unfold fibK0ToPeirceOp fibModelToPeirceOp
      rw [InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel_tau]
      simp [InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciRingModel.tau]
    rw [← hTauOp]
    have hSpec :
        fibK0ToPeirceOp P A C z₁ *
            fibK0ToPeirceOp P A C InfoGeometry.Algebra.FibonacciGrothendieckRing.fibTauK0 -
          fibK0ToPeirceOp P A C
            (InfoGeometry.Algebra.FibonacciGrothendieckRing.k0Mul z₁
              InfoGeometry.Algebra.FibonacciGrothendieckRing.fibTauK0) =
        ((InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel z₁).2 *
          (InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel
            InfoGeometry.Algebra.FibonacciGrothendieckRing.fibTauK0).2) •
          (penroseDartOp P A C - 1) := by
      unfold fibK0ToPeirceOp fibModelToPeirceOp
      rw [InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel_k0Mul]
      exact hLinearMul _ _ _ _
    rw [hSpec, InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel_tau]
    simp [InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciRingModel.tau]
  refine ⟨?_, ?_, ?_, hMulDefect, hTauDefect, ?_, ?_⟩
  · unfold fibK0ToPeirceOp fibModelToPeirceOp
    rw [InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel_one]
    simp [InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciRingModel.one]
  · unfold fibK0ToPeirceOp fibModelToPeirceOp
    rw [InfoGeometry.Algebra.FibonacciGrothendieckRing.k0ToModel_tau]
    simp [InfoGeometry.Algebra.FibonacciGrothendieckRing.FibonacciRingModel.tau]
  · unfold fibK0ToPeirceOp fibModelToPeirceOp
    rw [map_add]
    dsimp
    rw [add_smul, add_smul]
    abel
  · intro hV1
    have hDart1 : penroseDartOp P A C - 1 = 0 := by
      unfold penroseDartOp
      rw [hV1, sub_self]
    refine ⟨?_, ?_⟩
    · apply eq_of_sub_eq_zero
      rw [← neg_sub, hMulDefect, hDart1, smul_zero, neg_zero]
    · apply eq_of_sub_eq_zero
      rw [← neg_sub, hTauDefect, hDart1, smul_zero, neg_zero]
  · unfold fibK0ToPeirceOp fibModelToPeirceOp
    have hKiteMap : f (penroseKiteOp P A C) = penroseKiteOp (f P) (f A) (f C) := by
      unfold penroseKiteOp peirceTransfer
      rw [map_add, map_genPhi]
    rw [map_add, map_zsmul, map_zsmul, map_one, hKiteMap]

/-!
## 20. Archetype X₁₀: The Clifford–Exterior–Interior Tetraktys Calculus & Paracomplex/Hypercomplex Cayley–Dickson Boost Doubling

Unifies the two ways the 4-element Peirce Tetraktys `(genV, genPhi, genJ, genSig)` is generated
in an arbitrary associative ring `B` with idempotent `P` (`P * P = P`):
1. **Interior (Jordan) + Exterior (Lie/Wedge) Decomposition of the Null Corner Pair `(N₊, N₋)`:**
   `V = {N₊, N₋}` (interior contraction, Grade 0) and `Σ = [N₊, N₋]` (exterior bivector, Grade 2);
2. **Orthogonal Clifford Grade-1 Vectors `(Φ, J)` (`Φ² = +V`, `J² = -V`, `{Φ, J} = 0`):**
   Because `{Φ, J} = 0`, their Clifford product coincides with their exterior product:
   `J * Φ = -Φ * J = Σ = invS P * V = V * invS P`;
3. **Paracomplex Boost Doubling (`γ = +1`, `SplitComplex.Carrier`) vs. Elliptic Hypercomplex Doubling (`γ = -1`):**
   Evaluates `SplitComplex.Carrier ℤ` into `B` along both `invS P` (exact lightcone zero-divisor
   homomorphism) and `genPhi P A C` (off-shell boost doubling defect and hyperbolic norm
   `a² • 1 - b² • V`, contrasted with the elliptic hypercomplex norm `a² • 1 + b² • V` along `genJ P A C`),
   and proves the Level-3 carrier bridge to `InfoGeometry.Projective.SplitQuaternionMatrix`.
-/

omit [StarRing B] in
/-- **Paracomplex Lightcone Grading Evaluator (`splitComplexToInvSOp`)**:
Evaluates `z = ⟨re, im⟩ : SplitComplex.Carrier ℤ` at the Peirce boost grading `invS P = 2P - 1`:
`z.re • 1 + z.im • invS P`. -/
def splitComplexToInvSOp (P : B) (z : InfoGeometry.Canonical.SplitComplex.Carrier ℤ) : B :=
  z.re • (1 : B) + z.im • invS P

omit [StarRing B] in
/-- **Paracomplex Boost Cayley–Dickson Evaluator (`splitComplexToBoostOp`)**:
Evaluates `z = ⟨re, im⟩ : SplitComplex.Carrier ℤ` at the Peirce Grade-1 boost generator `genPhi P A C`:
`z.re • 1 + z.im • genPhi P A C` (`Φ² = +V`). -/
def splitComplexToBoostOp (P A C : B) (z : InfoGeometry.Canonical.SplitComplex.Carrier ℤ) : B :=
  z.re • (1 : B) + z.im • genPhi P A C

omit [StarRing B] in
/-- **Elliptic Hypercomplex Cayley–Dickson Evaluator (`hypercomplexToRotOp`)**:
Evaluates `(a, b) : ℤ × ℤ` at the Peirce Grade-1 hypercomplex generator `genJ P A C`:
`a • 1 + b • genJ P A C` (`J² = -V`). -/
def hypercomplexToRotOp (P A C : B) (a b : ℤ) : B :=
  a • (1 : B) + b • genJ P A C

omit [StarRing B] in
/-- **Theorem X₁₀.1 (`tetraktys_clifford_interior_exterior_and_cayley_dickson_boost_bridge`)**:
In any non-commutative ring `B` with idempotent `P` (`P * P = P`) and arbitrary `A, C, X, Y : B`:
1. **Clifford Product = Interior (Jordan) + Exterior (Lie/Wedge) Decomposition:**
   `(2 : ℤ) • (X * Y) = anticomm X Y + comm X Y` and `(2 : ℤ) • (Y * X) = anticomm X Y - comm X Y`;
2. **Null Witt Corners `(N₊, N₋)` to 3rd (`V`) & 4th (`Σ`) Tetraktys Levels:**
   `anticomm (conePlus P A) (coneMinus P C) = genV P A C`,
   `comm (conePlus P A) (coneMinus P C) = genSig P A C`,
   `genV P A C + genSig P A C = (2 : ℤ) • (conePlus P A * coneMinus P C)`, and
   `genV P A C - genSig P A C = (2 : ℤ) • (coneMinus P C * conePlus P A)`;
3. **Orthogonal Clifford Grade-1 Vectors `(Φ, J)` Create `V` (Interior Square) and `Σ` (Clifford = Exterior Product):**
   `genPhi P A C * genPhi P A C = genV P A C`,
   `genJ P A C * genJ P A C = -genV P A C`,
   `anticomm (genPhi P A C) (genJ P A C) = 0`,
   `genJ P A C * genPhi P A C = genSig P A C`,
   `genPhi P A C * genJ P A C = -genSig P A C`,
   `comm (genJ P A C) (genPhi P A C) = (2 : ℤ) • genSig P A C`, and
   `genSig P A C = invS P * genV P A C`;
4. **Complete 4-Fold Tetraktys Graded Clifford Multiplication Table:**
   `genPhi P A C * genSig P A C = -genV P A C * genJ P A C`,
   `genSig P A C * genPhi P A C = genV P A C * genJ P A C`,
   `genJ P A C * genSig P A C = -genV P A C * genPhi P A C`,
   `genSig P A C * genJ P A C = genV P A C * genPhi P A C`, and
   `genSig P A C * genSig P A C = genV P A C * genV P A C`;
5. **Paracomplex Boost (`γ = +1`) vs. Elliptic Hypercomplex (`γ = -1`) Cayley–Dickson Doubling Laws:**
   - `splitComplexToInvSOp P (z₁ * z₂) = splitComplexToInvSOp P z₁ * splitComplexToInvSOp P z₂`,
     `splitComplexToInvSOp P (1 + Carrier.eps) = (2 : ℤ) • P`, and
     `splitComplexToInvSOp P (1 - Carrier.eps) = (2 : ℤ) • (1 - P)`,
   - `splitComplexToBoostOp P A C z₁ * splitComplexToBoostOp P A C z₂ - splitComplexToBoostOp P A C (z₁ * z₂) = (z₁.im * z₂.im) • (genV P A C - 1)`,
   - **Hyperbolic Boost Norm vs. Elliptic Hypercomplex Norm:**
     `splitComplexToBoostOp P A C ⟨a, b⟩ * splitComplexToBoostOp P A C ⟨a, -b⟩ = (a * a) • 1 - (b * b) • genV P A C` and
     `hypercomplexToRotOp P A C a b * hypercomplexToRotOp P A C a (-b) = (a * a) • 1 + (b * b) • genV P A C`. -/
theorem tetraktys_clifford_interior_exterior_and_cayley_dickson_boost_bridge
    {P : B} (hP : P * P = P) (A C X Y : B)
    (z₁ z₂ : InfoGeometry.Canonical.SplitComplex.Carrier ℤ) (a b : ℤ) :
    let eps := InfoGeometry.Canonical.SplitComplex.Carrier.eps (R := ℤ)
    ((2 : ℤ) • (X * Y) = anticomm X Y + comm X Y ∧
     (2 : ℤ) • (Y * X) = anticomm X Y - comm X Y) ∧
    (anticomm (conePlus P A) (coneMinus P C) = genV P A C ∧
     comm (conePlus P A) (coneMinus P C) = genSig P A C ∧
     genV P A C + genSig P A C = (2 : ℤ) • (conePlus P A * coneMinus P C) ∧
     genV P A C - genSig P A C = (2 : ℤ) • (coneMinus P C * conePlus P A)) ∧
    (genPhi P A C * genPhi P A C = genV P A C ∧
     genJ P A C * genJ P A C = -genV P A C ∧
     anticomm (genPhi P A C) (genJ P A C) = 0 ∧
     genJ P A C * genPhi P A C = genSig P A C ∧
     genPhi P A C * genJ P A C = -genSig P A C ∧
     comm (genJ P A C) (genPhi P A C) = (2 : ℤ) • genSig P A C ∧
     genSig P A C = invS P * genV P A C) ∧
    (genPhi P A C * genSig P A C = -genV P A C * genJ P A C ∧
     genSig P A C * genPhi P A C = genV P A C * genJ P A C ∧
     genJ P A C * genSig P A C = -genV P A C * genPhi P A C ∧
     genSig P A C * genJ P A C = genV P A C * genPhi P A C ∧
     genSig P A C * genSig P A C = genV P A C * genV P A C) ∧
    (splitComplexToInvSOp P (z₁ * z₂) =
       splitComplexToInvSOp P z₁ * splitComplexToInvSOp P z₂ ∧
     splitComplexToInvSOp P (1 + eps) = (2 : ℤ) • P ∧
     splitComplexToInvSOp P (1 - eps) = (2 : ℤ) • (1 - P) ∧
     splitComplexToBoostOp P A C z₁ * splitComplexToBoostOp P A C z₂ -
         splitComplexToBoostOp P A C (z₁ * z₂) =
       (z₁.im * z₂.im) • (genV P A C - 1) ∧
     splitComplexToBoostOp P A C ⟨a, b⟩ * splitComplexToBoostOp P A C ⟨a, -b⟩ =
       (a * a) • (1 : B) - (b * b) • genV P A C ∧
     hypercomplexToRotOp P A C a b * hypercomplexToRotOp P A C a (-b) =
       (a * a) • (1 : B) + (b * b) • genV P A C) := by
  dsimp only
  refine ⟨⟨?_, ?_⟩, ⟨rfl, rfl, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold anticomm comm; noncomm_ring
  · unfold anticomm comm; noncomm_ring
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · unfold anticomm; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · unfold comm; peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP
  · unfold splitComplexToInvSOp
    simp only [InfoGeometry.Canonical.SplitComplex.Carrier.mul_re,
      InfoGeometry.Canonical.SplitComplex.Carrier.mul_im]
    have hS2 : invS P * invS P = 1 := by
      unfold invS; noncomm_ring [hP]
    calc
      (z₁.re * z₂.re + z₁.im * z₂.im) • (1 : B) +
          (z₁.re * z₂.im + z₁.im * z₂.re) • invS P =
        (z₁.re * z₂.re) • (1 : B) + (z₁.re * z₂.im) • invS P +
          (z₁.im * z₂.re) • invS P + (z₁.im * z₂.im) • (invS P * invS P) := by
        rw [hS2, add_smul, add_smul]
        abel
      _ = (z₁.re • (1 : B)) * (z₂.re • (1 : B)) +
          (z₁.re • (1 : B)) * (z₂.im • invS P) +
          (z₁.im • invS P) * (z₂.re • (1 : B)) +
          (z₁.im • invS P) * (z₂.im • invS P) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
          mul_comm z₂.re z₁.re, mul_comm z₂.im z₁.re,
          mul_comm z₂.re z₁.im, mul_comm z₂.im z₁.im]
      _ = (z₁.re • (1 : B) + z₁.im • invS P) *
          (z₂.re • (1 : B) + z₂.im • invS P) := by
        simp only [mul_add, add_mul]
        abel
  · unfold splitComplexToInvSOp invS
    simp only [InfoGeometry.Canonical.SplitComplex.Carrier.add_re,
      InfoGeometry.Canonical.SplitComplex.Carrier.add_im,
      InfoGeometry.Canonical.SplitComplex.Carrier.one_re,
      InfoGeometry.Canonical.SplitComplex.Carrier.one_im,
      InfoGeometry.Canonical.SplitComplex.Carrier.eps_re,
      InfoGeometry.Canonical.SplitComplex.Carrier.eps_im,
      add_zero, zero_add, one_smul]
    noncomm_ring
  · unfold splitComplexToInvSOp invS
    simp only [InfoGeometry.Canonical.SplitComplex.Carrier.sub_re,
      InfoGeometry.Canonical.SplitComplex.Carrier.sub_im,
      InfoGeometry.Canonical.SplitComplex.Carrier.one_re,
      InfoGeometry.Canonical.SplitComplex.Carrier.one_im,
      InfoGeometry.Canonical.SplitComplex.Carrier.eps_re,
      InfoGeometry.Canonical.SplitComplex.Carrier.eps_im,
      sub_zero, zero_sub, one_smul, neg_smul]
    noncomm_ring
  · unfold splitComplexToBoostOp
    simp only [InfoGeometry.Canonical.SplitComplex.Carrier.mul_re,
      InfoGeometry.Canonical.SplitComplex.Carrier.mul_im]
    have hPhi2 : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
    let Φ := genPhi P A C
    calc
      (z₁.re • (1 : B) + z₁.im • Φ) * (z₂.re • (1 : B) + z₂.im • Φ) -
          ((z₁.re * z₂.re + z₁.im * z₂.im) • (1 : B) +
            (z₁.re * z₂.im + z₁.im * z₂.re) • Φ) =
        (z₁.re • (1 : B)) * (z₂.re • (1 : B)) +
          (z₁.re • (1 : B)) * (z₂.im • Φ) +
          (z₁.im • Φ) * (z₂.re • (1 : B)) +
          (z₁.im • Φ) * (z₂.im • Φ) -
          ((z₁.re * z₂.re + z₁.im * z₂.im) • (1 : B) +
            (z₁.re * z₂.im + z₁.im * z₂.re) • Φ) := by
        simp only [mul_add, add_mul]
        abel
      _ = (z₁.re * z₂.re) • (1 : B) + (z₁.re * z₂.im) • Φ +
          (z₁.im * z₂.re) • Φ + (z₁.im * z₂.im) • (Φ * Φ) -
          ((z₁.re * z₂.re) • (1 : B) + (z₁.im * z₂.im) • (1 : B) +
            ((z₁.re * z₂.im) • Φ + (z₁.im * z₂.re) • Φ)) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, add_smul,
          mul_comm z₂.re z₁.re, mul_comm z₂.im z₁.re,
          mul_comm z₂.re z₁.im, mul_comm z₂.im z₁.im]
      _ = (z₁.im * z₂.im) • (Φ * Φ) - (z₁.im * z₂.im) • (1 : B) := by
        abel
      _ = (z₁.im * z₂.im) • (genV P A C - 1) := by
        dsimp [Φ]
        rw [hPhi2, ← smul_sub]
  · unfold splitComplexToBoostOp
    dsimp only
    have hPhi2 : genPhi P A C * genPhi P A C = genV P A C := by peirce_nf hP
    let Φ := genPhi P A C
    calc
      (a • (1 : B) + b • Φ) * (a • (1 : B) + (-b) • Φ) =
        (a • (1 : B)) * (a • (1 : B)) + (a • (1 : B)) * ((-b) • Φ) +
          (b • Φ) * (a • (1 : B)) + (b • Φ) * ((-b) • Φ) := by
        simp only [mul_add, add_mul]
        abel
      _ = (a * a) • (1 : B) - (b * a) • Φ + (a * b) • Φ - (b * b) • (Φ * Φ) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
          mul_neg, neg_smul, sub_eq_add_neg]
      _ = (a * a) • (1 : B) - (b * b) • genV P A C := by
        dsimp [Φ]
        rw [mul_comm a b, hPhi2]
        abel
  · unfold hypercomplexToRotOp
    have hJ2 : genJ P A C * genJ P A C = -genV P A C := by peirce_nf hP
    let J := genJ P A C
    calc
      (a • (1 : B) + b • J) * (a • (1 : B) + (-b) • J) =
        (a • (1 : B)) * (a • (1 : B)) + (a • (1 : B)) * ((-b) • J) +
          (b • J) * (a • (1 : B)) + (b • J) * ((-b) • J) := by
        simp only [mul_add, add_mul]
        abel
      _ = (a * a) • (1 : B) - (b * a) • J + (a * b) • J - (b * b) • (J * J) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one,
          mul_neg, neg_smul, sub_eq_add_neg]
      _ = (a * a) • (1 : B) + (b * b) • genV P A C := by
        dsimp [J]
        rw [mul_comm a b, hJ2, smul_neg, sub_neg_eq_add]
        abel

omit [StarRing B] in
/-- **Theorem X₁₀.2 (`tetraktys_splitQuaternionMatrix_carrier_bridge`)**:
Level-3 Cross-Lane Carrier Compatibility between the Peirce Tetraktys
(`genV`, `genJ`, `genPhi`, `genSig`, `invS`) and `InfoGeometry.Projective.SplitQuaternionMatrix`
(`mat_1`, `mat_i`, `mat_j`, `mat_k`, `splitQuaternionToMatrix`, `splitNormSq`):
In `Matrix (Fin 2) (Fin 2) ℝ` with `P = peirceSheetProj = !![1, 0; 0, 0]`,
`A₁ = !![0, 1; 0, 0]`, `C₁ = !![0, 0; 1, 0]`:
1. `genV P A₁ C₁ = InfoGeometry.Projective.mat_1` (Grade-0 Interior Scale `V = 1`);
2. `genJ P A₁ C₁ = InfoGeometry.Projective.mat_i` (Grade-1 Hypercomplex generator `J = i`, `i² = -1`);
3. `genPhi P A₁ C₁ = InfoGeometry.Projective.mat_j` (Grade-1 Paracomplex Boost generator `Φ = j`, `j² = +1`);
4. `genSig P A₁ C₁ = InfoGeometry.Projective.mat_k` and `invS P = InfoGeometry.Projective.mat_k`
   (Grade-2 Exterior Bivector / Clifford Product `Σ = J * Φ = k = i * j`, `k² = +1`);
5. For all `(w, x, y, z : ℝ)`,
   `InfoGeometry.Projective.splitQuaternionToMatrix w x y z = w • genV P A₁ C₁ + x • genJ P A₁ C₁ + y • genPhi P A₁ C₁ + z • genSig P A₁ C₁`,
   and its determinant equals the `(2, 2)` split-quaternion norm
   `(w • genV P A₁ C₁ + x • genJ P A₁ C₁ + y • genPhi P A₁ C₁ + z • genSig P A₁ C₁).det = InfoGeometry.Projective.splitNormSq w x y z`. -/
theorem tetraktys_splitQuaternionMatrix_carrier_bridge (w x y z : ℝ) :
    let P : Matrix (Fin 2) (Fin 2) ℝ :=
      InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj
    let A₁ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let C₁ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    genV P A₁ C₁ = InfoGeometry.Projective.mat_1 ∧
    genJ P A₁ C₁ = InfoGeometry.Projective.mat_i ∧
    genPhi P A₁ C₁ = InfoGeometry.Projective.mat_j ∧
    genSig P A₁ C₁ = InfoGeometry.Projective.mat_k ∧
    invS P = InfoGeometry.Projective.mat_k ∧
    InfoGeometry.Projective.splitQuaternionToMatrix w x y z =
      w • genV P A₁ C₁ + x • genJ P A₁ C₁ + y • genPhi P A₁ C₁ + z • genSig P A₁ C₁ ∧
    (w • genV P A₁ C₁ + x • genJ P A₁ C₁ + y • genPhi P A₁ C₁ + z • genSig P A₁ C₁).det =
      InfoGeometry.Projective.splitNormSq w x y z := by
  dsimp only
  have hCP : ∀ M : Matrix (Fin 2) (Fin 2) ℝ,
      conePlus
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ)) M =
      !![(0 : ℝ), M 0 1; 0, 0] := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conePlus,
        InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj,
        Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Fin.sum_univ_two]
  have hCM : ∀ M : Matrix (Fin 2) (Fin 2) ℝ,
      coneMinus
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ)) M =
      !![(0 : ℝ), 0; M 1 0, 0] := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coneMinus,
        InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj,
        Matrix.mul_apply, Fin.sum_univ_two]
  have hV :
      genV
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ))
        !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] =
      InfoGeometry.Projective.mat_1 := by
    rw [genV, anticomm, hCP, hCM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Projective.mat_1]
  have hJ :
      genJ
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ))
        !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] =
      InfoGeometry.Projective.mat_i := by
    rw [genJ, hCP, hCM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Projective.mat_i]
  have hPhi :
      genPhi
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ))
        !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] =
      InfoGeometry.Projective.mat_j := by
    rw [genPhi, hCP, hCM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Projective.mat_j]
  have hSig :
      genSig
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ))
        !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] =
      InfoGeometry.Projective.mat_k := by
    rw [genSig, comm, hCP, hCM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Projective.mat_k]
  have hS :
      invS
        (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ)) =
      InfoGeometry.Projective.mat_k := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [invS,
        InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj,
        InfoGeometry.Projective.mat_k]
  have hCombo :
      InfoGeometry.Projective.splitQuaternionToMatrix w x y z =
        w • genV
          (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ))
          !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] +
        x • genJ
          (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ))
          !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] +
        y • genPhi
          (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ))
          !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] +
        z • genSig
          (InfoGeometry.OperatorAlgebra.OperatorZornPeirceTetraktysBridge.peirceSheetProj (A := ℝ))
          !![(0 : ℝ), 1; 0, 0] !![(0 : ℝ), 0; 1, 0] := by
    rw [hV, hJ, hPhi, hSig]
    rfl
  refine ⟨hV, hJ, hPhi, hSig, hS, hCombo, ?_⟩
  rw [← hCombo]
  exact InfoGeometry.Projective.det_splitQuaternionToMatrix w x y z

/-!
## 21. Archetype X₁₁: Kantor Triple Product, 5-Graded Anomaly Generators, Zorn Associator Grade Flip, & Operator Cyclotomic Characteristic Polynomials

Formalizes:
1. **Kantor Triple Product (`opKantorTriple`) & Kantor Skew Anomaly (`opKantorAnomaly`)** on the
   Peirce Spine, proving the Kantor 5-grade adjoint cubic law `ad_S³ - 4 • ad_S = 0` (`S = invS P`),
   the decomposition of the BdG interaction anomaly `[evenGrade P D, genJ P A C]` into pure
   Grade `+2` (`bdgUpperAnomaly`) and Grade `-2` (`bdgLowerAnomaly`) generators, and the Kantor
   skew-anomaly generation of `genSig P A C` and `-genV P A C`;
2. **Exact Operator Cyclotomic Characteristic Polynomials (Cayley–Hamilton Identities over `ℤ[V]`):**
   Proves that `peirceTransferJ` (`W = P + J`), `peirceTransferJComplement` (`W̄ = (1-P) - J`),
   `cubeRootOp` (`ω = -(P + J)`), `cubeRootOpConj` (`ω̄ = -(1-P) + J`), and `peirceTransfer`
   (`T = 1 + Φ`), `peirceTransferComplement` (`T̄ = 1 - Φ`) satisfy exact zero-shell operator
   characteristic equations `W² - W + V = 0`, `ω² + ω + V = 0`, and `T² - 2•T + (1 - V) = 0`;
3. **Non-Associative Zorn Associator Grade-Flip Anomaly (`zorn_associator_grade_anomaly_bridge`):**
   Proves that in `OperatorZornMatrix B`, the associator `associator X (pureNPlus a) Y` vanishes
   on `n_plus`, `n_minus`, and `sigma_plus` and generates purely the opposite-grade chiral vector
   `sigma_minus i = -zornCross X.sigma_plus (fun j => a * Y.sigma_plus j) i`, while
   `associator X (pureNMinus b) Y` generates purely `sigma_plus i = zornCross X.sigma_minus (fun j => b * Y.sigma_minus j) i`.
-/

omit [StarRing B] in
/-- **Operator Kantor–Jordan Triple Product (`opKantorTriple`)**:
`{X, Y, Z}_K = X * Y * Z + Z * Y * X` in an associative ring `B`. -/
def opKantorTriple (X Y Z : B) : B :=
  X * Y * Z + Z * Y * X

omit [StarRing B] in
/-- **Operator Kantor Skew Anomaly (`opKantorAnomaly`)**:
`K(X, Y)(Z) = X * Z * Y - Y * Z * X`, measuring outer-asymmetry of the associative triple product. -/
def opKantorAnomaly (X Y Z : B) : B :=
  X * Z * Y - Y * Z * X

omit [StarRing B] in
/-- **Upper Grade-`+2` BdG / Chiral Interaction Anomaly Generator (`bdgUpperAnomaly`)**:
`P * D * P * conePlus P A - conePlus P A * (1 - P) * D * (1 - P)`. -/
def bdgUpperAnomaly (P D A : B) : B :=
  P * D * P * conePlus P A - conePlus P A * (1 - P) * D * (1 - P)

omit [StarRing B] in
/-- **Lower Grade-`-2` BdG / Chiral Interaction Anomaly Generator (`bdgLowerAnomaly`)**:
`coneMinus P C * P * D * P - (1 - P) * D * (1 - P) * coneMinus P C`. -/
def bdgLowerAnomaly (P D C : B) : B :=
  coneMinus P C * P * D * P - (1 - P) * D * (1 - P) * coneMinus P C

omit [StarRing B] in
/-- **`Φ₆`-Deformed Operator Characteristic Polynomial (`opCharPolyPhi6`)**:
`X² - X + genV P A C`. -/
def opCharPolyPhi6 (P A C X : B) : B :=
  X * X - X + genV P A C

omit [StarRing B] in
/-- **`Φ₃`-Deformed Operator Characteristic Polynomial (`opCharPolyPhi3`)**:
`X² + X + genV P A C`. -/
def opCharPolyPhi3 (P A C X : B) : B :=
  X * X + X + genV P A C

omit [StarRing B] in
/-- **Golden / Transfer Operator Characteristic Polynomial (`opCharPolyTransfer`)**:
`X² - X - genV P A C` (the `V`-deformed Golden polynomial satisfied by both `peirceTransfer` and `peirceTransferComplement`). -/
def opCharPolyTransfer (P A C X : B) : B :=
  X * X - X - genV P A C

omit [StarRing B] in
/-- **Theorem X₁₁.1 (`kantor_triple_five_grade_anomalies_and_operator_cyclotomic_charpoly_bridge`)**:
In any non-commutative ring `B` with idempotent `P` (`P * P = P`) and arbitrary `A, C, D, X : B`:
1. **Kantor 5-Grade Adjoint Eigenvalues & Cubic Characteristic Law (`S = invS P`):**
   `comm S (conePlus P A) = (2 : ℤ) • conePlus P A`,
   `comm S (coneMinus P C) = -(2 : ℤ) • coneMinus P C`,
   `comm S (evenGrade P D) = 0`, `comm S (genV P A C) = 0`, `comm S (genSig P A C) = 0`, and
   `comm S (comm S (comm S X)) - (4 : ℤ) • comm S X = 0`;
2. **BdG Interaction Anomaly Decomposition into Grade `+2` and Grade `-2` Generators:**
   `comm (evenGrade P D) (genJ P A C) = bdgUpperAnomaly P D A + bdgLowerAnomaly P D C`,
   `comm (evenGrade P D) (genPhi P A C) = bdgUpperAnomaly P D A - bdgLowerAnomaly P D C`,
   `comm S (bdgUpperAnomaly P D A) = (2 : ℤ) • bdgUpperAnomaly P D A`, and
   `comm S (bdgLowerAnomaly P D C) = -(2 : ℤ) • bdgLowerAnomaly P D C`;
3. **Kantor Triple Product & Kantor Skew Anomaly on Peirce Corners:**
   `opKantorTriple (conePlus P A) (coneMinus P C) (conePlus P A) = (2 : ℤ) • (genV P A C * conePlus P A)`,
   `opKantorTriple (coneMinus P C) (conePlus P A) (coneMinus P C) = (2 : ℤ) • (genV P A C * coneMinus P C)`,
   `opKantorAnomaly (conePlus P A) (coneMinus P C) 1 = genSig P A C`, and
   `opKantorAnomaly (conePlus P A) (coneMinus P C) (invS P) = -genV P A C`;
4. **Exact Zero-Shell Operator Cyclotomic Characteristic Polynomials over `ℤ[V]`:**
   `opCharPolyPhi6 P A C (peirceTransferJ P A C) = 0`,
   `opCharPolyPhi6 P A C (peirceTransferJComplement P A C) = 0`,
   `opCharPolyPhi3 P A C (cubeRootOp P A C) = 0`,
   `opCharPolyPhi3 P A C (cubeRootOpConj P A C) = 0`,
   `opCharPolyTransfer P A C (peirceTransfer P A C) = 0`,
   `opCharPolyTransfer P A C (peirceTransferComplement P A C) = 0`,
   `cyclotomicThree (genJ P A C) * cyclotomicSix (genJ P A C) = cyclotomicSix (genV P A C)`, and
   `cyclotomicThree (genPhi P A C) * cyclotomicSix (genPhi P A C) = cyclotomicThree (genV P A C)`. -/
theorem kantor_triple_five_grade_anomalies_and_operator_cyclotomic_charpoly_bridge
    {P : B} (hP : P * P = P) (A C D X : B) :
    let S := invS P
    (comm S (conePlus P A) = (2 : ℤ) • conePlus P A ∧
     comm S (coneMinus P C) = -(2 : ℤ) • coneMinus P C ∧
     comm S (evenGrade P D) = 0 ∧
     comm S (genV P A C) = 0 ∧
     comm S (genSig P A C) = 0 ∧
     comm S (comm S (comm S X)) - (4 : ℤ) • comm S X = 0) ∧
    (comm (evenGrade P D) (genJ P A C) = bdgUpperAnomaly P D A + bdgLowerAnomaly P D C ∧
     comm (evenGrade P D) (genPhi P A C) = bdgUpperAnomaly P D A - bdgLowerAnomaly P D C ∧
     comm S (bdgUpperAnomaly P D A) = (2 : ℤ) • bdgUpperAnomaly P D A ∧
     comm S (bdgLowerAnomaly P D C) = -(2 : ℤ) • bdgLowerAnomaly P D C) ∧
    (opKantorTriple (conePlus P A) (coneMinus P C) (conePlus P A) =
       (2 : ℤ) • (genV P A C * conePlus P A) ∧
     opKantorTriple (coneMinus P C) (conePlus P A) (coneMinus P C) =
       (2 : ℤ) • (genV P A C * coneMinus P C) ∧
     opKantorAnomaly (conePlus P A) (coneMinus P C) 1 = genSig P A C ∧
     opKantorAnomaly (conePlus P A) (coneMinus P C) S = -genV P A C) ∧
    (opCharPolyPhi6 P A C (peirceTransferJ P A C) = 0 ∧
     opCharPolyPhi6 P A C (peirceTransferJComplement P A C) = 0 ∧
     opCharPolyPhi3 P A C (cubeRootOp P A C) = 0 ∧
     opCharPolyPhi3 P A C (cubeRootOpConj P A C) = 0 ∧
     opCharPolyTransfer P A C (peirceTransfer P A C) = 0 ∧
     opCharPolyTransfer P A C (peirceTransferComplement P A C) = 0 ∧
     cyclotomicThree (genJ P A C) * cyclotomicSix (genJ P A C) = cyclotomicSix (genV P A C) ∧
     cyclotomicThree (genPhi P A C) * cyclotomicSix (genPhi P A C) = cyclotomicThree (genV P A C)) := by
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · unfold comm; peirce_nf hP
  · unfold comm; peirce_nf hP
  · unfold comm evenGrade; peirce_nf hP
  · unfold comm; peirce_nf hP
  · unfold comm; peirce_nf hP
  · unfold comm; peirce_nf hP
  · unfold comm evenGrade bdgUpperAnomaly bdgLowerAnomaly; peirce_nf hP
  · unfold comm evenGrade bdgUpperAnomaly bdgLowerAnomaly; peirce_nf hP
  · unfold comm bdgUpperAnomaly; peirce_nf hP
  · unfold comm bdgLowerAnomaly; peirce_nf hP
  · unfold opKantorTriple; peirce_nf hP
  · unfold opKantorTriple; peirce_nf hP
  · unfold opKantorAnomaly; peirce_nf hP
  · unfold opKantorAnomaly; peirce_nf hP
  · unfold opCharPolyPhi6 peirceTransferJ; peirce_nf hP
  · unfold opCharPolyPhi6 peirceTransferJComplement; peirce_nf hP
  · unfold opCharPolyPhi3 cubeRootOp; peirce_nf hP
  · unfold opCharPolyPhi3 cubeRootOpConj; peirce_nf hP
  · unfold opCharPolyTransfer peirceTransfer; peirce_nf hP
  · unfold opCharPolyTransfer peirceTransferComplement; peirce_nf hP
  · unfold cyclotomicThree cyclotomicSix; peirce_nf hP
  · unfold cyclotomicThree cyclotomicSix; peirce_nf hP

omit [StarRing B] in
/-- **Theorem X₁₁.2 (`zorn_associator_grade_anomaly_bridge`)**:
In `OperatorZornMatrix B` (`NCZornElement B`) over any non-commutative ring `B`,
sandwiching the upper-sheet element `pureNPlus a` or lower-sheet element `pureNMinus b`
inside the Zorn associator `associator X M Y = (X * M) * Y - X * (M * Y)` annihilates both
diagonal sheets (`n_plus = 0`, `n_minus = 0`) and swaps chirality in both off-diagonal
vector grades simultaneously via the octonionic cross-product anomaly:
1. For `M = pureNPlus a`:
   `(associator X (pureNPlus a) Y).n_plus = 0`,
   `(associator X (pureNPlus a) Y).n_minus = 0`,
   `(associator X (pureNPlus a) Y).sigma_plus i = -zornCross X.sigma_minus (fun j => a * Y.sigma_minus j) i`, and
   `(associator X (pureNPlus a) Y).sigma_minus i = -zornCross X.sigma_plus (fun j => a * Y.sigma_plus j) i`;
2. For `M = pureNMinus b`:
   `(associator X (pureNMinus b) Y).n_plus = 0`,
   `(associator X (pureNMinus b) Y).n_minus = 0`,
   `(associator X (pureNMinus b) Y).sigma_minus i = zornCross X.sigma_plus (fun j => b * Y.sigma_plus j) i`, and
   `(associator X (pureNMinus b) Y).sigma_plus i = zornCross X.sigma_minus (fun j => b * Y.sigma_minus j) i`. -/
theorem zorn_associator_grade_anomaly_bridge
    (a b : B)
    (X Y : InfoGeometry.Physics.NCG.NCZornElement B)
    (i : Fin 3) :
    let assoc := InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator
    let purePlus := InfoGeometry.Physics.NCG.NCZornElement.pureNPlus
    let pureMinus := InfoGeometry.Physics.NCG.NCZornElement.pureNMinus
    let zCross := InfoGeometry.Physics.NCG.NCZornElement.zornCross
    ((assoc X (purePlus a) Y).n_plus = 0 ∧
     (assoc X (purePlus a) Y).n_minus = 0 ∧
     (assoc X (purePlus a) Y).sigma_plus i =
       -zCross X.sigma_minus (fun j => a * Y.sigma_minus j) i ∧
     (assoc X (purePlus a) Y).sigma_minus i =
       -zCross X.sigma_plus (fun j => a * Y.sigma_plus j) i) ∧
    ((assoc X (pureMinus b) Y).n_plus = 0 ∧
     (assoc X (pureMinus b) Y).n_minus = 0 ∧
     (assoc X (pureMinus b) Y).sigma_minus i =
       zCross X.sigma_plus (fun j => b * Y.sigma_plus j) i ∧
     (assoc X (pureMinus b) Y).sigma_plus i =
       zCross X.sigma_minus (fun j => b * Y.sigma_minus j) i) := by
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · simp only [InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornSub_nPlus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nPlus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaPlus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaMinus,
      InfoGeometry.Physics.NCG.NCZornElement.pureNPlus,
      InfoGeometry.Physics.NCG.NCZornElement.zornDot,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]
    noncomm_ring
  · simp only [InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornSub_nMinus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nMinus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaPlus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaMinus,
      InfoGeometry.Physics.NCG.NCZornElement.pureNPlus,
      InfoGeometry.Physics.NCG.NCZornElement.zornDot,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]
    noncomm_ring
  · fin_cases i <;>
      (simp only [InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornSub_sigmaPlus_apply,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nPlus,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nMinus,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaPlus_apply,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaMinus_apply,
         InfoGeometry.Physics.NCG.NCZornElement.pureNPlus,
         InfoGeometry.Physics.NCG.NCZornElement.zornDot,
         InfoGeometry.Physics.NCG.NCZornElement.zornCross]
       noncomm_ring)
  · fin_cases i <;>
      (simp only [InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornSub_sigmaMinus_apply,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nPlus,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nMinus,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaPlus_apply,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaMinus_apply,
         InfoGeometry.Physics.NCG.NCZornElement.pureNPlus,
         InfoGeometry.Physics.NCG.NCZornElement.zornDot,
         InfoGeometry.Physics.NCG.NCZornElement.zornCross]
       noncomm_ring)
  · simp only [InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornSub_nPlus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nPlus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaPlus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaMinus,
      InfoGeometry.Physics.NCG.NCZornElement.pureNMinus,
      InfoGeometry.Physics.NCG.NCZornElement.zornDot,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]
    noncomm_ring
  · simp only [InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornSub_nMinus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nMinus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaPlus,
      InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaMinus,
      InfoGeometry.Physics.NCG.NCZornElement.pureNMinus,
      InfoGeometry.Physics.NCG.NCZornElement.zornDot,
      InfoGeometry.Physics.NCG.NCZornElement.zornCross]
    noncomm_ring
  · fin_cases i <;>
      (simp only [InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornSub_sigmaMinus_apply,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nPlus,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nMinus,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaPlus_apply,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaMinus_apply,
         InfoGeometry.Physics.NCG.NCZornElement.pureNMinus,
         InfoGeometry.Physics.NCG.NCZornElement.zornDot,
         InfoGeometry.Physics.NCG.NCZornElement.zornCross]
       noncomm_ring)
  · fin_cases i <;>
      (simp only [InfoGeometry.Canonical.OperatorZornFourPotentialGauge.associator,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornSub_sigmaPlus_apply,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nPlus,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_nMinus,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaPlus_apply,
         InfoGeometry.Canonical.OperatorZornFourPotentialGauge.zornMul_sigmaMinus_apply,
         InfoGeometry.Physics.NCG.NCZornElement.pureNMinus,
         InfoGeometry.Physics.NCG.NCZornElement.zornDot,
         InfoGeometry.Physics.NCG.NCZornElement.zornCross]
       noncomm_ring)

end InfoGeometry.OperatorAlgebra.PeirceSpine
