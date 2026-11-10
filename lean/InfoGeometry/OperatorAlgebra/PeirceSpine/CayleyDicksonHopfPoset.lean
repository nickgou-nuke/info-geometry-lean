/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Bergman
import InfoGeometry.OperatorAlgebra.PeirceSpine.QuantumAffineFlagClusterPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.UHFHeisenbergSugawaraVirasoroPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornPeirceTetradPoset
import InfoGeometry.OperatorAlgebra.PeirceSpine.Supercharge
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Stage `D₃₀` (Archetypes `N₁ → N₅`): Universal Lie–Jordan Product, Sector Charge Operators, Intertwining Embeddings, and Non-Commutative Operator Hopf Coordinates

This module formalizes the 5-stage causal poset of non-commutative Lie–Jordan, sector-idempotent
charge, intertwining embedding, and operator Hopf coordinate archetypes (`N₁ → N₅`) over an
arbitrary associative ring with involution `[Ring B] [StarRing B]`, reusing the canonical
`PeirceSpine` vocabulary (`comm`, `anticomm`, `conePlus`, `coneMinus`, `qgtPlus`, `qgtMinus`,
`genPhi`, `genV`, `genSig`):

1. **Archetype `N₁` (`fureyProduct`, `furey_universal_lie_jordan_quartet`):**
   Universal Lie–Jordan binary operation `fureyProduct a b = a * b + b * star a` unifying all four
   Hermitian (`star h = h`) and skew-Hermitian (`star u = -u`) commutator/anticommutator closure
   sectors simultaneously.
2. **Archetypes `N₂` & `N₃` (`chargeY6`, `chargeQ6`, `quatChiralInv`,
   `quaternionic_symmetry_breaking_and_charge_operators`):**
   Orthogonal sector idempotent charge operators `chargeY6` and `chargeQ6`, chiral difference
   `quatChiralInv P_H1 P_H2 = P_H2 - P_H1`, exact difference identity `Q₆ - Y₆ = 3 (P_H2 - P_H1)`,
   unital square `(P_H2 - P_H1)² = P_H1 + P_H2`, pre-breaking commutator vanishing
   `comm Y₆ (P_H1 * X * P_H2) = 0`, and post-breaking eigenvalue `comm Q₆ (P_H1 * X * P_H2) = -6 • (P_H1 * X * P_H2)`.
3. **Archetype `N₄` (`inducedEndoRep`, `corner_embedding_equivariance`):**
   A multiplicative, generally non-unital corner map on the associative ring `B`, satisfying
   `inducedEndoRep ι ι_inv X * ι = ι * X` when `ι_inv * ι = 1`. This is not an embedding of a
   Cayley–Dickson or split-octonion carrier; those nonassociative carriers require a separate map.
4. **Archetype `N₅` (`hopfCoordZ`, `hopfCoordPerp`, `hopfRadiusSq`,
   `operator_hopf_coordinate_identities_and_peirce_evaluations`,
   `stage_D30_furey_lie_jordan_corner_hopf_master_synthesis`):**
   Non-commutative operator Hopf coordinates `(a₁ a₁^⋆ - a₂ a₂^⋆, a₁ a₂^⋆ + a₂ a₁^⋆, a₁ a₁^⋆ + a₂ a₂^⋆)`
   connecting the Peirce north-pole pair `(P, conePlus P A)` directly to `(P - qgtPlus P A (star A), 0)`
   and the bipartite chiral cone pair `(conePlus P A, coneMinus P (star A))` directly to
   `(genSig P A (star A), 0, genV P A (star A))` with the exact quadratic identity `Z² + Perp² = (R²)²`.

## Three-Bucket Audit Classification

- **BUCKET 1 (`KERNEL_PROVED`):**
  All 5 stages `N₁ → N₅` (`CayleyDicksonHopfStage`), Furey's universal Lie–Jordan quartet,
  sector hypercharge/electric-charge operators `Y₆, Q₆`, corner embedding equivariance, and
  non-commutative operator Hopf coordinates in `[Ring B] [StarRing B]`.
- **BUCKET 2 (`EXPLICIT_HYPOTHESIS`):**
  Idempotency, mutual orthogonality, and Hermitian/skew-Hermitian star-hypotheses on `[Ring B] [StarRing B]`.
- **BUCKET 3 (`OPEN_HORIZON`):**
  Non-associative octonionic division-algebra representation beyond associative corner endomorphisms in `[Ring B]`.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

/-! ### 1. Causal Poset of Lie–Jordan, Sector Charge & Operator Hopf Archetypes (`N₁ → N₅`) -/

/-- The 5-stage causal poset of non-commutative Lie–Jordan, sector-charge, intertwining embedding,
and operator Hopf coordinate archetypes (`N₁ → N₅`). -/
inductive CayleyDicksonHopfStage : Type
  | N1_universal_lie_jordan_product
  | N2_sector_idempotent_charge_operators
  | N3_quaternionic_chiral_symmetry_breaking
  | N4_equivariant_intertwining_embedding
  | N5_operator_hopf_coordinate_evaluations
  deriving DecidableEq, Repr

namespace CayleyDicksonHopfStage

/-- Numerical topological rank of each stage `N₁..N₅`. -/
def rank : CayleyDicksonHopfStage → ℕ
  | N1_universal_lie_jordan_product => 1
  | N2_sector_idempotent_charge_operators => 2
  | N3_quaternionic_chiral_symmetry_breaking => 3
  | N4_equivariant_intertwining_embedding => 4
  | N5_operator_hopf_coordinate_evaluations => 5

/-- The topological rank map on `CayleyDicksonHopfStage` is injective. -/
theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> revert h <;> decide

instance : LinearOrder CayleyDicksonHopfStage :=
  LinearOrder.lift' rank rank_injective

/-- Directed causal dependency edges of the `N₁ → N₅` poset. -/
def causalEdge : CayleyDicksonHopfStage → CayleyDicksonHopfStage → Prop
  | N1_universal_lie_jordan_product, N2_sector_idempotent_charge_operators => True
  | N1_universal_lie_jordan_product, N5_operator_hopf_coordinate_evaluations => True
  | N2_sector_idempotent_charge_operators, N3_quaternionic_chiral_symmetry_breaking => True
  | N3_quaternionic_chiral_symmetry_breaking, N4_equivariant_intertwining_embedding => True
  | N4_equivariant_intertwining_embedding, N5_operator_hopf_coordinate_evaluations => True
  | _, _ => False

/-- Every directed causal edge in `CayleyDicksonHopfStage` strictly increases topological rank. -/
theorem causalEdge_strict_rank_mono {a b : CayleyDicksonHopfStage}
    (h : causalEdge a b) : rank a < rank b := by
  cases a <;> cases b <;> simp [causalEdge, rank] at h ⊢

/-- The directed causal edge relation on `CayleyDicksonHopfStage` is irreflexive. -/
theorem causalEdge_irrefl (a : CayleyDicksonHopfStage) : ¬ causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (causalEdge_strict_rank_mono h)

/-- Transitive chains of causal edges in `CayleyDicksonHopfStage` strictly increase topological rank. -/
theorem transGen_causalEdge_strict_rank_mono {a b : CayleyDicksonHopfStage}
    (h : Relation.TransGen causalEdge a b) : rank a < rank b := by
  induction h with
  | single hab => exact causalEdge_strict_rank_mono hab
  | tail _ hbc ih => exact lt_trans ih (causalEdge_strict_rank_mono hbc)

/-- The `CayleyDicksonHopfStage` causal poset is strictly acyclic. -/
theorem causalEdge_acyclic (a : CayleyDicksonHopfStage) :
    ¬ Relation.TransGen causalEdge a a := by
  intro h
  exact Nat.lt_irrefl (rank a) (transGen_causalEdge_strict_rank_mono h)

end CayleyDicksonHopfStage

/-! ### 2. Core Lie–Jordan, Sector Charge & Operator Hopf Coordinate Primitives -/

variable {B : Type*} [Ring B] [StarRing B]

/-- **Furey's Universal Lie–Jordan Product (`m(a, b) = a * b + b * star a`):**
Unifies the Jordan anticommutator and Lie commutator across Hermitian and skew-Hermitian sectors. -/
def fureyProduct (a b : B) : B :=
  a * b + b * star a

/-- **Pre-Breaking Sector Hypercharge Operator (`Y₆`):**
`2 • P_O2 + 3 • (P_H1 + P_H2) + 6 • P_C`. -/
def chargeY6 (P_O2 P_H1 P_H2 P_C : B) : B :=
  (2 : ℤ) • P_O2 + (3 : ℤ) • (P_H1 + P_H2) + (6 : ℤ) • P_C

/-- **Post-Breaking Sector Electric Charge Operator (`Q₆`):**
`2 • P_O2 + 6 • P_H2 + 6 • P_C`. -/
def chargeQ6 (P_O2 P_H2 P_C : B) : B :=
  (2 : ℤ) • P_O2 + (6 : ℤ) • P_H2 + (6 : ℤ) • P_C

/-- **Quaternionic Sector Chiral Involution (`Γ_H = P_H2 - P_H1`):** -/
def quatChiralInv (P_H1 P_H2 : B) : B :=
  P_H2 - P_H1

/-- **Induced Endomorphism Representation (`ρ_V(X) = ι * X * ι_inv`):** -/
def inducedEndoRep (ι ι_inv X : B) : B :=
  ι * X * ι_inv

/-- **Longitudinal Operator Hopf Coordinate (`Z(a₁, a₂) = a₁ a₁^⋆ - a₂ a₂^⋆`):** -/
def hopfCoordZ (a₁ a₂ : B) : B :=
  a₁ * star a₁ - a₂ * star a₂

/-- **Transverse Operator Hopf Coordinate (`Perp(a₁, a₂) = a₁ a₂^⋆ + a₂ a₁^⋆`):** -/
def hopfCoordPerp (a₁ a₂ : B) : B :=
  a₁ * star a₂ + a₂ * star a₁

/-- **Radial-Squared Operator Hopf Coordinate (`R²(a₁, a₂) = a₁ a₁^⋆ + a₂ a₂^⋆`):** -/
def hopfRadiusSq (a₁ a₂ : B) : B :=
  a₁ * star a₁ + a₂ * star a₂

/-- The radial-squared operator coordinate is self-adjoint. -/
theorem hopfRadiusSq_selfAdjoint (a₁ a₂ : B) :
    star (hopfRadiusSq a₁ a₂) = hopfRadiusSq a₁ a₂ := by
  unfold hopfRadiusSq
  rw [star_add, star_mul, star_mul, star_star, star_star]

omit [StarRing B] in
/-- Left-multiplication absorption `P * (P * X) = P * X` for an idempotent `P`. -/
theorem P_assoc {P : B} (hP : P * P = P) (X : B) : P * (P * X) = P * X := by
  rw [← mul_assoc, hP]

omit [StarRing B] in
/-- Associative zero-product propagation `X * (Y * Z) = 0` when `X * Y = 0`. -/
theorem zero_mul_assoc {X Y : B} (h : X * Y = 0) (Z : B) : X * (Y * Z) = 0 := by
  rw [← mul_assoc, h, zero_mul]

/-! ### 3. Individual Lemmas for Archetypes `N₁ → N₅` -/

/-- **Lemma `N₁.1` (`furey_universal_lie_jordan_quartet`):**
Let `h, h' : B` be Hermitian (`star h = h`, `star h' = h'`) and let `u, u' : B` be skew-Hermitian
(`star u = -u`, `star u' = -u'`). Then the single binary operation `fureyProduct a b = a * b + b * star a`
satisfies all four Lie–Jordan closure laws simultaneously:
1. `fureyProduct h h' = anticomm h h'` and `star (fureyProduct h h') = fureyProduct h h'`,
2. `fureyProduct u u' = comm u u'` and `star (fureyProduct u u') = -fureyProduct u u'`,
3. `fureyProduct h u = anticomm h u` and `star (fureyProduct h u) = -fureyProduct h u`,
4. `fureyProduct u h = comm u h` and `star (fureyProduct u h) = fureyProduct u h`. -/
lemma furey_universal_lie_jordan_quartet
    {h h' u u' : B}
    (hh : star h = h) (hh' : star h' = h')
    (hu : star u = -u) (hu' : star u' = -u') :
    fureyProduct h h' = anticomm h h' ∧
    star (fureyProduct h h') = fureyProduct h h' ∧
    fureyProduct u u' = comm u u' ∧
    star (fureyProduct u u') = -fureyProduct u u' ∧
    fureyProduct h u = anticomm h u ∧
    star (fureyProduct h u) = -fureyProduct h u ∧
    fureyProduct u h = comm u h ∧
    star (fureyProduct u h) = fureyProduct u h := by
  have h1 : fureyProduct h h' = anticomm h h' := by
    unfold fureyProduct anticomm; rw [hh]
  have h2 : fureyProduct u u' = comm u u' := by
    unfold fureyProduct comm; rw [hu, mul_neg, ← sub_eq_add_neg]
  have h3 : fureyProduct h u = anticomm h u := by
    unfold fureyProduct anticomm; rw [hh]
  have h4 : fureyProduct u h = comm u h := by
    unfold fureyProduct comm; rw [hu, mul_neg, ← sub_eq_add_neg]
  refine ⟨h1, ?_, h2, ?_, h3, ?_, h4, ?_⟩
  · rw [h1]; unfold anticomm; rw [star_add, star_mul, star_mul, hh, hh', add_comm]
  · rw [h2]; unfold comm; rw [star_sub, star_mul, star_mul, hu, hu', neg_mul_neg, neg_mul_neg, neg_sub]
  · rw [h3]; unfold anticomm; rw [star_add, star_mul, star_mul, hh, hu, neg_mul, mul_neg, ← neg_add, add_comm]
  · rw [h4]; unfold comm; rw [star_sub, star_mul, star_mul, hu, hh, mul_neg, neg_mul, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]

/-- **Lemma `N₁.2` (`fureyProduct_genPhi_genJ_tetraktys`):**
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A : B`, the Peirce
generators `genPhi P A (star A)` (Hermitian) and `genJ P A (star A)` (skew-Hermitian) satisfy
the exact Tetraktys Lie–Jordan table under `fureyProduct`:
1. `fureyProduct (genPhi P A (star A)) (genPhi P A (star A)) = (2 : ℤ) • genV P A (star A)`,
2. `fureyProduct (genJ P A (star A)) (genJ P A (star A)) = 0`,
3. `fureyProduct (genPhi P A (star A)) (genJ P A (star A)) = 0`,
4. `fureyProduct (genJ P A (star A)) (genPhi P A (star A)) = (2 : ℤ) • genSig P A (star A)`. -/
lemma fureyProduct_genPhi_genJ_tetraktys
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) :
    fureyProduct (genPhi P A (star A)) (genPhi P A (star A)) =
      (2 : ℤ) • genV P A (star A) ∧
    fureyProduct (genJ P A (star A)) (genJ P A (star A)) = 0 ∧
    fureyProduct (genPhi P A (star A)) (genJ P A (star A)) = 0 ∧
    fureyProduct (genJ P A (star A)) (genPhi P A (star A)) =
      (2 : ℤ) • genSig P A (star A) := by
  have hStarPlus : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarMinus : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarPlus, star_star]
  have hStarPhi : star (genPhi P A (star A)) = genPhi P A (star A) := by
    unfold genPhi
    rw [star_add, hStarPlus, hStarMinus, add_comm]
  have hStarJ : star (genJ P A (star A)) = -genJ P A (star A) := by
    unfold genJ
    rw [star_sub, hStarPlus, hStarMinus, neg_sub]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold fureyProduct
    rw [hStarPhi]
    peirce_nf hP
  · unfold fureyProduct
    rw [hStarJ]
    simp [mul_neg]
  · unfold fureyProduct
    rw [hStarPhi]
    peirce_nf hP
  · unfold fureyProduct
    rw [hStarJ, mul_neg]
    peirce_nf hP

omit [StarRing B] in
/-- The sector charge difference and the square of its chiral difference follow
from the orthogonal idempotent relations alone; no transition operator is
needed for these two operator identities. -/
theorem quaternionic_charge_difference_and_sector_square
    {P_O2 P_H1 P_H2 P_C : B}
    (hH1 : P_H1 * P_H1 = P_H1) (hH2 : P_H2 * P_H2 = P_H2)
    (hH12 : P_H1 * P_H2 = 0) (hH21 : P_H2 * P_H1 = 0) :
    chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C =
      (3 : ℤ) • quatChiralInv P_H1 P_H2 ∧
    quatChiralInv P_H1 P_H2 * quatChiralInv P_H1 P_H2 = P_H1 + P_H2 := by
  constructor
  · unfold chargeQ6 chargeY6 quatChiralInv
    simp only [zsmul_add, zsmul_sub]
    abel
  · unfold quatChiralInv
    simp only [sub_mul, mul_sub, hH1, hH2, hH12, hH21]
    abel

omit [StarRing B] in
/-- **Lemma `N₂.1 & N₃.1` (`quaternionic_symmetry_breaking_and_charge_operators`):**
Let `P_O2, P_H1, P_H2, P_C : B` be mutually orthogonal idempotents in the quaternionic sector
(`hH1 : P_H1 * P_H1 = P_H1`, `hH2 : P_H2 * P_H2 = P_H2`, `hH12 : P_H1 * P_H2 = 0`, `hH21 : P_H2 * P_H1 = 0`,
`hO_H1 : P_O2 * P_H1 = 0`, `hH2_O : P_H2 * P_O2 = 0`, `hC_H1 : P_C * P_H1 = 0`, `hH2_C : P_H2 * P_C = 0`).
Then for any off-diagonal transition operator `W_H = P_H1 * X * P_H2`:
1. **Charge Difference (`Q₆ - Y₆ = 3 (P_H2 - P_H1) = 3 Γ_H`):**
   `chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C = (3 : ℤ) • quatChiralInv P_H1 P_H2`.
2. **Square of the Quaternionic Chiral Involution Equals the Sector Projector `P_H1 + P_H2`:**
   `quatChiralInv P_H1 P_H2 * quatChiralInv P_H1 P_H2 = P_H1 + P_H2`.
3. **Pre-Breaking Invariance vs. Post-Breaking Charge Eigenvalue on `P_H1 * X * P_H2`:**
   - `comm (chargeY6 P_O2 P_H1 P_H2 P_C) (P_H1 * X * P_H2) = 0`,
   - `comm (chargeQ6 P_O2 P_H2 P_C) (P_H1 * X * P_H2) = -(6 : ℤ) • (P_H1 * X * P_H2)`. -/
theorem quaternionic_symmetry_breaking_and_charge_operators
    {P_O2 P_H1 P_H2 P_C : B}
    (hH1 : P_H1 * P_H1 = P_H1) (hH2 : P_H2 * P_H2 = P_H2)
    (hH12 : P_H1 * P_H2 = 0) (hH21 : P_H2 * P_H1 = 0)
    (hO_H1 : P_O2 * P_H1 = 0) (hH2_O : P_H2 * P_O2 = 0)
    (hC_H1 : P_C * P_H1 = 0) (hH2_C : P_H2 * P_C = 0) (X : B) :
    chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C =
      (3 : ℤ) • quatChiralInv P_H1 P_H2 ∧
    quatChiralInv P_H1 P_H2 * quatChiralInv P_H1 P_H2 = P_H1 + P_H2 ∧
    comm (chargeY6 P_O2 P_H1 P_H2 P_C) (P_H1 * X * P_H2) = 0 ∧
    comm (chargeQ6 P_O2 P_H2 P_C) (P_H1 * X * P_H2) =
      -(6 : ℤ) • (P_H1 * X * P_H2) := by
  have hBase := quaternionic_charge_difference_and_sector_square
    (P_O2 := P_O2) (P_C := P_C) hH1 hH2 hH12 hH21
  refine ⟨hBase.1, hBase.2, ?_, ?_⟩
  · unfold comm chargeY6
    simp only [add_mul, mul_add, smul_add, mul_assoc, smul_mul_assoc, mul_smul_comm,
               P_assoc hH1, hH2,
               hH21, zero_mul_assoc hH21,
               zero_mul_assoc hO_H1, hH2_O,
               zero_mul_assoc hC_H1, hH2_C,
               mul_zero, smul_zero]
    abel
  · unfold comm chargeQ6
    simp only [add_mul, mul_add, mul_assoc, smul_mul_assoc, mul_smul_comm,
               hH2,
               zero_mul_assoc hH21,
               zero_mul_assoc hO_H1, hH2_O,
               zero_mul_assoc hC_H1, hH2_C,
               mul_zero, smul_zero]
    abel

omit [StarRing B] in
/-- **Lemma `N₄.1` (`corner_embedding_equivariance`):**
Let `ι, ι_inv : B` satisfy `ι_inv * ι = 1`. Then for all `X, Y : B`:
1. `inducedEndoRep ι ι_inv X * ι = ι * X`,
2. `inducedEndoRep ι ι_inv X * inducedEndoRep ι ι_inv Y = inducedEndoRep ι ι_inv (X * Y)`. -/
theorem corner_embedding_equivariance
    {ι ι_inv : B} (hEmb : ι_inv * ι = 1) (X Y : B) :
    inducedEndoRep ι ι_inv X * ι = ι * X ∧
    inducedEndoRep ι ι_inv X * inducedEndoRep ι ι_inv Y =
      inducedEndoRep ι ι_inv (X * Y) := by
  constructor
  · unfold inducedEndoRep
    rw [mul_assoc, hEmb, mul_one]
  · unfold inducedEndoRep
    calc (ι * X * ι_inv) * (ι * Y * ι_inv)
      _ = ι * X * (ι_inv * ι) * Y * ι_inv := by simp only [mul_assoc]
      _ = ι * (X * Y) * ι_inv := by rw [hEmb, mul_one]; simp only [mul_assoc]

omit [StarRing B] in
/-- The conjugation-shaped map is injective under the stated one-sided inverse law.
Its value at `1` is the corner idempotent `ι * ι_inv`, so this does not assert
that it is a unital homomorphism into the ambient ring. -/
theorem inducedEndoRep_injective_of_leftInverse
    {ι ι_inv : B} (hEmb : ι_inv * ι = 1) :
    Function.Injective (inducedEndoRep ι ι_inv) := by
  intro X Y h
  have h' := congrArg (fun Z : B => ι_inv * Z * ι) h
  change ι_inv * (ι * X * ι_inv) * ι = ι_inv * (ι * Y * ι_inv) * ι at h'
  have hx : ι_inv * (ι * X * ι_inv) * ι = X := by
    calc
      _ = (ι_inv * ι) * X * (ι_inv * ι) := by noncomm_ring
      _ = X := by rw [hEmb]; simp
  have hy : ι_inv * (ι * Y * ι_inv) * ι = Y := by
    calc
      _ = (ι_inv * ι) * Y * (ι_inv * ι) := by noncomm_ring
      _ = Y := by rw [hEmb]; simp
  exact hx.symm.trans (h'.trans hy)

/-- **Lemma `N₅.1` (`operator_hopf_coordinate_identities_and_peirce_evaluations`):**
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`) and any `A, a₁, a₂ : B`:
1. **Self-Adjointness of All Three Operator Hopf Coordinates:**
   `star (hopfCoordZ a₁ a₂) = hopfCoordZ a₁ a₂` and
   `star (hopfCoordPerp a₁ a₂) = hopfCoordPerp a₁ a₂` and
   `star (hopfRadiusSq a₁ a₂) = hopfRadiusSq a₁ a₂`.
2. **North-Pole Peirce-Corner Evaluation (`a₁ = P`, `a₂ = conePlus P A`):**
   - `hopfCoordZ P (conePlus P A) = P - qgtPlus P A (star A)`,
    - `hopfCoordPerp P (conePlus P A) = 0`.
3. **Bipartite Chiral Cone Hopf Evaluation (`a₁ = conePlus P A`, `a₂ = coneMinus P (star A)`):**
   - `hopfCoordZ (conePlus P A) (coneMinus P (star A)) = genSig P A (star A)`,
   - `hopfCoordPerp (conePlus P A) (coneMinus P (star A)) = 0`,
   - `hopfRadiusSq (conePlus P A) (coneMinus P (star A)) = genV P A (star A)`,
   - **Exact Operator Hopf Sphere Identity (`Z² + Perp² = (R²)²`):**
     `hopfCoordZ (conePlus P A) (coneMinus P (star A)) * hopfCoordZ (conePlus P A) (coneMinus P (star A)) +`
     `hopfCoordPerp (conePlus P A) (coneMinus P (star A)) * hopfCoordPerp (conePlus P A) (coneMinus P (star A)) =`
     `hopfRadiusSq (conePlus P A) (coneMinus P (star A)) * hopfRadiusSq (conePlus P A) (coneMinus P (star A))`. -/
lemma operator_hopf_coordinate_identities_and_peirce_evaluations
    {P : B} (hP : P * P = P) (hPsym : star P = P) (a₁ a₂ A : B) :
    star (hopfCoordZ a₁ a₂) = hopfCoordZ a₁ a₂ ∧
    star (hopfCoordPerp a₁ a₂) = hopfCoordPerp a₁ a₂ ∧
    star (hopfRadiusSq a₁ a₂) = hopfRadiusSq a₁ a₂ ∧
    hopfCoordZ P (conePlus P A) = P - qgtPlus P A (star A) ∧
    hopfCoordPerp P (conePlus P A) = 0 ∧
    hopfCoordZ (conePlus P A) (coneMinus P (star A)) = genSig P A (star A) ∧
    hopfCoordPerp (conePlus P A) (coneMinus P (star A)) = 0 ∧
    hopfRadiusSq (conePlus P A) (coneMinus P (star A)) = genV P A (star A) ∧
    hopfCoordZ (conePlus P A) (coneMinus P (star A)) *
      hopfCoordZ (conePlus P A) (coneMinus P (star A)) +
      hopfCoordPerp (conePlus P A) (coneMinus P (star A)) *
      hopfCoordPerp (conePlus P A) (coneMinus P (star A)) =
      hopfRadiusSq (conePlus P A) (coneMinus P (star A)) *
      hopfRadiusSq (conePlus P A) (coneMinus P (star A)) := by
  have hStarConePlus : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarConeMinus : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarConePlus, star_star]
  have hZ : hopfCoordZ (conePlus P A) (coneMinus P (star A)) = genSig P A (star A) := by
    unfold hopfCoordZ genSig comm
    rw [hStarConePlus, hStarConeMinus]
  have hPerp : hopfCoordPerp (conePlus P A) (coneMinus P (star A)) = 0 := by
    unfold hopfCoordPerp
    rw [hStarConePlus, hStarConeMinus]
    peirce_nf hP
  have hRad : hopfRadiusSq (conePlus P A) (coneMinus P (star A)) = genV P A (star A) := by
    unfold hopfRadiusSq genV anticomm
    rw [hStarConePlus, hStarConeMinus]
  refine ⟨?_, ?_, hopfRadiusSq_selfAdjoint a₁ a₂, ?_, ?_, hZ, hPerp, hRad, ?_⟩
  · unfold hopfCoordZ; rw [star_sub, star_mul, star_mul, star_star, star_star]
  · unfold hopfCoordPerp; rw [star_add, star_mul, star_mul, star_star, star_star, add_comm]
  · unfold hopfCoordZ qgtPlus
    rw [hPsym, hP, hStarConePlus]
  · unfold hopfCoordPerp
    rw [hPsym, hStarConePlus]
    peirce_nf hP
  · rw [hZ, hPerp, hRad, mul_zero, add_zero]
    peirce_nf hP

/-- **Lemma `N₅.2` (`hopfCoord_north_pole_coneMinus`):**
On the spinor column pair `(P, coneMinus P (star A))`, the longitudinal Hopf coordinate evaluates
to `P - qgtMinus P A (star A)` and the transverse Hopf coordinate evaluates identically to the
odd Dirac/tetrad generator `genPhi P A (star A)`. -/
lemma hopfCoord_north_pole_coneMinus
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) :
    hopfCoordZ P (coneMinus P (star A)) = P - qgtMinus P A (star A) ∧
    hopfCoordPerp P (coneMinus P (star A)) = genPhi P A (star A) := by
  have hStarConePlus : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarConeMinus : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarConePlus, star_star]
  constructor
  · unfold hopfCoordZ qgtMinus
    rw [hPsym, hP, hStarConeMinus]
  · unfold hopfCoordPerp
    rw [hPsym, hStarConeMinus]
    peirce_nf hP

/-! ### 4. Master Theorem `D₃₀`: Synthesis of the Lie–Jordan, Sector-Charge & Operator Hopf Spine -/

/-- **Master Theorem `D₃₀` (`stage_D30_furey_lie_jordan_corner_hopf_master_synthesis`):**
Unifies all five stages (`N₁ → N₅`) of the non-commutative Lie–Jordan product, orthogonal sector-charge
symmetry breaking, equivariant intertwining embedding, and operator Hopf coordinates over `[Ring B] [StarRing B]`. -/
theorem stage_D30_furey_lie_jordan_corner_hopf_master_synthesis
    {P P_O2 P_H1 P_H2 P_C ι ι_inv h h' u u' X A : B}
    (hP : P * P = P) (hPsym : star P = P)
    (hh : star h = h) (hh' : star h' = h') (hu : star u = -u) (hu' : star u' = -u')
    (hH1 : P_H1 * P_H1 = P_H1) (hH2 : P_H2 * P_H2 = P_H2)
    (hH12 : P_H1 * P_H2 = 0) (hH21 : P_H2 * P_H1 = 0)
    (hO_H1 : P_O2 * P_H1 = 0) (hH2_O : P_H2 * P_O2 = 0)
    (hC_H1 : P_C * P_H1 = 0) (hH2_C : P_H2 * P_C = 0)
    (hEmb : ι_inv * ι = 1) :
    -- 1. Universal Lie–Jordan Product Quartet (`m(a, b) = a b + b a^⋆`) (N₁):
    fureyProduct h h' = anticomm h h' ∧
    fureyProduct u u' = comm u u' ∧
    fureyProduct h u = anticomm h u ∧
    fureyProduct u h = comm u h ∧
    -- 2. Sector Charge Symmetry Breaking (`Q₆ - Y₆ = 3 Γ_H`, `[Y₆, W_H] = 0`, `[Q₆, W_H] = -6 W_H`) (N₂ & N₃):
    chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C =
      (3 : ℤ) • quatChiralInv P_H1 P_H2 ∧
    comm (chargeY6 P_O2 P_H1 P_H2 P_C) (P_H1 * X * P_H2) = 0 ∧
    comm (chargeQ6 P_O2 P_H2 P_C) (P_H1 * X * P_H2) =
      -(6 : ℤ) • (P_H1 * X * P_H2) ∧
    -- 3. Multiplicative Corner Intertwining Map (N₄):
    inducedEndoRep ι ι_inv X * ι = ι * X ∧
    Function.Injective (inducedEndoRep ι ι_inv) ∧
    -- 4. Non-Commutative Operator Hopf Coordinates (`h_A(P, N_+) = (P - Q_+, 0)`, `h_A(N_+, N_-) = (Σ, 0)`) (N₅):
    hopfCoordZ P (conePlus P A) = P - qgtPlus P A (star A) ∧
    hopfCoordPerp P (conePlus P A) = 0 ∧
    hopfCoordZ (conePlus P A) (coneMinus P (star A)) = genSig P A (star A) ∧
    hopfCoordZ (conePlus P A) (coneMinus P (star A)) *
      hopfCoordZ (conePlus P A) (coneMinus P (star A)) +
      hopfCoordPerp (conePlus P A) (coneMinus P (star A)) *
      hopfCoordPerp (conePlus P A) (coneMinus P (star A)) =
      hopfRadiusSq (conePlus P A) (coneMinus P (star A)) *
      hopfRadiusSq (conePlus P A) (coneMinus P (star A)) ∧
    star (hopfRadiusSq (conePlus P A) (coneMinus P (star A))) =
      hopfRadiusSq (conePlus P A) (coneMinus P (star A)) := by
  rcases furey_universal_lie_jordan_quartet hh hh' hu hu' with
    ⟨hLJ1, _, hLJ3, _, hLJ5, _, hLJ7, _⟩
  rcases quaternionic_symmetry_breaking_and_charge_operators
    hH1 hH2 hH12 hH21 hO_H1 hH2_O hC_H1 hH2_C X with
    ⟨hQ1, _, hQ3, hQ4⟩
  rcases corner_embedding_equivariance hEmb X X with ⟨hE1, _⟩
  have hE2 := inducedEndoRep_injective_of_leftInverse hEmb
  rcases operator_hopf_coordinate_identities_and_peirce_evaluations hP hPsym P (conePlus P A) A with
    ⟨_, _, _, hH3, hH4, hH5, _, _, hH8⟩
  have hHrad := hopfRadiusSq_selfAdjoint (conePlus P A) (coneMinus P (star A))
  exact ⟨hLJ1, hLJ3, hLJ5, hLJ7, hQ1, hQ3, hQ4, hE1, hE2,
    hH3, hH4, hH5, hH8, hHrad⟩

/-! ### 5. Stages `D₃₃`–`D₃₅`: Hopf–Zorn Matrix Soldering, Partial-Flag Sector Charge Realization, and All-Mode Virasoro–Hopf Tower -/

/-- **Theorem `D₃₃` (`hopf_zorn_matrix_soldering_and_norm`):**
Solders the non-commutative operator Hopf coordinates (`hopfCoordZ`, `hopfCoordPerp`, `hopfRadiusSq`)
directly to the Zorn–Peirce block encoding `zornMatrix` and quadratic norm `zornNorm`:
1. `zornMatrix P (hopfCoordZ P (conePlus P A)) (1 - qgtMinus P A (star A)) (-A) (star A) =`
   `(1 - genV P A (star A)) + genPhi P A (star A)`,
2. `zornMatrix P (hopfRadiusSq (conePlus P A) (coneMinus P (star A)))`
   `  (hopfRadiusSq (conePlus P A) (coneMinus P (star A))) (-A) (star A) =`
   `genV P A (star A) + genPhi P A (star A)`,
3. `zornNorm P (genV P A (star A) + genPhi P A (star A)) =`
   `idemDefect (hopfRadiusSq (conePlus P A) (coneMinus P (star A)))`. -/
theorem hopf_zorn_matrix_soldering_and_norm
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) :
    zornMatrix P (hopfCoordZ P (conePlus P A)) (1 - qgtMinus P A (star A)) (-A) (star A) =
      (1 - genV P A (star A)) + genPhi P A (star A) ∧
    zornMatrix P
        (hopfRadiusSq (conePlus P A) (coneMinus P (star A)))
        (hopfRadiusSq (conePlus P A) (coneMinus P (star A)))
        (-A) (star A) =
      genV P A (star A) + genPhi P A (star A) ∧
    zornNorm P (genV P A (star A) + genPhi P A (star A)) =
      idemDefect (hopfRadiusSq (conePlus P A) (coneMinus P (star A))) := by
  rcases operator_hopf_coordinate_identities_and_peirce_evaluations hP hPsym P (conePlus P A) A with
    ⟨_, _, _, hHopfZ, _, _, _, hHopfRad, _⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hHopfZ]
    unfold zornMatrix peirce11 peirce00 qgtPlus qgtMinus
    peirce_nf hP
  · rw [hHopfRad]
    unfold zornMatrix peirce11 peirce00
    peirce_nf hP
  · rw [hHopfRad]
    exact (zorn_conjugation_and_quadratic_norms hP 1 1 A (star A)).2.2

omit [StarRing B] in
/-- **Theorem `D₃₄` (`partial_flag_sector_quaternionic_symmetry_breaking_and_step_charges`):**
Instantiates the orthogonal 4-sector charge decomposition (`P_O2`, `P_H1`, `P_H2`, `P_C`)
concretely on the 4-stratum partial flag filtration `P₁ ⊂ P₂ ⊂ P₃`
(`P_O2 := P₁`, `P_H1 := flagStratumIdem P₁ P₂`, `P_H2 := flagStratumIdem P₂ P₃`, `P_C := 1 - P₃`),
discharging all orthogonality hypotheses and proving the exact pre-breaking (`chargeY6`) and
post-breaking (`chargeQ6`) charge eigenvalues on the parabolic step corners `flagStepCorner`. -/
theorem partial_flag_sector_quaternionic_symmetry_breaking_and_step_charges
    {P₁ P₂ P₃ : B}
    (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂) (h3 : P₃ * P₃ = P₃)
    (h12 : P₁ * P₂ = P₁) (h21 : P₂ * P₁ = P₁)
    (h23 : P₂ * P₃ = P₂) (h32 : P₃ * P₂ = P₂)
    (h13 : P₁ * P₃ = P₁) (h31 : P₃ * P₁ = P₁)
    (X : B) :
    let P_O2 := P₁
    let P_H1 := flagStratumIdem P₁ P₂
    let P_H2 := flagStratumIdem P₂ P₃
    let P_C := 1 - P₃
    P_O2 + P_H1 + P_H2 + P_C = 1 ∧
    chargeQ6 P_O2 P_H2 P_C - chargeY6 P_O2 P_H1 P_H2 P_C =
      (3 : ℤ) • quatChiralInv P_H1 P_H2 ∧
    quatChiralInv P_H1 P_H2 * quatChiralInv P_H1 P_H2 = P_H1 + P_H2 ∧
    comm (chargeY6 P_O2 P_H1 P_H2 P_C) (flagStepCorner P_H1 P_H2 X) = 0 ∧
    comm (chargeQ6 P_O2 P_H2 P_C) (flagStepCorner P_H1 P_H2 X) =
      -(6 : ℤ) • flagStepCorner P_H1 P_H2 X ∧
    comm (chargeY6 P_O2 P_H1 P_H2 P_C) (flagStepCorner P_O2 P_H1 X) =
      -flagStepCorner P_O2 P_H1 X ∧
    comm (chargeQ6 P_O2 P_H2 P_C) (flagStepCorner P_O2 P_H1 X) =
      (2 : ℤ) • flagStepCorner P_O2 P_H1 X := by
  dsimp only
  have hFlags := stage_D30_three_step_partial_flag_and_parabolic_radical_bridge
      h1 h2 h3 h12 h21 h23 h32 h13 h31 X X
  have hH1 := hFlags.1
  have hH2 := hFlags.2.1
  have hH12 := hFlags.2.2.1
  have hH21 := hFlags.2.2.2.1
  have hPart := hFlags.2.2.2.2.1
  have hOH1 : P₁ * flagStratumIdem P₁ P₂ = 0 := by
    unfold flagStratumIdem; rw [mul_sub, h12, h1, sub_self]
  have hH2O : flagStratumIdem P₂ P₃ * P₁ = 0 := by
    unfold flagStratumIdem; rw [sub_mul, h31, h21, sub_self]
  have hCH1 : (1 - P₃) * flagStratumIdem P₁ P₂ = 0 := by
    unfold flagStratumIdem
    simp only [sub_mul, mul_sub, one_mul, h32, h31, sub_self]
  have hH2C : flagStratumIdem P₂ P₃ * (1 - P₃) = 0 := by
    unfold flagStratumIdem
    simp only [sub_mul, mul_sub, mul_one, h3, h23, sub_self]
  have hH1O : flagStratumIdem P₁ P₂ * P₁ = 0 := by
    unfold flagStratumIdem; rw [sub_mul, h21, h1, sub_self]
  have hH1C : flagStratumIdem P₁ P₂ * (1 - P₃) = 0 := by
    unfold flagStratumIdem
    simp only [sub_mul, mul_sub, mul_one, h23, h13, sub_self]
  have hCO : (1 - P₃) * P₁ = 0 := by
    rw [sub_mul, one_mul, h31, sub_self]
  rcases quaternionic_symmetry_breaking_and_charge_operators
      hH1 hH2 hH12 hH21 hOH1 hH2O hCH1 hH2C X with
    ⟨hDiff, hSq, hY23, hQ23⟩
  let W := flagStepCorner P₁ (flagStratumIdem P₁ P₂) X
  have hO_W : P₁ * W = W := by
    unfold W flagStepCorner; rw [← mul_assoc, ← mul_assoc, h1]
  have hW_O : W * P₁ = 0 := by
    unfold W flagStepCorner; rw [mul_assoc, hH1O, mul_zero]
  have hH1_W : flagStratumIdem P₁ P₂ * W = 0 := by
    unfold W flagStepCorner; rw [← mul_assoc, ← mul_assoc, hH1O, zero_mul, zero_mul]
  have hW_H1 : W * flagStratumIdem P₁ P₂ = W := by
    unfold W flagStepCorner; rw [mul_assoc, hH1]
  have hH2_W : flagStratumIdem P₂ P₃ * W = 0 := by
    unfold W flagStepCorner; rw [← mul_assoc, ← mul_assoc, hH2O, zero_mul, zero_mul]
  have hW_H2 : W * flagStratumIdem P₂ P₃ = 0 := by
    unfold W flagStepCorner; rw [mul_assoc, hH12, mul_zero]
  have hC_W : (1 - P₃) * W = 0 := by
    unfold W flagStepCorner; rw [← mul_assoc, ← mul_assoc, hCO, zero_mul, zero_mul]
  have hW_C : W * (1 - P₃) = 0 := by
    unfold W flagStepCorner; rw [mul_assoc, hH1C, mul_zero]
  refine ⟨hPart, hDiff, hSq, hY23, hQ23, ?_, ?_⟩
  · change comm (chargeY6 P₁ (flagStratumIdem P₁ P₂) (flagStratumIdem P₂ P₃) (1 - P₃)) W = -W
    unfold comm chargeY6
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
               hO_W, hW_O, hH1_W, hW_H1, hH2_W, hW_H2, hC_W, hW_C,
               smul_zero, add_zero, zero_add]
    abel
  · change comm (chargeQ6 P₁ (flagStratumIdem P₂ P₃) (1 - P₃)) W = (2 : ℤ) • W
    unfold comm chargeQ6
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
               hO_W, hW_O, hH2_W, hW_H2, hC_W, hW_C,
               smul_zero, add_zero, sub_zero]

/-- **Theorem `D₃₅` (`all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower`):**
For any self-adjoint idempotent `P` (`P * P = P`, `star P = P`), any `A : B`, and any mode index `n : ℕ`,
evaluating the non-commutative operator Hopf coordinates (`hopfCoordZ`, `hopfCoordPerp`, `hopfRadiusSq`)
and Furey's Lie–Jordan product `fureyProduct` on the affine Heisenberg current modes
`J_{+,n} = heisenbergSourceMode n P A (star A)` and `J_{-,n} = heisenbergSinkMode n P A (star A)` yields:
1. `star (heisenbergSourceMode n P A (star A)) = heisenbergSinkMode n P A (star A)` and
   `star (heisenbergSinkMode n P A (star A)) = heisenbergSourceMode n P A (star A)`,
2. `hopfCoordZ (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) =`
   `virasoroModeChiral (n + n) P A (star A)`,
3. `hopfCoordPerp (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) = 0`,
4. `hopfRadiusSq (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) =`
   `virasoroModeEven (n + n) P A (star A)`,
5. **All-Mode Virasoro–Hopf Sphere Identity (`Z_n² + Perp_n² = R_n⁴ = L_{4n+1}^+`):**
   `hopfCoordZ (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) *`
   `  hopfCoordZ (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) +`
   `hopfCoordPerp (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) *`
   `  hopfCoordPerp (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) =`
   `virasoroModeEven (n + n + (n + n) + 1) P A (star A)`,
6. `fureyProduct (heisenbergSourceMode n P A (star A)) (heisenbergSourceMode n P A (star A)) =`
   `heisenbergSourceMode n P A (star A) * heisenbergSinkMode n P A (star A)`. -/
theorem all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A : B) (n : ℕ) :
    star (heisenbergSourceMode n P A (star A)) = heisenbergSinkMode n P A (star A) ∧
    star (heisenbergSinkMode n P A (star A)) = heisenbergSourceMode n P A (star A) ∧
    hopfCoordZ (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) =
      virasoroModeChiral (n + n) P A (star A) ∧
    hopfCoordPerp (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) = 0 ∧
    hopfRadiusSq (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) =
      virasoroModeEven (n + n) P A (star A) ∧
    hopfCoordZ (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) *
        hopfCoordZ (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) +
      hopfCoordPerp (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) *
        hopfCoordPerp (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) =
      virasoroModeEven (n + n + (n + n) + 1) P A (star A) ∧
    fureyProduct (heisenbergSourceMode n P A (star A)) (heisenbergSourceMode n P A (star A)) =
      heisenbergSourceMode n P A (star A) * heisenbergSinkMode n P A (star A) := by
  have hStarConePlus : star (conePlus P A) = coneMinus P (star A) := by
    unfold conePlus coneMinus
    rw [star_mul, star_mul, star_sub, star_one, hPsym, mul_assoc]
  have hStarConeMinus : star (coneMinus P (star A)) = conePlus P A := by
    rw [← hStarConePlus, star_star]
  have hStarSug : star (sugawaraTensor P A (star A)) = sugawaraTensor P A (star A) := by
    unfold sugawaraTensor chiralSource chiralSink anticomm
    change star (conePlus P A * coneMinus P (star A) + coneMinus P (star A) * conePlus P A) =
      conePlus P A * coneMinus P (star A) + coneMinus P (star A) * conePlus P A
    rw [star_add, star_mul, star_mul, hStarConePlus, hStarConeMinus, add_comm]
  have hStarOpPow : ∀ k : ℕ,
      star (opPow k (sugawaraTensor P A (star A))) = opPow k (sugawaraTensor P A (star A)) := by
    intro k
    induction k with
    | zero => simp [opPow]
    | succ m ih =>
      rw [opPow_succ, star_mul, ih, hStarSug, mul_opPow_comm, ← opPow_succ]
  have hStarSrc :
      star (heisenbergSourceMode n P A (star A)) = heisenbergSinkMode n P A (star A) := by
    unfold heisenbergSourceMode heisenbergSinkMode chiralSource chiralSink
    change star (opPow n (sugawaraTensor P A (star A)) * conePlus P A) =
      coneMinus P (star A) * opPow n (sugawaraTensor P A (star A))
    rw [star_mul, hStarConePlus, hStarOpPow n]
  have hStarSnk :
      star (heisenbergSinkMode n P A (star A)) = heisenbergSourceMode n P A (star A) := by
    rw [← hStarSrc, star_star]
  rcases all_mode_heisenberg_current_algebra hP A (star A) n n with
    ⟨hJpSq, hJmSq, hComm, hAnti⟩
  have hHopfZ :
      hopfCoordZ (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) =
        virasoroModeChiral (n + n) P A (star A) := by
    unfold hopfCoordZ
    rw [hStarSrc, hStarSnk, ← hComm]
    rfl
  have hHopfPerp :
      hopfCoordPerp (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) = 0 := by
    unfold hopfCoordPerp
    rw [hStarSnk, hStarSrc, hJpSq, hJmSq, add_zero]
  have hHopfRad :
      hopfRadiusSq (heisenbergSourceMode n P A (star A)) (heisenbergSinkMode n P A (star A)) =
        virasoroModeEven (n + n) P A (star A) := by
    unfold hopfRadiusSq
    rw [hStarSrc, hStarSnk, ← hAnti]
    rfl
  have hChiralSq := (virasoro_sugawara_mode_closure hP A (star A) (n + n) (n + n)).2.1
  refine ⟨hStarSrc, hStarSnk, hHopfZ, hHopfPerp, hHopfRad, ?_, ?_⟩
  · rw [hHopfZ, hHopfPerp, mul_zero, add_zero, hChiralSq]
  · unfold fureyProduct
    rw [hStarSrc, hJpSq, zero_add]

/-- **Theorem `D₃₆.1` (`star_mul_hopfRadiusSq_and_zornTetradSym_eq_sum_squares`):**
In any associative ring with involution `[Ring B] [StarRing B]`, for any self-adjoint
idempotent `P` (`P * P = P`, `star P = P`), any `A, X : B`, and any mode index `r : ℕ`,
conjugating `hopfRadiusSq (heisenbergSourceMode r P A (star A)) (heisenbergSinkMode r P A (star A))`,
`virasoroModeEven (r + r) P A (star A)`, and the diagonal complex-tetrad metric
`zornTetradSym P A (star A) A (star A)` by `X` yields an exact sum of Hermitian squares:
1. `star X * hopfRadiusSq (heisenbergSourceMode r P A (star A)) (heisenbergSinkMode r P A (star A)) * X =`
   `star (heisenbergSinkMode r P A (star A) * X) * (heisenbergSinkMode r P A (star A) * X) +`
   `star (heisenbergSourceMode r P A (star A) * X) * (heisenbergSourceMode r P A (star A) * X)`,
2. `star X * virasoroModeEven (r + r) P A (star A) * X =`
   `star (heisenbergSinkMode r P A (star A) * X) * (heisenbergSinkMode r P A (star A) * X) +`
   `star (heisenbergSourceMode r P A (star A) * X) * (heisenbergSourceMode r P A (star A) * X)`,
3. `star X * zornTetradSym P A (star A) A (star A) * X =`
   `star (genPhi P A (star A) * X) * (genPhi P A (star A) * X) +`
   `star (genPhi P A (star A) * X) * (genPhi P A (star A) * X)`. -/
theorem star_mul_hopfRadiusSq_and_zornTetradSym_eq_sum_squares
    {P : B} (hP : P * P = P) (hPsym : star P = P) (A X : B) (r : ℕ) :
    star X * hopfRadiusSq (heisenbergSourceMode r P A (star A))
        (heisenbergSinkMode r P A (star A)) * X =
      star (heisenbergSinkMode r P A (star A) * X) * (heisenbergSinkMode r P A (star A) * X) +
        star (heisenbergSourceMode r P A (star A) * X) *
          (heisenbergSourceMode r P A (star A) * X) ∧
    star X * virasoroModeEven (r + r) P A (star A) * X =
      star (heisenbergSinkMode r P A (star A) * X) * (heisenbergSinkMode r P A (star A) * X) +
        star (heisenbergSourceMode r P A (star A) * X) *
          (heisenbergSourceMode r P A (star A) * X) ∧
    star X * zornTetradSym P A (star A) A (star A) * X =
      star (genPhi P A (star A) * X) * (genPhi P A (star A) * X) +
        star (genPhi P A (star A) * X) * (genPhi P A (star A) * X) := by
  rcases all_mode_heisenberg_virasoro_hopf_coordinate_identity_and_furey_tower hP hPsym A r with
    ⟨hStarSrc, hStarSnk, _, _, hHopfRad, _, _⟩
  have h1 :
      star X * hopfRadiusSq (heisenbergSourceMode r P A (star A))
          (heisenbergSinkMode r P A (star A)) * X =
        star (heisenbergSinkMode r P A (star A) * X) * (heisenbergSinkMode r P A (star A) * X) +
          star (heisenbergSourceMode r P A (star A) * X) *
            (heisenbergSourceMode r P A (star A) * X) := by
    unfold hopfRadiusSq
    rw [star_mul (heisenbergSinkMode r P A (star A)) X,
        star_mul (heisenbergSourceMode r P A (star A)) X,
        hStarSrc, hStarSnk]
    noncomm_ring
  have h2 :
      star X * virasoroModeEven (r + r) P A (star A) * X =
        star (heisenbergSinkMode r P A (star A) * X) * (heisenbergSinkMode r P A (star A) * X) +
          star (heisenbergSourceMode r P A (star A) * X) *
            (heisenbergSourceMode r P A (star A) * X) := by
    rw [← hHopfRad, h1]
  have hStarPhi : star (genPhi P A (star A)) = genPhi P A (star A) := by
    unfold genPhi conePlus coneMinus
    rw [star_add, star_mul, star_mul, star_mul, star_mul, star_sub, star_one, star_star, hPsym,
        mul_assoc, mul_assoc, add_comm]
  have hSymEq :=
    (complex_tetrad_metric_electromagnetic_split_and_square hP hPsym A (star A) A (star A)).1
  have h3 :
      star X * zornTetradSym P A (star A) A (star A) * X =
        star (genPhi P A (star A) * X) * (genPhi P A (star A) * X) +
          star (genPhi P A (star A) * X) * (genPhi P A (star A) * X) := by
    rw [← hSymEq, star_mul (genPhi P A (star A)) X, hStarPhi]
    unfold anticomm
    noncomm_ring
  exact ⟨h1, h2, h3⟩

end InfoGeometry.OperatorAlgebra.PeirceSpine
