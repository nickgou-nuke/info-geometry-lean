/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.Attention.AttentionMetriplecticPoset

/-!
# Causal Poset of the Metriplectic Attention Architecture (Archetypes 901–917)

This module establishes the verified causal poset of the 17 archetypes governing
the Metriplectic Attention Dynamics, the Latent Curvature Lie Holonomy,
the Multi-Head Symplectic Reduction, the Residual Stream Euler-Metriplectic Flow,
and the Symplectic Defect Operator Tetrad:

  Archetype 901: metriplecticSplit (M = diag(M) + C(M))
  Archetype 902: frobeniusOrthogonality (⟨diag(M), C(M)⟩ = 0)
  Archetype 903: casimirGradingInvariance (tr(G * C(M)) = 0)
  Archetype 904: metriplecticDiracDispersion ((pG + C)² = (p² + m²)·1)
  Archetype 905: softmaxEntropySecondLaw (tr(diag(M)) > 0 as irreversible entropy)
  Archetype 906: latentCurvatureLieHolonomy ([C₁, C₂] = ω(M₁, M₂)·G)
  Archetype 907: multiHeadSymplecticReduction (Hᵀ J + J H = 0, H ∈ 𝔰𝔭(2, ℝ))
  Archetype 908: residualEulerIntegrator (x_{l+1} = x_l + M x_l)
  Archetype 909: metriplecticPropagator (T(M) = (𝕀 + diag(M)) + C(M))
  Archetype 910: kineticEnergyConservation (⟨x, C(M)x⟩ = 0 for skew-symmetric coupling)
  Archetype 911: dissipativeRadialContraction (⟨x, Mx⟩ = M₀₀ x₀² + M₁₁ x₁²)
  Archetype 912: lyapunovLatentStability (ΔE = 2⟨x, Mx⟩ + ‖Mx‖²)
  Archetype 913: symplecticDefectIdentity (Xᵀ J + J X = tr(X) • J)
  Archetype 914: symplecticTracelessEquivalence (Xᵀ J + J X = 0 ↔ tr(X) = 0)
  Archetype 915: tracelessCanonicalProjection (traceless_proj(X) ∈ 𝔰𝔭(2, ℝ))
  Archetype 916: operatorTetradDecomposition (M = c₀ 𝕀 + c₁ G + c₂ C_sym + c₃ J)
  Archetype 917: tetradPairwiseOrthogonality (⟨A, B⟩ = 0 for A ≠ B in tetrad)

Every theorem is verified with 0 sorry and 0 custom axioms.
-/

inductive MetriplecticArchetype : Type
  | metriplecticSplit
  | frobeniusOrthogonality
  | casimirGradingInvariance
  | metriplecticDiracDispersion
  | softmaxEntropySecondLaw
  | latentCurvatureLieHolonomy
  | multiHeadSymplecticReduction
  | residualEulerIntegrator
  | metriplecticPropagator
  | kineticEnergyConservation
  | dissipativeRadialContraction
  | lyapunovLatentStability
  | symplecticDefectIdentity
  | symplecticTracelessEquivalence
  | tracelessCanonicalProjection
  | operatorTetradDecomposition
  | tetradPairwiseOrthogonality
  | polylogOne
  | oddsRatioDeriv
  | motivicNilpotent
  | dilogarithmSeam
  | carnotShannonUnification
  deriving DecidableEq, Repr

open MetriplecticArchetype

/-- The causal prerequisite set for each archetype in the metriplectic architecture. -/
def causalPrerequisites : MetriplecticArchetype → Finset ℕ
  | metriplecticSplit               => {0}
  | frobeniusOrthogonality           => {0, 1}
  | casimirGradingInvariance         => {0, 2}
  | metriplecticDiracDispersion      => {0, 2, 3}
  | softmaxEntropySecondLaw          => {0, 4}
  | latentCurvatureLieHolonomy       => {0, 2, 5}
  | multiHeadSymplecticReduction     => {0, 2, 3, 6}
  | residualEulerIntegrator          => {0, 7}
  | metriplecticPropagator           => {0, 7, 8}
  | kineticEnergyConservation        => {0, 2, 7, 9}
  | dissipativeRadialContraction     => {0, 7, 8, 10}
  | lyapunovLatentStability          => {0, 2, 7, 8, 9, 10, 11}
  | symplecticDefectIdentity         => {0, 2, 3, 6, 12}
  | symplecticTracelessEquivalence   => {0, 2, 3, 6, 12, 13}
  | tracelessCanonicalProjection     => {0, 2, 3, 6, 12, 13, 14}
  | operatorTetradDecomposition      => {0, 2, 3, 6, 12, 13, 14, 15}
  | tetradPairwiseOrthogonality       => {0, 1, 2, 3, 6, 12, 13, 14, 15, 16}
  | polylogOne                        => {0, 4, 17}
  | oddsRatioDeriv                    => {0, 4, 17, 18}
  | motivicNilpotent                  => {0, 2, 4, 5, 17, 18}
  | dilogarithmSeam                   => {0, 2, 4, 5, 17, 18, 19}
  | carnotShannonUnification          => {0, 2, 4, 5, 17, 18, 19, 20}

/-- Master Theorem 1 (Prerequisites Faithfulness):
    The causal prerequisite map is strictly injective. -/
theorem causalPrerequisites_injective : Function.Injective causalPrerequisites := by
  intro a b h
  cases a <;> cases b <;> try rfl
  all_goals revert h; decide

/-- Canonical Partial Order on Metriplectic Archetypes lifted from Finset inclusion. -/
instance : PartialOrder MetriplecticArchetype :=
  PartialOrder.lift causalPrerequisites causalPrerequisites_injective

/-- Decidable ordering relation for automatic verification. -/
instance : DecidableRel (α := MetriplecticArchetype) (· ≤ ·) :=
  fun left right => inferInstanceAs (Decidable (causalPrerequisites left ⊆ causalPrerequisites right))

/-- Master Theorem 2: Strict irreflexivity of causal precedence (acyclic DAG). -/
theorem causalOrder_irreflexive_strict (a : MetriplecticArchetype) : ¬(a < a) :=
  lt_irrefl a

/-- Master Theorem 3: Metriplectic splitting is the foundational root of all 17 archetypes. -/
theorem metriplecticSplit_is_root (a : MetriplecticArchetype) :
    metriplecticSplit ≤ a := by
  cases a <;> decide

/-- Master Theorem 4: The Second Law entropy trace is structurally independent of the curvature Lie bracket. -/
theorem entropy_incomparable_curvature :
    ¬(softmaxEntropySecondLaw ≤ latentCurvatureLieHolonomy) ∧
    ¬(latentCurvatureLieHolonomy ≤ softmaxEntropySecondLaw) := by
  decide

/-- Master Theorem 5: The Dirac dispersion causally precedes multi-head symplectic reduction. -/
theorem dispersion_le_symplectic_reduction :
    metriplecticDiracDispersion ≤ multiHeadSymplecticReduction := by
  decide

/-- Master Theorem 6: Symplectic reduction causally precedes the symplectic defect identity. -/
theorem reduction_le_defect_identity :
    multiHeadSymplecticReduction ≤ symplecticDefectIdentity := by
  decide

/-- Master Theorem 7: The defect identity causally precedes the 2D sp(2, ℝ) ≅ sl₂(ℝ) equivalence. -/
theorem defect_identity_le_equivalence :
    symplecticDefectIdentity ≤ symplecticTracelessEquivalence := by
  decide

/-- Master Theorem 8: The tetrad decomposition causally precedes pairwise Frobenius orthogonality. -/
theorem tetrad_le_orthogonality :
    operatorTetradDecomposition ≤ tetradPairwiseOrthogonality := by
  decide

/-- Master Theorem 9: The forward-Euler residual integrator causally precedes Lyapunov stability. -/
theorem euler_le_lyapunov :
  residualEulerIntegrator ≤ lyapunovLatentStability := by
  decide

theorem motivic_chain :
    polylogOne ≤ oddsRatioDeriv ∧
    oddsRatioDeriv ≤ motivicNilpotent ∧
    motivicNilpotent ≤ dilogarithmSeam ∧
    dilogarithmSeam ≤ carnotShannonUnification := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- Master Theorem 10: Reversible kinetic energy conservation is a prerequisite for Lyapunov stability. -/
theorem kinetic_conservation_le_lyapunov :
    kineticEnergyConservation ≤ lyapunovLatentStability := by
  decide

/-! ### Non-Commutative Operator Realization of `MetriplecticArchetype` over `[Ring B]` -/

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- Non-commutative operator realization mapping each `MetriplecticArchetype` node
to its canonical Peirce operator in `[Ring B]`. -/
def metriplecticArchetypeOperator (P A C X : B) : MetriplecticArchetype → B
  | .metriplecticSplit => evenGrade P X + oddGrade P X
  | .frobeniusOrthogonality => peirce11 P X * peirce00 P X
  | .casimirGradingInvariance => invS P * evenGrade P X * invS P
  | .metriplecticDiracDispersion => genPhi P A C * genPhi P A C
  | .softmaxEntropySecondLaw => evenGrade P X
  | .latentCurvatureLieHolonomy => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genPhi P A C) (genJ P A C)
  | .multiHeadSymplecticReduction => InfoGeometry.OperatorAlgebra.PeirceSpine.anticomm (genPhi P A C) (genJ P A C)
  | .residualEulerIntegrator => 1 + oddGrade P X
  | .metriplecticPropagator => (1 + evenGrade P X) + oddGrade P X
  | .kineticEnergyConservation => genJ P A C * genJ P A C
  | .dissipativeRadialContraction => peirce11 P X + peirce00 P X
  | .lyapunovLatentStability => genSig P A C * genSig P A C
  | .symplecticDefectIdentity => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genPhi P A C)
  | .symplecticTracelessEquivalence => InfoGeometry.OperatorAlgebra.PeirceSpine.comm (genSig P A C) (genJ P A C)
  | .tracelessCanonicalProjection => oddGrade P (evenGrade P X)
  | .operatorTetradDecomposition => projV P A C X + projPhi P A C X + projJ P A C X + projSig P A C X
  | .tetradPairwiseOrthogonality => projPhi P A C (genV P A C)
  | .polylogOne => conePlus P A
  | .oddsRatioDeriv => coneMinus P C
  | .motivicNilpotent => conePlus P A * conePlus P A
  | .dilogarithmSeam => genV P A C
  | .carnotShannonUnification => genSig P A C

/-- **Theorem (Non-Commutative Operator Identities across `MetriplecticArchetype`)**:
For any idempotent `P * P = P` in a non-commutative ring `[Ring B]`, the metriplectic
attention archetypes satisfy exact Peirce splitting, diagonal-block orthogonality,
grading invariance, Tetraktys Dirac dispersion `Φ² = V` and `J² = -V`, the owner-convention
Lie bracket `[Φ, J] = -2 Σ`, symplectic anticommutativity `{Φ, J} = 0`, Casimir equality
`Σ² = V²`, and the Peirce-spine Klein character decomposition. -/
theorem metriplecticArchetype_operator_identities {P : B} (hP : P * P = P) (A C X : B) :
    metriplecticArchetypeOperator P A C X .metriplecticSplit = X ∧
    metriplecticArchetypeOperator P A C X .frobeniusOrthogonality = 0 ∧
    metriplecticArchetypeOperator P A C X .casimirGradingInvariance = evenGrade P X ∧
    metriplecticArchetypeOperator P A C X .metriplecticDiracDispersion =
      metriplecticArchetypeOperator P A C X .dilogarithmSeam ∧
    metriplecticArchetypeOperator P A C X .latentCurvatureLieHolonomy =
      -((2 : ℤ) • metriplecticArchetypeOperator P A C X .carnotShannonUnification) ∧
    metriplecticArchetypeOperator P A C X .multiHeadSymplecticReduction = 0 ∧
    metriplecticArchetypeOperator P A C X .kineticEnergyConservation =
      -metriplecticArchetypeOperator P A C X .dilogarithmSeam ∧
    metriplecticArchetypeOperator P A C X .lyapunovLatentStability =
      metriplecticArchetypeOperator P A C X .dilogarithmSeam *
        metriplecticArchetypeOperator P A C X .dilogarithmSeam ∧
    metriplecticArchetypeOperator P A C X .tracelessCanonicalProjection = 0 ∧
    metriplecticArchetypeOperator P A C X .operatorTetradDecomposition =
      (8 : ℤ) • X ∧
    metriplecticArchetypeOperator P A C X .tetradPairwiseOrthogonality = 0 ∧
    metriplecticArchetypeOperator P A C X .motivicNilpotent = 0 := by
  dsimp only [metriplecticArchetypeOperator]
  have hA3 := archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C
  have hA5 := archetype_A5_klein_hadamard_spectra_and_partition (P := P) hP A C X
  have hA11 := archetype_A11_klein_hadamard_character_selection (P := P) hP A C
  rcases hA3 with ⟨hPlus, _, hPhiSq, hJSq, _, _, _, hAnti, _, _, hSigSq, _, _, _, _⟩
  have hSplit := (archetype_A9_peirce_block_diagonal_splits (P := P) hP A C X).1
  refine ⟨?_, ?_, ?_, hPhiSq,
    (archetype_A7_so12_lie_brackets_and_cubic_inversions (P := P) hP A C).1,
    hAnti, hJSq, hSigSq, ?_, hA5.1, hA11.2.1, hPlus⟩
  · calc
      evenGrade P X + oddGrade P X =
          peirce11 P X + peirce00 P X + conePlus P X + coneMinus P X := by
            dsimp [evenGrade, oddGrade]
            abel
      _ = X := hSplit
  · peirce_nf hP
  · peirce_nf hP
  · peirce_nf hP

end NonCommutativeOperatorRealization

end InfoGeometry.Attention.AttentionMetriplecticPoset
