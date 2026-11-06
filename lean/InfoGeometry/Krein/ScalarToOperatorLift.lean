/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Scalar-to-Operator Lifting: Scalars as Central Operators

This module formalizes the foundational ontology shift: scalars are lifted to
operators. The map `r ↦ r • id_H` embeds the scalar field `ℝ` as central
scalar multiples of the identity operator inside the bounded operator algebra
`B(H)`. This makes the operator algebra a `ℝ`-algebra whose center contains
all scalars, so every Lean formalization, Mathlib theorem prover can benefit
from this formalization.

## Contents

1. **`scalarToOperator`**: The unital ring homomorphism `ℝ → B(H)`,
   `r ↦ r • id_H`.
2. **`scalarToOperator_center`**: The image of `ℝ` lies in the center of `B(H)`
   — scalars commute with every operator.
3. **`kreinInner_scalarOperator`**: The Krein pairing respects scalar
   multiplication: `[r•u, v]_J = r·[u,v]_J` and `[u, r•v]_J = r·[u,v]_J`.
4. **`mcJet_scalarLift`**: Lifting a Maurer–Cartan jet's scalar entries to
   scalar operators preserves the Krein-skew-adjointness of every component.
-/

open InfoGeometry.Synthesis.MajoranaParaKahlerMaurerCartanSupercolorSynthesis
open InfoGeometry.Krein
open InfoGeometry.Krein.KreinSpace

section ScalarToOperatorLift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Scalar-to-operator embedding: `r ↦ r • id_H` as a bounded linear operator.
This is the foundational map that promotes scalars to central operators,
making `B(H)` a `ℝ`-algebra whose center contains all scalars. -/
def scalarToOperator (r : ℝ) : H →L[ℝ] H :=
  (r : ℝ) • ContinuousLinearMap.id ℝ H

/-- The scalar-to-operator map is a unital ring homomorphism `ℝ → B(H)`:
   `scalarToOperator (r + s) = scalarToOperator r + scalarToOperator s`,
   `scalarToOperator (r * s) = scalarToOperator r * scalarToOperator s`,
   `scalarToOperator 1 = id`. -/
theorem scalarToOperator_ringHom (r s : ℝ) :
    scalarToOperator (H := H) (r + s) = scalarToOperator (H := H) r + scalarToOperator (H := H) s ∧
    scalarToOperator (H := H) (r * s) = scalarToOperator (H := H) r * scalarToOperator (H := H) s ∧
    scalarToOperator (H := H) (1 : ℝ) = ContinuousLinearMap.id ℝ H := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp [scalarToOperator, add_smul]
  · ext x
    simp [scalarToOperator, ContinuousLinearMap.mul_def, mul_smul]
    exact smul_comm r s x
  · ext x
    simp [scalarToOperator]

/-- The image of `ℝ` under `scalarToOperator` lies in the center of `B(H)`:
   scalars commute with every operator. -/
theorem scalarToOperator_center (r : ℝ) (A : H →L[ℝ] H) :
    scalarToOperator (H := H) r * A = A * scalarToOperator (H := H) r := by
  ext x
  simp [scalarToOperator, ContinuousLinearMap.mul_def]

/-- The Krein pairing respects scalar multiplication:
   `[r•u, v]_J = r·[u,v]_J` and `[u, r•v]_J = r·[u,v]_J`. -/
theorem kreinInner_scalarOperator [CompleteSpace H] [KreinSpace H]
    (r : ℝ) (u v : H) :
    kreinInner ((r : ℝ) • u) v = r * kreinInner u v ∧
    kreinInner u ((r : ℝ) • v) = r * kreinInner u v :=
  ⟨kreinInner_smul_left r u v, kreinInner_smul_right r u v⟩

/-- Lift a Maurer–Cartan jet's scalar entries to scalar operators.
   Given a jet over `ℝ`, produce a jet over `B(H)` by sending each scalar
   entry `c : ℝ` to `c • id_H : B(H)`. -/
def mcJet_scalarLift (jet : FiveGradedMaurerCartanJet ℝ) : FiveGradedMaurerCartanJet (H →L[ℝ] H) :=
  { dOmega_m2 := jet.dOmega_m2 • ContinuousLinearMap.id ℝ H
  , dOmega_m1 := jet.dOmega_m1 • ContinuousLinearMap.id ℝ H
  , dOmega_0 := jet.dOmega_0 • ContinuousLinearMap.id ℝ H
  , dOmega_p1 := jet.dOmega_p1 • ContinuousLinearMap.id ℝ H
  , dOmega_p2 := jet.dOmega_p2 • ContinuousLinearMap.id ℝ H
  , br_0_m2 := jet.br_0_m2 • ContinuousLinearMap.id ℝ H
  , br_m1_m1_half := jet.br_m1_m1_half • ContinuousLinearMap.id ℝ H
  , br_0_m1 := jet.br_0_m1 • ContinuousLinearMap.id ℝ H
  , br_p1_m2 := jet.br_p1_m2 • ContinuousLinearMap.id ℝ H
  , br_0_0_half := jet.br_0_0_half • ContinuousLinearMap.id ℝ H
  , br_m1_p1 := jet.br_m1_p1 • ContinuousLinearMap.id ℝ H
  , br_m2_p2 := jet.br_m2_p2 • ContinuousLinearMap.id ℝ H
  , br_0_p1 := jet.br_0_p1 • ContinuousLinearMap.id ℝ H
  , br_m1_p2 := jet.br_m1_p2 • ContinuousLinearMap.id ℝ H
  , br_0_p2 := jet.br_0_p2 • ContinuousLinearMap.id ℝ H
  , br_p1_p1_half := jet.br_p1_p1_half • ContinuousLinearMap.id ℝ H }

/-- Every entry of a scalar-lifted jet is Krein-self-adjoint (not skew-adjoint,
   since real scalars are self-adjoint). This is the operator-algebra version
   of "scalars are central": they commute with the Krein involution. -/
theorem mcJet_scalarLift_selfAdjoint [CompleteSpace H] [KreinSpace H]
  (jet : FiveGradedMaurerCartanJet ℝ) :
    IsKreinSelfAdjoint (jet.dOmega_m2 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.dOmega_m1 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.dOmega_0 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.dOmega_p1 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.dOmega_p2 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_0_m2 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_m1_m1_half • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_0_m1 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_p1_m2 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_0_0_half • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_m1_p1 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_m2_p2 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_0_p1 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_m1_p2 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_0_p2 • ContinuousLinearMap.id ℝ H) ∧
    IsKreinSelfAdjoint (jet.br_p1_p1_half • ContinuousLinearMap.id ℝ H) := by
  have h (r : ℝ) : IsKreinSelfAdjoint (r • ContinuousLinearMap.id ℝ H) := by
    simp [IsKreinSelfAdjoint, kreinAdjoint_smul, kreinAdjoint_id]
  refine ⟨h jet.dOmega_m2, h jet.dOmega_m1, h jet.dOmega_0, h jet.dOmega_p1,
    h jet.dOmega_p2, h jet.br_0_m2, h jet.br_m1_m1_half, h jet.br_0_m1,
    h jet.br_p1_m2, h jet.br_0_0_half, h jet.br_m1_p1, h jet.br_m2_p2,
    h jet.br_0_p1, h jet.br_m1_p2, h jet.br_0_p2, h jet.br_p1_p1_half⟩

end ScalarToOperatorLift
