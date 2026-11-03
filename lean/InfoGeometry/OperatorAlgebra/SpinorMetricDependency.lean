/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Star.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Basic
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.OperatorAlgebra.SpinorMetricDependency

inductive Archetype
  | matrixTower
  | faithfulTrace
  | isometricTransitions
  | dualTangentSpace
  | positiveDensity
  | sldInverse
  | traceMetric
  deriving DecidableEq

open Archetype

instance : Fintype Archetype where
  elems := {matrixTower, faithfulTrace, isometricTransitions, dualTangentSpace, positiveDensity, sldInverse, traceMetric}
  complete := by rintro (_ | _ | _ | _ | _ | _ | _) <;> simp

def prerequisites : Archetype → Finset Archetype
  | matrixTower => {matrixTower}
  | faithfulTrace => {matrixTower, faithfulTrace}
  | isometricTransitions => {matrixTower, faithfulTrace, isometricTransitions}
  | dualTangentSpace => {dualTangentSpace}
  | positiveDensity => {positiveDensity}
  | sldInverse => {positiveDensity, sldInverse}
  | traceMetric => {positiveDensity, sldInverse, traceMetric}

instance : PartialOrder Archetype where
  le earlier later := prerequisites earlier ⊆ prerequisites later
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ := Finset.Subset.trans
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

theorem tower_order : matrixTower ≤ faithfulTrace ∧ faithfulTrace ≤ isometricTransitions := by
  change prerequisites matrixTower ⊆ prerequisites faithfulTrace ∧
    prerequisites faithfulTrace ⊆ prerequisites isometricTransitions
  decide

theorem metric_order : positiveDensity ≤ sldInverse ∧ sldInverse ≤ traceMetric := by
  change prerequisites positiveDensity ⊆ prerequisites sldInverse ∧
    prerequisites sldInverse ⊆ prerequisites traceMetric
  decide

theorem independent_branches : ¬ isometricTransitions ≤ traceMetric ∧
    ¬ traceMetric ≤ isometricTransitions ∧ ¬ dualTangentSpace ≤ traceMetric := by
  change ¬ prerequisites isometricTransitions ⊆ prerequisites traceMetric ∧
    ¬ prerequisites traceMetric ⊆ prerequisites isometricTransitions ∧
    ¬ prerequisites dualTangentSpace ⊆ prerequisites traceMetric
  decide

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

/-- **Archetype 1 (`matrixTower`):**
Peirce corner embedding `X ↦ peirce11 P X = P X P` is a multiplicative ring homomorphism on
the upper diagonal block (`peirce11 P X * peirce11 P Y = peirce11 P (X * P * Y)`) and
annihilates the lower block `peirce00 P Z`. -/
theorem archetype_matrixTower_block_multiplicativity
    {P : B} (hP : P * P = P) (X Y Z : B) :
    peirce11 P X * peirce11 P Y = peirce11 P (X * P * Y) ∧
    peirce11 P X * peirce00 P Z = 0 ∧
    peirce00 P Z * peirce11 P X = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [peirce11, peirce00]; peirce_nf hP)

/-- **Archetype 2 (`faithfulTrace`):**
Diagonal Peirce block projection of `V = {N_+, N_-}` and `Σ = [N_+, N_-]` isolates the two
corner Gram operators `N_+ N_-` and `N_- N_+`. -/
theorem archetype_faithfulTrace_gram_blocks
    {P : B} (hP : P * P = P) (A C : B) :
    peirce11 P (genV P A C) = conePlus P A * coneMinus P C ∧
    peirce00 P (genV P A C) = coneMinus P C * conePlus P A ∧
    peirce11 P (genV P A C) + peirce00 P (genV P A C) = genV P A C ∧
    peirce11 P (genV P A C) - peirce00 P (genV P A C) = genSig P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [peirce11, peirce00]; peirce_nf hP)

/-- **Archetype 3 (`isometricTransitions`):**
Partial-isometry intertwining between the upper and lower Peirce blocks:
`N_+ * (N_- * N_+) = (N_+ * N_-) * N_+ = V * N_+` and
`N_- * (N_+ * N_-) = (N_- * N_+) * N_- = V * N_-`. -/
theorem archetype_isometricTransitions_corner_intertwining
    {P : B} (hP : P * P = P) (A C : B) :
    conePlus P A * (coneMinus P C * conePlus P A) = genV P A C * conePlus P A ∧
    coneMinus P C * (conePlus P A * coneMinus P C) = genV P A C * coneMinus P C ∧
    genV P A C * conePlus P A = conePlus P A * genV P A C ∧
    genV P A C * coneMinus P C = coneMinus P C * genV P A C := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 4 (`dualTangentSpace`):**
Dual tangent splitting into off-diagonal Hermitian (`Φ = N_+ + N_-`) and skew-Hermitian
(`J = N_+ - N_-`) tangent directions:
`Φ + J = 2 • N_+`, `Φ - J = 2 • N_-`, `{Φ, J} = 0`, and `[Φ, J] = -2 • Σ`. -/
theorem archetype_dualTangentSpace_chiral_splitting
    {P : B} (hP : P * P = P) (A C : B) :
    genPhi P A C + genJ P A C = (2 : ℤ) • conePlus P A ∧
    genPhi P A C - genJ P A C = (2 : ℤ) • coneMinus P C ∧
    anticomm (genPhi P A C) (genJ P A C) = 0 ∧
    comm (genPhi P A C) (genJ P A C) = -((2 : ℤ) • genSig P A C) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 5 (`positiveDensity`):**
In any `[StarRing B]` with `star P = P`, the symmetric Gram density
`V = N_+ N_+^* + N_+^* N_+` is self-adjoint (`star V = V`) and commutes with `P` (`[V, P] = 0`). -/
theorem archetype_positiveDensity_self_adjoint_gram
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A : B) :
    star (genV P A (star A)) = genV P A (star A) ∧
    comm (genV P A (star A)) P = 0 := by
  have h1 : star (conePlus P A) = coneMinus P (star A) := by
    simp only [conePlus, coneMinus, star_mul, star_sub, star_one, hPstar, mul_assoc]
  have h2 : star (coneMinus P (star A)) = conePlus P A := by
    simp only [conePlus, coneMinus, star_mul, star_sub, star_one, star_star, hPstar, mul_assoc]
  refine ⟨?_, by peirce_nf hP⟩
  simp only [genV, anticomm, star_add, star_mul, h1, h2]

/-- **Archetype 6 (`sldInverse`):**
Symmetric Logarithmic Derivative (SLD) Jordan anticommutator action of the density weight `V`
on the off-diagonal tangent basis `(Φ, J)`:
`{V, Φ} = 2 • (V * Φ) = 2 • (Φ * Φ * Φ)` and `{V, J} = 2 • (V * J) = -(2 • (J * J * J))`. -/
theorem archetype_sldInverse_jordan_anticommutator
    {P : B} (hP : P * P = P) (A C : B) :
    anticomm (genV P A C) (genPhi P A C) = (2 : ℤ) • (genV P A C * genPhi P A C) ∧
    anticomm (genV P A C) (genPhi P A C) = (2 : ℤ) • (genPhi P A C * genPhi P A C * genPhi P A C) ∧
    anticomm (genV P A C) (genJ P A C) = (2 : ℤ) • (genV P A C * genJ P A C) ∧
    anticomm (genV P A C) (genJ P A C) = -((2 : ℤ) • (genJ P A C * genJ P A C * genJ P A C)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> peirce_nf hP

/-- **Archetype 7 (`traceMetric`):**
Quadratic Bures/SLD metric identities linking the Jordan anticommutator `{V, ·}` with the
double-commutator Hessian `derivSqPhi` and `derivSqJ` on `(Φ, J)`:
`derivSqPhi P A C (genJ P A C) = -((2 : ℤ) • anticomm (genV P A C) (genJ P A C))` and
`derivSqJ P A C (genPhi P A C) = -((2 : ℤ) • anticomm (genV P A C) (genPhi P A C))`. -/
theorem archetype_traceMetric_bures_hessian_relation
    {P : B} (hP : P * P = P) (A C : B) :
    derivSqPhi P A C (genJ P A C) = -((2 : ℤ) • anticomm (genV P A C) (genJ P A C)) ∧
    derivSqJ P A C (genPhi P A C) = -((2 : ℤ) • anticomm (genV P A C) (genPhi P A C)) := by
  refine ⟨?_, ?_⟩ <;>
    (simp only [derivSqPhi, derivSqJ]; peirce_nf hP)

/-- **Master Synthesis (`spinor_metric_dependency_master_synthesis`):**
Unites the partial-order branch theorems with all seven `[Ring B] [StarRing B]`
non-commutative operator theorems. -/
theorem spinor_metric_dependency_master_synthesis
    [StarRing B] {P : B} (hP : P * P = P) (hPstar : star P = P) (A X Y Z : B) :
    (matrixTower ≤ faithfulTrace ∧ faithfulTrace ≤ isometricTransitions) ∧
    (positiveDensity ≤ sldInverse ∧ sldInverse ≤ traceMetric) ∧
    (peirce11 P X * peirce00 P Z = 0) ∧
    (peirce11 P (genV P A (star A)) - peirce00 P (genV P A (star A)) = genSig P A (star A)) ∧
    (conePlus P A * (coneMinus P (star A) * conePlus P A) = genV P A (star A) * conePlus P A) ∧
    (comm (genPhi P A (star A)) (genJ P A (star A)) = -((2 : ℤ) • genSig P A (star A))) ∧
    (star (genV P A (star A)) = genV P A (star A)) ∧
    (anticomm (genV P A (star A)) (genPhi P A (star A)) =
      (2 : ℤ) • (genV P A (star A) * genPhi P A (star A))) ∧
    (derivSqPhi P A (star A) (genJ P A (star A)) =
      -((2 : ℤ) • anticomm (genV P A (star A)) (genJ P A (star A)))) := by
  have h1 := archetype_matrixTower_block_multiplicativity hP X Y Z
  have h2 := archetype_faithfulTrace_gram_blocks hP A (star A)
  have h3 := archetype_isometricTransitions_corner_intertwining hP A (star A)
  have h4 := archetype_dualTangentSpace_chiral_splitting hP A (star A)
  have h5 := archetype_positiveDensity_self_adjoint_gram hP hPstar A
  have h6 := archetype_sldInverse_jordan_anticommutator hP A (star A)
  have h7 := archetype_traceMetric_bures_hessian_relation hP A (star A)
  exact ⟨tower_order, metric_order, h1.2.1, h2.2.2.2, h3.1, h4.2.2.2, h5.1, h6.1, h7.1⟩

end NonCommutativeOperatorRealization

end InfoGeometry.OperatorAlgebra.SpinorMetricDependency
