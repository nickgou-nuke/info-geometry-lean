import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Canonical.RelativeModularHamiltonian
import InfoGeometry.Canonical.StandardFormCore
import InfoGeometry.Meta.Architecture

open scoped BigOperators InnerProductSpace

/-!
# InfoGeometry.Canonical.FirstQuantizationProbability

Finite first-quantization dictionary for probability data in the modular lane.

This module packages the three substitutions as compiled surfaces:

1. classical density ratio `λ` -> relative modular operator `Δ`,
2. classical surprisal `-log λ` -> relative modular Hamiltonian `K = -log Δ`,
3. classical expectation -> operator/vacuum expectation pairing.
-/

namespace InfoGeometry.Canonical.FirstQuantizationProbability

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativePotentialCore
open InfoGeometry.Canonical.RelativeModularOperator
open InfoGeometry.Canonical.RelativeModularHamiltonian
open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.Canonical.StandardFormCore
open InfoGeometry.MaxEnt.JaynesInfoStatMech.ThermalDiagonal

section FiniteDictionary

variable {n : ℕ} [Nonempty (Fin n)]

/-- Classical density-ratio observable `λ = p/q` on a finite carrier. -/
@[rep_depth projective]
noncomputable def classicalDensityRatio
    (q q0 : PositiveRay (Fin n)) : Fin n → ℝ :=
  fun i => relativeDensity (α := Fin n) q q0 i

/-- Classical surprisal of the density ratio, pointwise: `-log λ`. -/
@[rep_depth projective]
noncomputable def classicalSurprisal
    (q q0 : PositiveRay (Fin n)) : Fin n → ℝ :=
  fun i => -Real.log (classicalDensityRatio (n := n) q q0 i)

/-- First quantization of the classical density-ratio observable. -/
@[rep_depth operator]
noncomputable def quantizedDensityRatioOperator
    (q q0 : PositiveRay (Fin n)) : FinMat n :=
  firstQuantize (n := n) (classicalDensityRatio (n := n) q q0)

/-- `λ -> Δ`: first-quantized density ratio is exactly the relative modular operator. -/
@[rep_depth operator]
theorem quantizedDensityRatioOperator_eq_relativeModularOperator
    (q q0 : PositiveRay (Fin n)) :
    quantizedDensityRatioOperator (n := n) q q0
      = relativeModularOperator (n := n) q q0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [quantizedDensityRatioOperator, firstQuantize_apply_diag]
    rw [classicalDensityRatio]
    rw [relativeModularOperator_diag]
  · rw [quantizedDensityRatioOperator, firstQuantize_apply_offdiag (n := n) (hij := hij)]
    rw [relativeModularOperator_offdiag (n := n) (q := q) (q0 := q0) (hij := hij)]

/-- Pointwise classical surprisal coincides with relative modular potential. -/
@[rep_depth projective, simp]
theorem classicalSurprisal_eq_relativeModularPotential
    (q q0 : PositiveRay (Fin n)) (i : Fin n) :
    classicalSurprisal (n := n) q q0 i =
      relativeModularPotential (α := Fin n) q q0 i := by
  unfold classicalSurprisal classicalDensityRatio
  rw [relativeDensity_eq_exp_relativeLogDensity]
  rw [Real.log_exp]
  rw [relativeModularPotential_eq_neg_relativeLogDensity]

/-- First quantization of classical surprisal `-log λ`. -/
@[rep_depth operator]
noncomputable def quantizedSurprisalOperator
    (q q0 : PositiveRay (Fin n)) : FinMat n :=
  firstQuantize (n := n) (classicalSurprisal (n := n) q q0)

/-- `-log λ` first-quantized equals the relative modular-potential operator. -/
@[rep_depth operator]
theorem quantizedSurprisalOperator_eq_relativeModularPotentialOperator
    (q q0 : PositiveRay (Fin n)) :
    quantizedSurprisalOperator (n := n) q q0
      = relativeModularPotentialOperator (n := n) q q0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [quantizedSurprisalOperator, firstQuantize_apply_diag]
    rw [classicalSurprisal_eq_relativeModularPotential (n := n) q q0]
    rw [relativeModularPotentialOperator_diag]
  · rw [quantizedSurprisalOperator, firstQuantize_apply_offdiag (n := n) (hij := hij)]
    rw [relativeModularPotentialOperator]
    rw [firstQuantize_apply_offdiag (n := n) (hij := hij)]

/--
`-log λ -> K`: the finite relative modular Hamiltonian operator is exactly the
first-quantized surprisal of the density ratio.
-/
@[rep_depth operator]
theorem relativeModularHamiltonianOperator_eq_quantizedSurprisalOperator
    (q q0 : PositiveRay (Fin n)) :
    relativeModularHamiltonianOperator (n := n) q q0
      = quantizedSurprisalOperator (n := n) q q0 := by
  calc
    relativeModularHamiltonianOperator (n := n) q q0
      = relativeModularPotentialOperator (n := n) q q0 := by
          ext i j
          by_cases hij : i = j
          · subst hij
            rw [relativeModularHamiltonianOperator_diag]
            rw [relativeModularPotentialOperator_diag]
          · rw [relativeModularHamiltonianOperator_offdiag (n := n) (q := q) (q0 := q0) (hij := hij)]
            rw [relativeModularPotentialOperator]
            rw [firstQuantize_apply_offdiag (n := n) (hij := hij)]
    _ = quantizedSurprisalOperator (n := n) q q0 := by
          symm
          exact quantizedSurprisalOperator_eq_relativeModularPotentialOperator (n := n) q q0

end FiniteDictionary

section ClassicalExpectation

variable {n : ℕ}

/-- Classical expectation on a finite probability law. -/
@[rep_depth projective]
noncomputable def classicalExpectation
    (p : InfoGeometry.FinProb (Fin n)) (a : Fin n → ℝ) : ℝ :=
  InfoGeometry.expectation p a

 /-- `∫ p(...)` equals diagonal operator expectation of the first quantization. -/
@[rep_depth operator]
theorem classicalExpectation_eq_diagonalExpectation_firstQuantize
    (p : InfoGeometry.FinProb (Fin n)) (a : Fin n → ℝ) :
    classicalExpectation (n := n) p a
      = diagonalExpectation p (firstQuantize (n := n) a) := by
  unfold classicalExpectation InfoGeometry.expectation
  symm
  exact diagonalExpectation_firstQuantize (n := n) p a

end ClassicalExpectation

section VacuumExpectation

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H

/-- Vacuum-style operator expectation pairing on the doubled carrier. -/
@[rep_depth krein]
noncomputable abbrev vacuumExpectation (Φ : VectorState H) (A : EndH) : ℝ :=
  Φ.expectation A

/-- Vacuum expectation is exactly the inner pairing `⟪AΦ, Φ⟫`. -/
@[rep_depth krein, simp]
theorem vacuumExpectation_eq_inner (Φ : VectorState H) (A : EndH) :
    vacuumExpectation Φ A = ⟪A Φ.vector, Φ.vector⟫_ℝ := rfl

end VacuumExpectation

section DictionaryPackage

variable {n : ℕ} [Nonempty (Fin n)]
variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "EndH" => InfoGeometry.Volume.ConnesCocycle.AlgebraEnd H

/--
Compiled package of the first-quantization substitutions:
- `λ -> Δ`,
- `-log λ -> K`,
- expectation -> vacuum pairing.
-/
@[rep_depth thermo, capstone]
theorem firstQuantization_dictionary
    (q q0 : PositiveRay (Fin n))
    (Φ : VectorState H) (A : EndH) :
    quantizedDensityRatioOperator (n := n) q q0 = relativeModularOperator (n := n) q q0
      ∧ relativeModularHamiltonianOperator (n := n) q q0
          = quantizedSurprisalOperator (n := n) q q0
      ∧ vacuumExpectation Φ A = ⟪A Φ.vector, Φ.vector⟫_ℝ := by
  refine ⟨?_, ?_, ?_⟩
  · exact quantizedDensityRatioOperator_eq_relativeModularOperator (n := n) q q0
  · exact relativeModularHamiltonianOperator_eq_quantizedSurprisalOperator (n := n) q q0
  · exact vacuumExpectation_eq_inner (H := H) Φ A

end DictionaryPackage

end InfoGeometry.Canonical.FirstQuantizationProbability
