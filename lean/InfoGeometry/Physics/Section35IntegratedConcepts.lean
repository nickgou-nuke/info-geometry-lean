import InfoGeometry.Physics.Section34StrengthenedFormalism

/-!
# Section 35 repaired: integrated finite concepts

The source integrates complex rapidities, phase/spin, mixed states, Kähler
language, chirality, and conformal-coordinate Einstein/Dirac equations into the
quaternionic-emergent-spacetime story.

The theorem-safe repaired content is finite algebra only:

* the operator `I + r n·σ` is exactly twice the radius-`r` Bloch density;
* the density determinant and spacetime determinant are governed by the same
  algebraic residual `1 - r²(n₁²+n₂²+n₃²)`;
* the boundary/pure/null case is the residual-zero specialization already
  developed in Sections 32--34;
* a finite biquaternion-pair `j`-conjugation flips the dual component, is an
  involution, preserves a quadratic trace shadow, and flips a linear chiral
  asymmetry readout.

No theorem is asserted about entropy/time dilation, Planck discreteness,
Kähler manifolds, electroweak chirality, Einstein equations, Dirac PDEs,
Lorentz/conformal exponentials, or physical emergence.
-/

noncomputable section

namespace Section35IntegratedConcepts

open Matrix Complex
open InfoGeometry.Canonical.UnifiedMatrixQuantumGeometryFinite
open InfoGeometry.Physics.Section32QuaternionicEmergentSpacetime
open InfoGeometry.Physics.Section33PauliBiquaternionCompletion

/-- Finite spin-spacetime operator `I + r n·σ`. -/
def spinSpacetimeOperator (r n1 n2 n3 : ℂ) : Mat2 :=
  σ0 + (r * n1) • σ1 + (r * n2) • σ2 + (r * n3) • σ3

/-- The spin-spacetime operator is exactly twice the associated Bloch density. -/
theorem spinSpacetimeOperator_eq_two_density (r n1 n2 n3 : ℂ) :
    spinSpacetimeOperator r n1 n2 n3 =
      (2 : ℂ) • blochDensityAtRadius r n1 n2 n3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSpacetimeOperator, blochDensityAtRadius, densityMatrix,
      σ0, σ1, σ2, σ3]
  all_goals ring

/-- Algebraic residual distinguishing boundary/null from interior/timelike shadows. -/
def blochResidual (r n1 n2 n3 : ℂ) : ℂ :=
  1 - r ^ 2 * (n1 ^ 2 + n2 ^ 2 + n3 ^ 2)

/-- Density determinant is one quarter of the Bloch residual. -/
theorem blochDensityAtRadius_det_eq_residual (r n1 n2 n3 : ℂ) :
    (blochDensityAtRadius r n1 n2 n3).det =
      (1 / 4 : ℂ) * blochResidual r n1 n2 n3 := by
  rw [blochDensityAtRadius, densityMatrix_det]
  unfold blochResidual
  ring

/-- The Section 32 spacetime point determinant is `t²` times the same residual. -/
theorem blochSpacetimePoint_det_eq_t_sq_residual (t r n1 n2 n3 : ℂ) :
    (blochSpacetimePoint t r n1 n2 n3).det =
      t ^ 2 * blochResidual r n1 n2 n3 := by
  rw [blochSpacetimePoint_det]
  rfl

/-- Residual zero gives the pure-density determinant-zero certificate. -/
theorem blochDensityAtRadius_det_zero_of_residual_zero (r n1 n2 n3 : ℂ)
    (hres : blochResidual r n1 n2 n3 = 0) :
    (blochDensityAtRadius r n1 n2 n3).det = 0 := by
  rw [blochDensityAtRadius_det_eq_residual, hres]
  ring

/-- Residual zero gives the null-spacetime determinant-zero certificate. -/
theorem blochSpacetimePoint_det_zero_of_residual_zero (t r n1 n2 n3 : ℂ)
    (hres : blochResidual r n1 n2 n3 = 0) :
    (blochSpacetimePoint t r n1 n2 n3).det = 0 := by
  rw [blochSpacetimePoint_det_eq_t_sq_residual, hres]
  ring

/-! ## Finite biquaternion dual/chiral shadow -/

/-- Finite `j`-conjugation on a biquaternion pair: keep primal, flip dual. -/
def dualConj (q : BiquaternionPair) : BiquaternionPair :=
  { primal := q.primal, dual := -q.dual }

/-- Quadratic trace shadow preserved by dual conjugation. -/
def pairQuadraticTrace (q : BiquaternionPair) : ℂ :=
  trace (q.primal * q.primal) + trace (q.dual * q.dual)

/-- Linear dual-component readout used as a finite chiral-asymmetry shadow. -/
def chiralAsymmetryTrace (q : BiquaternionPair) : ℂ :=
  trace q.dual

/-- Dual conjugation is an involution. -/
theorem dualConj_involutive (q : BiquaternionPair) :
    dualConj (dualConj q) = q := by
  cases q
  simp [dualConj]

/-- The quadratic trace shadow is invariant under dual conjugation. -/
theorem pairQuadraticTrace_dualConj (q : BiquaternionPair) :
    pairQuadraticTrace (dualConj q) = pairQuadraticTrace q := by
  cases q
  simp [pairQuadraticTrace, dualConj]

/-- The linear chiral-asymmetry shadow flips sign under dual conjugation. -/
theorem chiralAsymmetryTrace_dualConj (q : BiquaternionPair) :
    chiralAsymmetryTrace (dualConj q) = -chiralAsymmetryTrace q := by
  cases q
  simp [chiralAsymmetryTrace, dualConj]

/-- Repaired Section 35 finite packet. -/
theorem repaired_section35_integrated_concepts_packet
    (t r n1 n2 n3 : ℂ) (q : BiquaternionPair) :
    spinSpacetimeOperator r n1 n2 n3 =
      (2 : ℂ) • blochDensityAtRadius r n1 n2 n3 ∧
    (blochDensityAtRadius r n1 n2 n3).det =
      (1 / 4 : ℂ) * blochResidual r n1 n2 n3 ∧
    (blochSpacetimePoint t r n1 n2 n3).det =
      t ^ 2 * blochResidual r n1 n2 n3 ∧
    dualConj (dualConj q) = q ∧
    pairQuadraticTrace (dualConj q) = pairQuadraticTrace q ∧
    chiralAsymmetryTrace (dualConj q) = -chiralAsymmetryTrace q := by
  exact ⟨spinSpacetimeOperator_eq_two_density r n1 n2 n3,
    blochDensityAtRadius_det_eq_residual r n1 n2 n3,
    blochSpacetimePoint_det_eq_t_sq_residual t r n1 n2 n3,
    dualConj_involutive q,
    pairQuadraticTrace_dualConj q,
    chiralAsymmetryTrace_dualConj q⟩

end Section35IntegratedConcepts

end noncomputable section
