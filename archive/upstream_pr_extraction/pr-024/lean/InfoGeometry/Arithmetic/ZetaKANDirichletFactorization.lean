import Mathlib
import InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
import InfoGeometry.Dynamics.KanDecomposition

/-!
# InfoGeometry.Arithmetic.ZetaKANDirichletFactorization

Scalar KAN readout of the centered Dirichlet mode.

The matrix KAN owner is `InfoGeometry.Dynamics.KanDecomposition`.  This file
does not reprove a global Iwasawa theorem.  It records the one-dimensional
character seen by the zeta summand

`exp(-L/2) * exp(-uL) * exp(-ivL)`.

In this scalar character:
* `K` is the compact phase wave;
* `A` is the abelian scale envelope;
* `N` acts trivially on the scalar Dirichlet mode, while the genuine unipotent
  matrix `N` remains the existing `componentN` corridor.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.ZetaKANDirichletFactorization

open Matrix
open InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions
open InfoGeometry.Arithmetic.ZetaCoordinateSymmetry.ZetaAffineChart.ZetaCenteredChart
open InfoGeometry.Dynamics.KanDecomposition

/-- Local abbreviation for the owner centered zeta chart. -/
abbrev CenteredChart :=
  InfoGeometry.Arithmetic.ZetaSymmetryAdaptedDefinitions.CenteredChart

/-! ## Scalar KAN characters for a centered Dirichlet mode -/

/-- Compact `K` character: the unitary phase wave along the critical line. -/
def scalarKCharacter (L : ℝ) (x : CenteredChart) : ℂ :=
  phaseWave L x.v

/-- Abelian `A` character: the scale-normal envelope away from the critical line. -/
def scalarACharacter (L : ℝ) (x : CenteredChart) : ℂ :=
  scaleEnvelope L x.u

/--
Scalar `N` character for Dirichlet modes.

The parabolic `N` matrix is nontrivial in the KAN owner.  The one-dimensional
Dirichlet character used here is blind to that shear, so its scalar readout is
the trivial character.
-/
def scalarNCharacter (_η : ℂ) : ℂ :=
  1

/-- Central half-density weight `exp(-L/2)` from the marked pair midpoint. -/
def scalarHalfDensity (L : ℝ) : ℂ :=
  criticalLineWeight L

/-- KAN-ordered scalar Dirichlet product. -/
def scalarKANDirichletProduct (L : ℝ) (x : CenteredChart) (η : ℂ) : ℂ :=
  scalarHalfDensity L * scalarKCharacter L x * scalarACharacter L x * scalarNCharacter η

@[simp] theorem scalarNCharacter_eq_one (η : ℂ) :
    scalarNCharacter η = 1 := rfl

@[simp] theorem scalarACharacter_of_criticalLine
    {L : ℝ} {x : CenteredChart} (hx : centeredCriticalLine x) :
    scalarACharacter L x = 1 := by
  rw [scalarACharacter, scaleEnvelope]
  rw [show x.u = 0 from hx]
  simp

@[simp] theorem scalarKCharacter_zero_height (L u : ℝ) :
    scalarKCharacter L ⟨u, 0⟩ = 1 := by
  simp [scalarKCharacter, phaseWave]

/--
The centered Dirichlet mode is exactly the scalar KAN character, with the
canonical half-density factor included.
-/
theorem scalarKANDirichletProduct_eq_centeredDirichletMode
    (L : ℝ) (x : CenteredChart) (η : ℂ) :
    scalarKANDirichletProduct L x η = centeredDirichletMode L x := by
  simp [scalarKANDirichletProduct, scalarHalfDensity, scalarKCharacter,
    scalarACharacter, scalarNCharacter, centeredDirichletMode]
  ring

/-- On the critical line, the `A` component drops out of the KAN scalar readout. -/
theorem scalarKANDirichletProduct_of_criticalLine
    {L : ℝ} {x : CenteredChart} (η : ℂ) (hx : centeredCriticalLine x) :
    scalarKANDirichletProduct L x η =
      scalarHalfDensity L * scalarKCharacter L x := by
  simp [scalarKANDirichletProduct, hx]

/-! ## Compatibility with finite Dirichlet and Euler readouts -/

/-- Finite Dirichlet readout as a sum of scalar KAN characters. -/
theorem finiteDirichletReadout_eq_sum_scalarKAN {ι : Type*}
    (S : Finset ι) (logWeight : ι → ℝ) (x : CenteredChart) (η : ℂ) :
    finiteDirichletReadout S logWeight x =
      S.sum (fun i => scalarKANDirichletProduct (logWeight i) x η) := by
  apply Finset.sum_congr rfl
  intro i _hi
  exact (scalarKANDirichletProduct_eq_centeredDirichletMode (logWeight i) x η).symm

/-- Finite Euler factor as an inverse built from the scalar KAN character. -/
theorem finiteEulerFactor_eq_scalarKAN
    (L : ℝ) (x : CenteredChart) (η : ℂ) :
    finiteEulerFactor L x = (1 - scalarKANDirichletProduct L x η)⁻¹ := by
  rw [scalarKANDirichletProduct_eq_centeredDirichletMode]
  rfl

/-- Finite Euler product as a product of scalar KAN-character factors. -/
theorem finiteEulerProduct_eq_prod_scalarKAN {ι : Type*}
    (S : Finset ι) (logWeight : ι → ℝ) (x : CenteredChart) (η : ℂ) :
    finiteEulerProduct S logWeight x =
      S.prod (fun i => (1 - scalarKANDirichletProduct (logWeight i) x η)⁻¹) := by
  apply Finset.prod_congr rfl
  intro i _hi
  exact finiteEulerFactor_eq_scalarKAN (logWeight i) x η

/-! ## Link back to the matrix KAN owner -/

/-- The genuine parabolic `N` matrix is trivial at zero shear. -/
theorem componentN_zero_eq_one :
    componentN 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [componentN_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The genuine parabolic `N` corridor composes by adding shear parameters. -/
theorem componentN_additive_shear (η θ : ℂ) :
    componentN η * componentN θ = componentN (η + θ) :=
  componentN_composition η θ

/-- The full matrix KAN product remains determinant one at every scalar-mode shear. -/
theorem kanProduct_det_one_for_dirichlet_shear
    (θ lam η : ℂ) :
    (kanProduct θ lam η).det = 1 :=
  kanProduct_det_eq_one θ lam η

end InfoGeometry.Arithmetic.ZetaKANDirichletFactorization
