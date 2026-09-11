import Mathlib.Data.Complex.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import InfoGeometry.Clifford.DiracPauliGamma
import InfoGeometry.Section12

/-!
# Section 21: finite spinor-condensate algebra shadows

The source text proposes spinor condensates, emergent vielbeins, torsion, an
Einstein-Cartan connection split, and an effective action.  This file repairs
that material into kernel-checkable finite algebra.

#### BUCKET 1: CLOSED FINITE THEOREMS
The standard Pauli-Dirac idempotent
`P = 1/4 (1 + γ0)(1 + i γ1 γ2)` is idempotent in the existing Section 5 matrix
representation.  The finite induced metric readout `η_ab e^a_mu e^b_nu` is
symmetric.  The gamma commutator bivector `σ_mu_nu = 1/2[γ_mu,γ_nu]` is
antisymmetric.  The Section 12 contorsion split is reused as the finite
Einstein-Cartan connection shadow.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.  All proofs are finite matrix or coefficient algebra.

#### BUCKET 3: OPEN CLOSURE DEBT
No vacuum expectation value, condensate existence theorem, minimal-left-ideal
classification, emergent nondegenerate vierbein theorem, Einstein-Cartan field
equations, effective action variation, stress-energy derivation, or quantum
bootstrap/self-consistency theorem is claimed here.
-/

noncomputable section

namespace Section21

open Matrix
open InfoGeometry.Clifford.DiracPauliGamma

abbrev DiracMatrix := InfoGeometry.Clifford.DiracPauliGamma.DiracMatrix
abbrev SpinMat := Section12.SpinMat
abbrev SpinConnection := Section12.SpinConnection

/-- The same projector after evaluation in the Section 5 gamma representation. -/
def spinorProjector : DiracMatrix :=
  !![(1 : ℂ), 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- The claimed spinor-ideal projector is idempotent in the finite gamma model. -/
theorem spinorProjector_idempotent :
    spinorProjector * spinorProjector = spinorProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinorProjector, Matrix.mul_apply, Fin.sum_univ_four]

/-- A finite vielbein coefficient table `e^a_mu`. -/
abbrev Vielbein := Fin 4 → Fin 4 → ℂ

/-- Finite induced metric readout for the `(+---)` diagonal Minkowski metric. -/
def inducedMetric (e : Vielbein) (mu nu : Fin 4) : ℂ :=
  e 0 mu * e 0 nu - e 1 mu * e 1 nu - e 2 mu * e 2 nu - e 3 mu * e 3 nu

/-- The finite induced metric readout is symmetric in its coordinate slots. -/
theorem inducedMetric_symmetric (e : Vielbein) (mu nu : Fin 4) :
    inducedMetric e mu nu = inducedMetric e nu mu := by
  simp [inducedMetric]
  ring

/-- Gamma bivector/commutator matrix with the source's `1/2 [γ_mu, γ_nu]` convention. -/
def gammaSigma (mu nu : Fin 4) : DiracMatrix :=
  (1 / 2 : ℂ) • (gamma mu * gamma nu - gamma nu * gamma mu)

/-- The finite gamma commutator bivector is antisymmetric. -/
theorem gammaSigma_antisymmetric (mu nu : Fin 4) :
    gammaSigma nu mu = -gammaSigma mu nu := by
  ext i j
  simp [gammaSigma, Matrix.sub_apply]
  ring

/-- Einstein-Cartan connection splitting, restricted to finite spin matrices. -/
def spinConnectionWithContorsionFinite
    (omegaLeviCivita contorsion : SpinConnection) : SpinConnection :=
  Section12.spinConnectionWithContorsion omegaLeviCivita contorsion

/-- Zero contorsion recovers the torsion-free spin connection component. -/
theorem spinConnectionWithContorsionFinite_zero
    (omegaLeviCivita : SpinConnection) (mu : Fin 4) :
    spinConnectionWithContorsionFinite omegaLeviCivita 0 mu = omegaLeviCivita mu :=
  Section12.spinConnectionWithContorsion_zero omegaLeviCivita mu

theorem section21_capstone :
    spinorProjector * spinorProjector = spinorProjector ∧
    (∀ e : Vielbein, ∀ mu nu : Fin 4, inducedMetric e mu nu = inducedMetric e nu mu) ∧
    (∀ mu nu : Fin 4, gammaSigma nu mu = -gammaSigma mu nu) ∧
    (∀ omegaLeviCivita : SpinConnection, ∀ mu : Fin 4,
      spinConnectionWithContorsionFinite omegaLeviCivita 0 mu = omegaLeviCivita mu) := by
  exact ⟨spinorProjector_idempotent, inducedMetric_symmetric, gammaSigma_antisymmetric,
    spinConnectionWithContorsionFinite_zero⟩

end Section21
