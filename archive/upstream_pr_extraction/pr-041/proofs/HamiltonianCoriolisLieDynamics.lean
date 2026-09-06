import proofs.GoutevTonevNuclearHamiltonian
import proofs.CoherentOrbitalPrecession

/-!
# Hamiltonian Coriolis / Lie-flow dynamics

This module turns the symbolic Goutev--Tonev Hamiltonian eigenvalue layer into
a minimal finite dynamics model:

* an eigenmode with energy `E` evolves by phase `exp(-iEt)`;
* two near-degenerate bands are modeled by a `2×2` Hamiltonian with diagonal
  energies and an off-diagonal Coriolis/Lie-flow coupling;
* the orbital-coherence correction `δ = λ_eff² Ξ` from
  `CoherentOrbitalPrecession` can be used as a dimensionless information-flow
  correction to a base energy.

This is deliberately finite and algebraic.
-/

noncomputable section

namespace HamiltonianCoriolisLieDynamics

open Matrix

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Schrödinger phase for an energy eigenmode. -/
def modePhase (E t : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (E * t : ℂ)))

@[simp] theorem modePhase_zero_time (E : ℝ) :
    modePhase E 0 = 1 := by
  simp [modePhase]

/-- Diagonal time evolution for two uncoupled energy eigenmodes. -/
def diagonalEvolution (E₁ E₂ t : ℝ) : M2C :=
  !![modePhase E₁ t, 0;
     0, modePhase E₂ t]

@[simp] theorem diagonalEvolution_zero_time (E₁ E₂ : ℝ) :
    diagonalEvolution E₁ E₂ 0 = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalEvolution]

/-- Two-level Hamiltonian with Coriolis/Lie-flow mixing. -/
def twoLevelHamiltonian (E₁ E₂ flow : ℝ) : M2C :=
  !![(E₁ : ℂ), (flow : ℂ);
     (flow : ℂ), (E₂ : ℂ)]

@[simp] theorem twoLevelHamiltonian_trace (E₁ E₂ flow : ℝ) :
    Matrix.trace (twoLevelHamiltonian E₁ E₂ flow) = (E₁ + E₂ : ℂ) := by
  simp [twoLevelHamiltonian, Matrix.trace_fin_two]

@[simp] theorem twoLevelHamiltonian_zero_flow_diagonal (E₁ E₂ : ℝ) :
    twoLevelHamiltonian E₁ E₂ 0 = !![(E₁ : ℂ), 0; 0, (E₂ : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoLevelHamiltonian]

/-- Coherence/Lie-flow corrected energy: `E -> E(1+λ_eff²Ξ)`. -/
def flowCorrectedEnergy (E lambdaEff Xi : ℝ) : ℝ :=
  E * (1 + CoherentOrbitalPrecession.fractionalCorrection lambdaEff Xi)

@[simp] theorem fractionalCorrection_eq_square (lambdaEff Xi : ℝ) :
    CoherentOrbitalPrecession.fractionalCorrection lambdaEff Xi =
      lambdaEff ^ 2 * Xi := by
  rfl

@[simp] theorem flowCorrectedEnergy_zero_lambda (E Xi : ℝ) :
    flowCorrectedEnergy E 0 Xi = E := by
  simp [flowCorrectedEnergy]

/-- A compact scalar coupling combining orbital Lie-flow asymmetry with the
existing odd-mass Coriolis decoupling term. -/
def coriolisLieCoupling
    (lambdaEff Xi a inertiaScale : ℝ)
    (s : GoutevTonevNuclearHamiltonian.SpectroscopyState) : ℝ :=
  CoherentOrbitalPrecession.fractionalCorrection lambdaEff Xi +
    GoutevTonevNuclearHamiltonian.coriolisEnergy a inertiaScale s

@[simp] theorem coriolisLieCoupling_zeroes
    (s : GoutevTonevNuclearHamiltonian.SpectroscopyState)
    (hK : s.k2 ≠ 1) :
    coriolisLieCoupling 0 0 0 0 s = 0 := by
  simp [coriolisLieCoupling,
    GoutevTonevNuclearHamiltonian.coriolisEnergy_vanishes_off_K_half 0 0 s hK]

end HamiltonianCoriolisLieDynamics
