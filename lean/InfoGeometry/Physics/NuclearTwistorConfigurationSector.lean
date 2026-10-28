/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealTwistorOneParticleDual
import InfoGeometry.Twistor.RealDualTwistorPositiveSector
import InfoGeometry.Physics.NuclearThreeConfigurationTransition

/-!
# Polynomial and genuine-dual realizations of configuration mixing

The three-configuration Hamiltonian is realized by the actual polynomial
operators `sum hᵢⱼ a†ᵢ aⱼ`. Its finite coordinate action is proved through
the one-excitation embedding. The auxiliary degree constraint, positive
dual graph, and the retained/eliminated configuration split are distinct.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearTwistorConfigurationSector

open scoped Matrix

open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Twistor.RealDualTwistor
open InfoGeometry.Twistor.RealDualTwistorPositiveSector
open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearThreeConfigurationTransition

abbrev PolynomialState := WavePolynomial (Fin 3)

/-- The full polynomial differential operator, before restricting its degree. -/
def polynomialHamiltonian (a c g : ℝ) : Operator (Fin 3) :=
  oneBody (hamiltonianMatrix a c g)

theorem hamiltonianMatrix_transpose (a c g : ℝ) :
    (hamiltonianMatrix a c g).transpose = hamiltonianMatrix a c g := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem polynomialHamiltonian_symmetric (a c g : ℝ) (p q : PolynomialState) :
    fockPairing (polynomialHamiltonian a c g p) q =
      fockPairing p (polynomialHamiltonian a c g q) :=
  oneBody_symmetric _ (hamiltonianMatrix_transpose a c g) p q

/-- The finite matrix is an exact restriction of the polynomial operator. -/
theorem polynomialHamiltonian_embedding (a c g : ℝ) (x : ConfigurationSpace) :
    polynomialHamiltonian a c g (euclideanEmbedding x) =
      euclideanEmbedding (hamiltonian a c g x) :=
  oneBody_euclideanEmbedding _ x

theorem polynomialHamiltonian_eigen_iff (a c g E : ℝ) (x : ConfigurationSpace) :
    polynomialHamiltonian a c g (euclideanEmbedding x) = E • euclideanEmbedding x ↔
      hamiltonian a c g x = E • x := by
  rw [polynomialHamiltonian_embedding, ← map_smul]
  exact euclideanEmbedding_injective.eq_iff

theorem polynomialHamiltonian_sector_commute (a c g : ℝ) :
    oneParticleProjector * polynomialHamiltonian a c g =
      polynomialHamiltonian a c g * oneParticleProjector :=
  oneParticleProjector_oneBody_commute _

/-- A nonzero coupling creates an actual off-diagonal configuration amplitude. -/
theorem polynomialHamiltonian_off_diagonal (a c g : ℝ) :
    oneParticleCoeff (polynomialHamiltonian a c g (MvPolynomial.X 0)) 2 = g := by
  rw [← linearForm_single (0 : Fin 3), polynomialHamiltonian, oneBody_linearForm,
    oneParticleCoeff_linearForm]
  simp [hamiltonianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- This projector acts on both legs of the infinite polynomial/algebraic-dual carrier. -/
def dualNumberProjector : Module.End ℝ (Carrier PolynomialState) :=
  dualLift oneParticleProjector

theorem dualNumberProjector_idempotent :
    dualNumberProjector * dualNumberProjector = dualNumberProjector :=
  dualLift_idempotent _ oneParticleProjector_idempotent

theorem dualNumberProjector_selfAdjoint (p q : Carrier PolynomialState) :
    neutralForm (dualNumberProjector p) q = neutralForm p (dualNumberProjector q) :=
  dualLift_neutral_selfAdjoint _ p q

theorem dualNumberProjector_hamiltonian_commute (a c g : ℝ) :
    dualNumberProjector * dualLift (polynomialHamiltonian a c g) =
      dualLift (polynomialHamiltonian a c g) * dualNumberProjector :=
  dualLift_commute_of_commute _ _ (polynomialHamiltonian_sector_commute a c g)

/-- A polynomial transition operator with the same calibrated finite probe. -/
def polynomialProbe (κ : ℝ) : Operator (Fin 3) :=
  oneBody !![κ, 0, 0; 0, -κ, 0; 0, 0, 0]

theorem polynomialProbe_embedding (κ : ℝ) (x : ConfigurationSpace) :
    polynomialProbe κ (euclideanEmbedding x) = euclideanEmbedding (probe κ x) :=
  oneBody_euclideanEmbedding _ x

theorem polynomialProbe_symmetric (κ : ℝ) (p q : PolynomialState) :
    fockPairing (polynomialProbe κ p) q = fockPairing p (polynomialProbe κ q) := by
  apply oneBody_symmetric
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The finite configuration operator acts on the genuine primal/dual carrier. -/
def configurationDualHamiltonian (a c g : ℝ) : Module.End ℝ (Carrier ConfigurationSpace) :=
  dualLift (hamiltonian a c g).toLinearMap

theorem configurationDualHamiltonian_selfAdjoint (a c g : ℝ)
    (p q : Carrier ConfigurationSpace) :
    neutralForm (configurationDualHamiltonian a c g p) q =
      neutralForm p (configurationDualHamiltonian a c g q) :=
  dualLift_neutral_selfAdjoint _ p q

theorem configurationDualHamiltonian_positiveEmbedding (a c g : ℝ) (x : ConfigurationSpace) :
    configurationDualHamiltonian a c g (positiveEmbedding x) =
      positiveEmbedding (hamiltonian a c g x) :=
  dualLift_positiveEmbedding _ (hamiltonian_adjoint a c g) x

theorem configurationDualHamiltonian_positiveProjector_commute (a c g : ℝ) :
    configurationDualHamiltonian a c g * positiveProjector =
      positiveProjector * configurationDualHamiltonian a c g :=
  dualLift_positiveProjector_commute _ (hamiltonian_adjoint a c g)

end InfoGeometry.Physics.NuclearTwistorConfigurationSector
