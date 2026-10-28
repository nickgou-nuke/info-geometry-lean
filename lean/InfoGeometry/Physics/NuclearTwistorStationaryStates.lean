/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.NuclearTwistorConfigurationSector
import InfoGeometry.Twistor.RealTwistorSpectralAction

/-!
# A concrete action, constraints and normalized stationary states

The stationary action acts on the full polynomial operator representation.
Its restriction to the actual degree-one sector agrees with the existing
three-configuration Hamiltonian. The genuine-dual positive graph carries
the same action and unit normalization. Dark and bright stationary states
are constructed from the existing graph maps and their induced norms.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearTwistorStationaryStates

open InfoGeometry.Twistor.RealPolynomialCCR
open InfoGeometry.Twistor.RealDualTwistor
open InfoGeometry.Twistor.RealDualTwistorKreinBridge
open InfoGeometry.Twistor.RealDualTwistorPositiveSector
open InfoGeometry.Twistor.RealSpectralAction
open InfoGeometry.Physics.NuclearThreeConfiguration
open InfoGeometry.Physics.NuclearThreeConfigurationTransition
open InfoGeometry.Physics.NuclearEffectiveObservables
open InfoGeometry.Physics.NuclearTwistorConfigurationSector

/-- An operator-valued source for the real stationary action. -/
def polynomialAction (a c g : ℝ) (p : PolynomialState) (E : ℝ) : ℝ :=
  action fockForm (polynomialHamiltonian a c g) p E

theorem polynomialAction_hasDerivAt (a c g : ℝ) (p v : PolynomialState) (E μ : ℝ) :
    HasDerivAt (fun t : ℝ => polynomialAction a c g (p + t • v) (E + t * μ))
      (fockPairing v (polynomialHamiltonian a c g p - E • p) -
        μ * (fockPairing p p - 1) / 2) 0 :=
  hasDerivAt_action_line fockForm (polynomialHamiltonian a c g)
    fockPairing_symmetric (polynomialHamiltonian_symmetric a c g) p v E μ

theorem polynomialStationary_iff (a c g : ℝ) (p : PolynomialState) (E : ℝ) :
    Stationary fockForm (polynomialHamiltonian a c g) p E ↔
      polynomialHamiltonian a c g p = E • p ∧ fockPairing p p = 1 :=
  stationary_iff fockForm (polynomialHamiltonian a c g)
    fockPairing_symmetric (polynomialHamiltonian_symmetric a c g)
    (fun _ hp => fockPairing_self_pos hp) p E

/-- The stationary equation is equivalent to the full configuration equation. -/
theorem polynomialStationary_embedding_iff (a c g E : ℝ) (x : ConfigurationSpace) :
    Stationary fockForm (polynomialHamiltonian a c g) (euclideanEmbedding x) E ↔
      hamiltonian a c g x = E • x ∧ inner ℝ x x = 1 := by
  rw [polynomialStationary_iff, polynomialHamiltonian_eigen_iff,
    euclideanEmbedding_pairing]

theorem configuration_inner_symmetric (a c g : ℝ) (x y : ConfigurationSpace) :
    inner ℝ (hamiltonian a c g x) y = inner ℝ x (hamiltonian a c g y) := by
  simpa only [hamiltonian_adjoint] using
    ((hamiltonian a c g).adjoint_inner_right x y).symm

/-- The same spectral action on the actual primal/algebraic-dual carrier. -/
def positiveDualAction (a c g : ℝ) (p : Carrier ConfigurationSpace) (E : ℝ) : ℝ :=
  neutralForm p (configurationDualHamiltonian a c g p) / 2 -
    E * (neutralForm p p - 1) / 2

theorem positiveDualAction_embedding (a c g E : ℝ) (x : ConfigurationSpace) :
    positiveDualAction a c g (positiveEmbedding x) E =
      action realInnerFlat (hamiltonian a c g).toLinearMap x E := by
  unfold positiveDualAction action
  rw [configurationDualHamiltonian_positiveEmbedding,
    positiveEmbedding_pairing, positiveEmbedding_pairing]
  rfl

/-- Variations stay in the explicitly selected positive graph. -/
theorem positiveDualAction_hasDerivAt (a c g : ℝ)
    (x v : ConfigurationSpace) (E μ : ℝ) :
    HasDerivAt (fun t : ℝ =>
        positiveDualAction a c g (positiveEmbedding (x + t • v)) (E + t * μ))
      (inner ℝ v (hamiltonian a c g x - E • x) -
        μ * (inner ℝ x x - 1) / 2) 0 := by
  simp_rw [positiveDualAction_embedding]
  exact hasDerivAt_action_line realInnerFlat (hamiltonian a c g).toLinearMap
    (fun x y => (real_inner_comm x y).symm) (configuration_inner_symmetric a c g) x v E μ

/-- Both the physical equation and normalization follow from graph-constrained stationarity. -/
theorem positiveDualAction_stationary_iff (a c g E : ℝ) (x : ConfigurationSpace) :
    (∀ (v : ConfigurationSpace) (μ : ℝ),
      deriv (fun t : ℝ =>
        positiveDualAction a c g (positiveEmbedding (x + t • v)) (E + t * μ)) 0 = 0) ↔
      hamiltonian a c g x = E • x ∧ inner ℝ x x = 1 := by
  simp_rw [positiveDualAction_embedding]
  exact stationary_iff realInnerFlat (hamiltonian a c g).toLinearMap
    (fun x y => (real_inner_comm x y).symm) (configuration_inner_symmetric a c g)
    (fun _ hx => real_inner_self_pos.mpr hx) x E

def darkConfiguration (a c g : ℝ) : ConfigurationSpace :=
  normalizedState (graphMap c g a) darkModel

def brightConfiguration (c g E : ℝ) : ConfigurationSpace :=
  normalizedState (graphMap c g E) brightModel

theorem darkConfiguration_unit (a c g : ℝ) :
    inner ℝ (darkConfiguration a c g) (darkConfiguration a c g) = 1 := by
  rw [real_inner_self_eq_norm_sq, darkConfiguration,
    norm_normalizedState _ (graphMap_injective c g a) darkModel_ne_zero]
  norm_num

theorem brightConfiguration_unit (c g E : ℝ) :
    inner ℝ (brightConfiguration c g E) (brightConfiguration c g E) = 1 := by
  rw [real_inner_self_eq_norm_sq, brightConfiguration,
    norm_normalizedState _ (graphMap_injective c g E) brightModel_ne_zero]
  norm_num

/-- The dark eigenstate exists even when its energy equals `c`; no pole inverse is used. -/
theorem darkConfiguration_eigen (a c g : ℝ) :
    hamiltonian a c g (darkConfiguration a c g) = a • darkConfiguration a c g := by
  unfold darkConfiguration normalizedState
  rw [map_smul, dark_eigen_equation]
  simp only [smul_smul, mul_comm]

theorem brightConfiguration_eigen (a c g E : ℝ) (hE : E ≠ c)
    (hsec : (a - E) * (c - E) = 2 * g ^ 2) :
    hamiltonian a c g (brightConfiguration c g E) = E • brightConfiguration c g E := by
  unfold brightConfiguration normalizedState
  rw [map_smul, (bright_eigen_equation_iff a c g E hE).mpr hsec]
  simp only [smul_smul, mul_comm]

def darkPolynomial (a c g : ℝ) : PolynomialState :=
  euclideanEmbedding (darkConfiguration a c g)

def brightPolynomial (c g E : ℝ) : PolynomialState :=
  euclideanEmbedding (brightConfiguration c g E)

theorem darkPolynomial_sector (a c g : ℝ) :
    oneParticleProjector (darkPolynomial a c g) = darkPolynomial a c g := by
  exact (mem_oneParticleSector_iff _).mp (euclideanEmbedding_mem_sector _)

theorem brightPolynomial_sector (c g E : ℝ) :
    oneParticleProjector (brightPolynomial c g E) = brightPolynomial c g E := by
  exact (mem_oneParticleSector_iff _).mp (euclideanEmbedding_mem_sector _)

theorem darkPolynomial_unit (a c g : ℝ) :
    fockPairing (darkPolynomial a c g) (darkPolynomial a c g) = 1 := by
  exact (euclideanEmbedding_pairing _ _).trans (darkConfiguration_unit a c g)

theorem brightPolynomial_unit (c g E : ℝ) :
    fockPairing (brightPolynomial c g E) (brightPolynomial c g E) = 1 := by
  exact (euclideanEmbedding_pairing _ _).trans (brightConfiguration_unit c g E)

/-- The stationary constraint is inhabited for every real model parameter. -/
theorem darkPolynomial_stationary (a c g : ℝ) :
    Stationary fockForm (polynomialHamiltonian a c g) (darkPolynomial a c g) a :=
  (polynomialStationary_embedding_iff a c g a _).mpr
    ⟨darkConfiguration_eigen a c g, darkConfiguration_unit a c g⟩

theorem brightPolynomial_stationary (a c g E : ℝ) (hE : E ≠ c)
    (hsec : (a - E) * (c - E) = 2 * g ^ 2) :
    Stationary fockForm (polynomialHamiltonian a c g) (brightPolynomial c g E) E :=
  (polynomialStationary_embedding_iff a c g E _).mpr
    ⟨brightConfiguration_eigen a c g E hE hsec, brightConfiguration_unit c g E⟩

theorem darkDual_unit (a c g : ℝ) :
    neutralForm (positiveEmbedding (darkConfiguration a c g))
      (positiveEmbedding (darkConfiguration a c g)) = 1 := by
  rw [positiveEmbedding_pairing, darkConfiguration_unit]

theorem brightDual_unit (c g E : ℝ) :
    neutralForm (positiveEmbedding (brightConfiguration c g E))
      (positiveEmbedding (brightConfiguration c g E)) = 1 := by
  rw [positiveEmbedding_pairing, brightConfiguration_unit]

end InfoGeometry.Physics.NuclearTwistorStationaryStates
