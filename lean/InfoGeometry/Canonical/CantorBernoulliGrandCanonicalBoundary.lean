import Mathlib.Tactic
import InfoGeometry.Canonical.CantorBernoulliBranchExchangeThermofield
import InfoGeometry.Canonical.GrandCanonicalCore
import InfoGeometry.Canonical.NambuGorkovParticleHoleBridge
import InfoGeometry.Quantum.DikinApolloniusTrap
import InfoGeometry.Canonical.CramerRaoUncertainty
import InfoGeometry.Physics.BogoliubovWeylChemicalPotential

/-
# Grand-canonical Cantor boundary readouts

The repository already owns the finite grand-canonical distribution, the
Bogoliubov/Fock chemical-potential form, the finite BdG particle-hole law, the
Dikin trap, and the Cramér-Rao reduction.  This file is only their finite
boundary adapter.

The Cantor carrier remains the existing binary Bernoulli Hilbert carrier
L2Boundary = Lp ℂ 2 μC.  The thermofield wave remains the existing TwinAmplitude
carrier transported by twinAmplitudeToCantorLinear.

The statements here are deliberately algebraic and finite.  They do not claim
a spectral integral, a Fokker--Planck limit, a global O₂ automorphism, a Pin
index, or an identification of the Cantor carrier with a BdG kernel.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBernoulliGrandCanonicalBoundary

open Complex
open InfoGeometry.Canonical.CantorBernoulliBranchExchangeThermofield
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport
open InfoGeometry.Canonical.SpinorCantorL2HilbertIntertwinerBridge
open InfoGeometry.Canonical.ThermofieldBidirectionalResonator
open InfoGeometry.Canonical.ThermofieldMobiusResonator
open InfoGeometry.GrandCanonical
open InfoGeometry.Physics.BogoliubovWeylChemicalPotential
open InfoGeometry.Physics.SupergradedCuntzBdG
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzCStarRealization
open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliKMSStateBridge
open NambuGorkovParticleHoleBridge
open InfoGeometry.Quantum.DikinApolloniusTrap
open InfoGeometry.Canonical.CramerRaoUncertainty

/-- A finite grand-canonical state selected for boundary readout. -/
structure GrandCanonicalBoundaryState
    (α : Type*) [Fintype α] [Nonempty α] where
  params : GrandCanonicalTwoParam α
  beta : ℝ
  mu : ℝ
  state : α

/-- The normalized finite grand-canonical weight at the selected state. -/
noncomputable def normalizedBoundaryWeight
    {α : Type*} [Fintype α] [Nonempty α]
    (s : GrandCanonicalBoundaryState α) : ℝ :=
  gibbsWeightGC s.params s.beta s.mu s.state

@[simp] theorem normalizedBoundaryWeight_pos
    {α : Type*} [Fintype α] [Nonempty α]
    (s : GrandCanonicalBoundaryState α) :
    0 < normalizedBoundaryWeight s := by
  exact gibbsWeightGC_pos s.params s.beta s.mu s.state

@[simp] theorem normalizedBoundaryWeight_nonneg
    {α : Type*} [Fintype α] [Nonempty α]
    (s : GrandCanonicalBoundaryState α) :
    0 ≤ normalizedBoundaryWeight s :=
  le_of_lt (normalizedBoundaryWeight_pos s)

/-- The finite grand-canonical weights sum to one. -/
theorem normalizedBoundaryWeight_sum_one
    {α : Type*} [Fintype α] [Nonempty α]
    (s : GrandCanonicalBoundaryState α) :
    ∑ x, gibbsWeightGC s.params s.beta s.mu x = 1 := by
  exact gibbsWeightGC_sum_one s.params s.beta s.mu

/-- The finite grand-canonical chemical potential direction is the existing
count response, exposed at the boundary adapter. -/
theorem normalizedBoundary_mu_response
    {α : Type*} [Fintype α] [Nonempty α]
    (s : GrandCanonicalBoundaryState α) :
    deriv
        (fun t =>
          potentialGC s.params s.beta t)
        s.mu =
      s.beta * meanNumber s.params s.beta s.mu := by
  exact potentialGC_deriv_mu_eq_beta_meanNumber
    s.params s.beta s.mu

/-- The finite inverse-temperature direction is the shifted-energy response. -/
theorem normalizedBoundary_beta_response
    {α : Type*} [Fintype α] [Nonempty α]
    (s : GrandCanonicalBoundaryState α) :
    deriv
        (fun t =>
          potentialGC s.params t s.mu)
        s.beta =
      -meanShift s.params s.beta s.mu := by
  exact potentialGC_deriv_beta_eq_neg_meanShift
    s.params s.beta s.mu

/-- Grand-canonical thermal weighting of the existing twin thermofield wave. -/
def grandCanonicalThermofieldAmplitude
    (beta energy mu charge gamma omega coupling time : ℝ) : TwinAmplitude :=
  thermofieldAmplitude beta (energy - mu * charge)
    gamma omega coupling time

/-- The grand-canonical thermal weight is exactly the existing thermal weight
at shifted energy E - μQ. -/
def grandCanonicalThermalWeight
    (beta energy mu charge : ℝ) : ℝ :=
  thermalWeight beta (energy - mu * charge)

theorem grandCanonicalThermalWeight_eq_exp_half
    (beta energy mu charge : ℝ) :
    grandCanonicalThermalWeight beta energy mu charge =
      Real.exp (-(beta * (energy - mu * charge)) / 2) := by
  unfold grandCanonicalThermalWeight thermalWeight
  congr 1
  ring

/-- The thermalized twin wave has the exact open-system energy decay after the
finite grand-canonical energy shift. -/
theorem grandCanonicalThermofieldAmplitude_totalEnergy
    (beta energy mu charge gamma omega coupling time : ℝ) :
    totalEnergy
        (grandCanonicalThermofieldAmplitude
          beta energy mu charge gamma omega coupling time) =
      (grandCanonicalThermalWeight beta energy mu charge) ^ 2 *
        Real.exp (-2 * gamma * time) := by
  simpa [grandCanonicalThermofieldAmplitude,
    grandCanonicalThermalWeight] using
    (envelopeDecay beta (energy - mu * charge)
      gamma omega coupling time)

/-- Finite twin-carrier chiral parity readout. -/
def chiralParityReadout (a : TwinAmplitude) : ℝ :=
  energyPlus a - energyMinus a

/-- The forward component energy of the existing thermofield solution. -/
theorem thermofield_energyPlus
    (beta energy gamma omega coupling time : ℝ) :
    energyPlus
        (thermofieldAmplitude beta energy gamma omega coupling time) =
      (thermalWeight beta energy) ^ 2 *
        (Real.exp (-gamma * time)) ^ 2 *
        (Real.cos (coupling * time)) ^ 2 := by
  unfold energyPlus thermofieldAmplitude
  dsimp
  have h_phase :
      Complex.normSq (Complex.exp (-Complex.I * omega * time)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    have h : (-Complex.I * omega * time).re = 0 := by
      simp
    rw [h, Real.exp_zero, one_pow]
  have h_plus :
      Complex.normSq
          ((thermalWeight beta energy : ℂ) *
            (Real.exp (-gamma * time) : ℂ) *
            Complex.exp (-Complex.I * omega * time) *
            (Real.cos (coupling * time) : ℂ)) =
        (thermalWeight beta energy) ^ 2 *
          (Real.exp (-gamma * time)) ^ 2 *
          (Real.cos (coupling * time)) ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
      h_phase, mul_one, Complex.normSq_ofReal,
      Complex.normSq_ofReal, Complex.normSq_ofReal]
    ring
  simp_rw [Complex.ofReal_mul]
  exact h_plus

/-- The scattered twin component energy of the existing thermofield solution. -/
theorem thermofield_energyMinus
    (beta energy gamma omega coupling time : ℝ) :
    energyMinus
        (thermofieldAmplitude beta energy gamma omega coupling time) =
      (thermalWeight beta energy) ^ 2 *
        (Real.exp (-gamma * time)) ^ 2 *
        (Real.sin (coupling * time)) ^ 2 := by
  unfold energyMinus thermofieldAmplitude
  dsimp
  have h_phase :
      Complex.normSq (Complex.exp (-Complex.I * omega * time)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    have h : (-Complex.I * omega * time).re = 0 := by
      simp
    rw [h, Real.exp_zero, one_pow]
  have h_minus :
      Complex.normSq
          (-Complex.I * (thermalWeight beta energy : ℂ) *
            (Real.exp (-gamma * time) : ℂ) *
            Complex.exp (-Complex.I * omega * time) *
            (Real.sin (coupling * time) : ℂ)) =
        (thermalWeight beta energy) ^ 2 *
          (Real.exp (-gamma * time)) ^ 2 *
          (Real.sin (coupling * time)) ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_I,
      one_mul, h_phase, mul_one, Complex.normSq_ofReal,
      Complex.normSq_ofReal, Complex.normSq_ofReal]
    ring
  simp_rw [Complex.ofReal_mul, ← mul_assoc (-Complex.I)]
  exact h_minus

/-- Exact parity trembling law on the finite thermofield carrier. -/
theorem thermofield_chiralParity
    (beta energy gamma omega coupling time : ℝ) :
    chiralParityReadout
        (thermofieldAmplitude beta energy gamma omega coupling time) =
      (thermalWeight beta energy) ^ 2 *
        Real.exp (-2 * gamma * time) *
        Real.cos (2 * (coupling * time)) := by
  unfold chiralParityReadout
  rw [thermofield_energyPlus, thermofield_energyMinus]
  have h_exp :
      (Real.exp (-gamma * time)) ^ 2 =
        Real.exp (-2 * gamma * time) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have h_trig :
      (Real.cos (coupling * time)) ^ 2 -
          (Real.sin (coupling * time)) ^ 2 =
        Real.cos (2 * (coupling * time)) := by
    rw [Real.cos_two_mul]
    nlinarith [Real.cos_sq_add_sin_sq (coupling * time)]
  calc
    (thermalWeight beta energy) ^ 2 *
          (Real.exp (-gamma * time)) ^ 2 *
          (Real.cos (coupling * time)) ^ 2 -
        (thermalWeight beta energy) ^ 2 *
          (Real.exp (-gamma * time)) ^ 2 *
          (Real.sin (coupling * time)) ^ 2 =
      (thermalWeight beta energy) ^ 2 *
        (Real.exp (-gamma * time)) ^ 2 *
        ((Real.cos (coupling * time)) ^ 2 -
          (Real.sin (coupling * time)) ^ 2) := by
      ring
    _ = (thermalWeight beta energy) ^ 2 *
        Real.exp (-2 * gamma * time) *
        ((Real.cos (coupling * time)) ^ 2 -
          (Real.sin (coupling * time)) ^ 2) := by
      rw [h_exp]
    _ = (thermalWeight beta energy) ^ 2 *
        Real.exp (-2 * gamma * time) *
        Real.cos (2 * (coupling * time)) := by
      rw [h_trig]

/-- The same finite parity law after the grand-canonical energy shift. -/
theorem grandCanonicalThermofield_chiralParity
    (beta energy mu charge gamma omega coupling time : ℝ) :
    chiralParityReadout
        (grandCanonicalThermofieldAmplitude
          beta energy mu charge gamma omega coupling time) =
      (grandCanonicalThermalWeight beta energy mu charge) ^ 2 *
        Real.exp (-2 * gamma * time) *
        Real.cos (2 * (coupling * time)) := by
  simpa [grandCanonicalThermofieldAmplitude,
    grandCanonicalThermalWeight] using
    thermofield_chiralParity beta (energy - mu * charge)
      gamma omega coupling time

/-- Concrete chiral parity on the Cantor boundary carrier. -/
def branchChiralParityOp : BoundaryOperator :=
  vLeft.comp (normalizedPrependBitLpAdjoint false) -
    vRight.comp (normalizedPrependBitLpAdjoint true)

/-- The Cantor parity operator acts as + on the left branch and - on the
right branch, on the existing two-channel carrier. -/
theorem branchChiralParityOp_twinAmplitude (a : TwinAmplitude) :
    branchChiralParityOp (twinAmplitudeToCantorLinear a) =
      a.aPlus • branchVector false -
        a.aMinus • branchVector true := by
  have hff :
      normalizedPrependBitLpAdjoint false (branchVector false) =
        vacuumL2 := by
    change
      normalizedPrependBitLpAdjoint false (vLeft vacuumL2) =
        vacuumL2
    exact ContinuousLinearMap.ext_iff.mp
      vLeft_adjoint_comp_vLeft vacuumL2
  have hft :
      normalizedPrependBitLpAdjoint false (branchVector true) =
        0 := by
    change
      normalizedPrependBitLpAdjoint false (vRight vacuumL2) = 0
    exact ContinuousLinearMap.ext_iff.mp
      vLeft_adjoint_comp_vRight vacuumL2
  have htf :
      normalizedPrependBitLpAdjoint true (branchVector false) =
        0 := by
    change
      normalizedPrependBitLpAdjoint true (vLeft vacuumL2) = 0
    exact ContinuousLinearMap.ext_iff.mp
      vRight_adjoint_comp_vLeft vacuumL2
  have htt :
      normalizedPrependBitLpAdjoint true (branchVector true) =
        vacuumL2 := by
    change
      normalizedPrependBitLpAdjoint true (vRight vacuumL2) =
        vacuumL2
    exact ContinuousLinearMap.ext_iff.mp
      vRight_adjoint_comp_vRight vacuumL2
  change
    vLeft (normalizedPrependBitLpAdjoint false
      (a.aPlus • branchVector false + a.aMinus • branchVector true)) -
      vRight (normalizedPrependBitLpAdjoint true
        (a.aPlus • branchVector false + a.aMinus • branchVector true)) =
      a.aPlus • branchVector false - a.aMinus • branchVector true
  simp only [map_add, map_smul, hff, hft, htf, htt,
    smul_zero, zero_add, add_zero]
  rfl

/-- The grand-canonical thermofield solution embedded in the existing Cantor
boundary carrier. -/
def cantorGrandCanonicalThermofieldAmplitude
    (beta energy mu charge gamma omega coupling time : ℝ) : L2Carrier :=
  twinAmplitudeToCantorLinear
    (grandCanonicalThermofieldAmplitude
      beta energy mu charge gamma omega coupling time)

/-- The first-level Cuntz exchange transports the grand-canonical twin wave
exactly as it transports the existing thermofield wave. -/
theorem branchExchangeOp_cantorGrandCanonicalThermofieldAmplitude
    (beta energy mu charge gamma omega coupling time : ℝ) :
    branchExchangeOp
        (cantorGrandCanonicalThermofieldAmplitude
          beta energy mu charge gamma omega coupling time) =
      twinAmplitudeToCantorLinear
        (twinAmplitudeSwapLinear
          (grandCanonicalThermofieldAmplitude
            beta energy mu charge gamma omega coupling time)) := by
  exact branchExchangeOp_twinAmplitude
    (grandCanonicalThermofieldAmplitude
      beta energy mu charge gamma omega coupling time)

/-- The same wave can be placed in any existing finite cylinder. -/
def prefixGrandCanonicalThermofieldAmplitude
    (w : List Bool)
    (beta energy mu charge gamma omega coupling time : ℝ) : L2Carrier :=
  operatorWord w
    (cantorGrandCanonicalThermofieldAmplitude
      beta energy mu charge gamma omega coupling time)

theorem prefixExchangeOp_apply_grandCanonicalThermofield
    (w : List Bool)
    (beta energy mu charge gamma omega coupling time : ℝ) :
    prefixExchangeOp w
        (prefixGrandCanonicalThermofieldAmplitude
          w beta energy mu charge gamma omega coupling time) =
      operatorWord w
        (twinAmplitudeToCantorLinear
          (twinAmplitudeSwapLinear
            (grandCanonicalThermofieldAmplitude
              beta energy mu charge gamma omega coupling time))) := by
  simpa [prefixGrandCanonicalThermofieldAmplitude,
    cantorGrandCanonicalThermofieldAmplitude] using
    (prefixExchangeOp_apply_thermofield w beta
      (energy - mu * charge) gamma omega coupling time)

/-- Particle-hole matching is the existing finite BdG theorem. -/
theorem finiteBdG_particleHole_pairing
    (xi : ℝ) (delta : ℂ) :
    particleHoleConj (kitaevH xi delta) =
      -kitaevH xi (-delta) := by
  exact bdg_class_D_particle_hole_symmetry xi delta

/-- Applying the finite particle-hole conjugation twice is the existing
involution theorem. -/
theorem finiteBdG_particleHole_involution
    (matrix : Matrix (Fin 2) (Fin 2) ℂ) :
    particleHoleConj (particleHoleConj matrix) = matrix := by
  exact particle_hole_operator_sq_eq_one matrix

/-- The Dikin scale metric is positive on the existing finite barrier lane. -/
theorem dikin_boundary_metric_pos (xi : ℝ) :
    0 < dikinScaleMetric xi :=
  dikin_scale_metric_pos xi

/-- The existing Dikin trap supplies the finite contraction readout. -/
theorem dikin_boundary_contraction
    (radius y Ty Kc : ℝ)
    (hKc : 0 ≤ Kc)
    (hy : y ∈ dikinEquilibriumEllipsoid radius)
    (hcontract : |Ty| ≤ Kc * |y|) :
    2 * Ty ^ 2 ≤ (Kc * radius) ^ 2 := by
  exact blahut_arimoto_dikin_shrinkage
    Kc radius y hKc hy Ty hcontract

/-- The existing Cramér-Rao owner supplies the finite uncertainty floor. -/
theorem dikin_boundary_cramer_rao_floor
    (variancePosition varianceMomentum fisher : ℝ)
    (hcr : variancePosition * fisher ≥ 1)
    (hmomentum : varianceMomentum = (1 / 4) * fisher) :
    variancePosition * varianceMomentum ≥ (1 / 4) := by
  exact heisenberg_from_cramer_rao
    variancePosition varianceMomentum fisher hcr hmomentum

/-- The finite Cantor boundary package exposed as one honest readout record. -/
structure ThermalizedCantorBoundaryReadout
    (α : Type*) [Fintype α] [Nonempty α] where
  finiteState : GrandCanonicalBoundaryState α
  beta : ℝ
  energy : ℝ
  mu : ℝ
  charge : ℝ
  gamma : ℝ
  omega : ℝ
  coupling : ℝ
  time : ℝ

/-- The package exposes the normalized finite Gibbs weight together with the
embedded grand-canonical thermofield boundary wave. -/
def ThermalizedCantorBoundaryReadout.weight
    {α : Type*} [Fintype α] [Nonempty α]
    (data : ThermalizedCantorBoundaryReadout α) : ℝ :=
  normalizedBoundaryWeight data.finiteState

def ThermalizedCantorBoundaryReadout.wave
    {α : Type*} [Fintype α] [Nonempty α]
    (data : ThermalizedCantorBoundaryReadout α) : L2Carrier :=
  cantorGrandCanonicalThermofieldAmplitude
    data.beta data.energy data.mu data.charge
    data.gamma data.omega data.coupling data.time

theorem ThermalizedCantorBoundaryReadout.weight_pos
    {α : Type*} [Fintype α] [Nonempty α]
    (data : ThermalizedCantorBoundaryReadout α) :
    0 < data.weight :=
  normalizedBoundaryWeight_pos data.finiteState

theorem ThermalizedCantorBoundaryReadout.wave_exchange
    {α : Type*} [Fintype α] [Nonempty α]
    (data : ThermalizedCantorBoundaryReadout α) :
    branchExchangeOp data.wave =
      twinAmplitudeToCantorLinear
        (twinAmplitudeSwapLinear
          (grandCanonicalThermofieldAmplitude
            data.beta data.energy data.mu data.charge
            data.gamma data.omega data.coupling data.time)) := by
  exact branchExchangeOp_cantorGrandCanonicalThermofieldAmplitude
    data.beta data.energy data.mu data.charge
    data.gamma data.omega data.coupling data.time

end InfoGeometry.Canonical.CantorBernoulliGrandCanonicalBoundary
