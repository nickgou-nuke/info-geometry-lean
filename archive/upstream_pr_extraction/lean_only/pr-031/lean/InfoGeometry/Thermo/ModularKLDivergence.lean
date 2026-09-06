import InfoGeometry.Canonical.IBFrozenModularBridge
import InfoGeometry.Canonical.RelativeModularOperator
import InfoGeometry.Canonical.RelativeSurprisalOperatorLift
import InfoGeometry.Projective.GaugeReduction

/-!
# InfoGeometry.Thermo.ModularKLDivergence

Thin thermo/modular bridge surface over existing owners.

This file introduces no new ontology. It only packages already-owned results:

- frozen Gibbs modular potential identities (`β · KL + log-partition`);
- projective/radial decomposition of generalized KL (shape/scale split);
- finite relative modular Hamiltonian readout identities;
- count-ray decomposition into projective readout + mass-shift gauge term.
-/

namespace InfoGeometry.Thermo.ModularKLDivergence

open scoped ENNReal NNReal

section FrozenGibbs

open InfoGeometry.Canonical.IB

variable {X Y T : Type} [Fintype X] [Fintype Y] [Fintype T]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace T] [MeasurableSingletonClass T]
variable [DecidableEq T]

/--
Frozen Gibbs/Jaynes variational identity on the local BA slice:
the logarithmic BA ratio equals `-(β · KL) - logPartition`.
-/
theorem operatorial_gibbs_variational_principle_frozen
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (x : X) (t : T) :
    Real.log ((((ibBlahutArimotoStepFrozen
      (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal) / (qT t).toReal)
      = -prob.beta *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
        - logPartitionFrozen prob qT mY_givenT x := by
  exact
    ibBlahutArimotoStepFrozen_log_ratio_eq_neg_betaKL_sub_logPartitionFrozen
      (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x t

/--
If the BA ratio positivity witness is provided, the scalar modular potential is
`β · KL + logPartition`.
-/
theorem operatorial_gibbs_variational_principle_frozen_scalar
    (prob : IBProblem (X := X) (Y := Y))
    (qT : FinProb T)
    (mY_givenT : T → FinProb Y)
    (hq : ∀ t : T, 0 < (qT t).toReal)
    (x : X) (t : T) :
    let r : ℝ :=
      (((ibBlahutArimotoStepFrozen
          (X := X) (Y := Y) (T := T) prob qT mY_givenT x) t).toReal) / (qT t).toReal
    ∀ hr : 0 < r,
    InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential
      r hr
      = prob.beta *
          (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
        + logPartitionFrozen prob qT mY_givenT x := by
  intro r hr
  rw [InfoGeometry.Canonical.RelativePotentialScalarBridge.scalarModularPotential_eq_neg_log]
  have hlog :
      Real.log r
        = -prob.beta *
            (InfoGeometry.fin_kl_div (condYGivenX prob x) (mY_givenT t)).toReal
          - logPartitionFrozen prob qT mY_givenT x := by
    simpa [r] using
      ibBlahutArimotoStepFrozen_log_ratio_eq_neg_betaKL_sub_logPartitionFrozen
        (X := X) (Y := Y) (T := T) prob qT mY_givenT hq x t
  linarith

end FrozenGibbs

section RelativeModularReadout

open InfoGeometry.Canonical.PositiveRayCore
open InfoGeometry.Canonical.RelativeModularOperator

variable {n : ℕ} [Nonempty (Fin n)]

/--
Finite relative modular Hamiltonian readout equals the averaged relative
modular potential on the diagonal owner.
-/
theorem relative_modular_hamiltonian_readout_eq_average_potential
    (q q0 : PositiveRay (Fin n)) :
    relativeModularHamiltonianReadout (n := n) q q0
      = (n : ℝ)⁻¹ * ∑ i,
          InfoGeometry.Canonical.RelativePotentialCore.relativeModularPotential q q0 i := by
  exact
    relativeModularHamiltonianReadout_eq_average_relativeModularPotential
      (n := n) q q0

/-- Self-relative modular Hamiltonian readout vanishes. -/
theorem relative_modular_hamiltonian_readout_self
    (q : PositiveRay (Fin n)) :
    relativeModularHamiltonianReadout (n := n) q q = 0 := by
  exact relativeModularHamiltonianReadout_self (n := n) q

end RelativeModularReadout

section ScaleShape

open InfoGeometry.PositiveMeasure

variable {α : Type*} [Fintype α] [Nonempty α]

/--
Generalized-KL projective/radial decomposition:
shape term on normalized rays plus scalar mass-gauge term.
-/
theorem generalizedKL_scale_shape_split
    (μ ν : PositiveMeasure α ℝ) :
    generalizedKL (α := α) μ ν
      =
    Z (α := α) (R := ℝ) μ
      * generalizedKL (α := α)
          (normalize (α := α) (R := ℝ) μ)
          (normalize (α := α) (R := ℝ) ν)
      + gklTerm (Z (α := α) (R := ℝ) μ) (Z (α := α) (R := ℝ) ν) := by
  simpa using
    generalizedKL_projective_radial_decomposition (α := α) μ ν

end ScaleShape

section CountRaySplit

open InfoGeometry.Canonical.RelativeSurprisalOperatorLift
open InfoGeometry.Canonical.RelativePotentialCountBridge

variable {n : ℕ} [Nonempty (Fin n)]

/--
Count-ray modular Hamiltonian decomposes into projective readout (`shape`) plus
count-mass shift (`scale/gauge`).
-/
theorem modular_hamiltonian_scale_shape_split_countRay
    (counts ref : RelativeCounts n)
    (hcounts : ∀ i : Fin n, 0 < counts i)
    (href : ∀ i : Fin n, 0 < ref i) :
    averagedModularHamiltonian n (relativeCountDensity n counts ref)
      =
    InfoGeometry.Canonical.RelativeModularOperator.relativeModularHamiltonianReadout (n := n)
      (countRay counts hcounts) (countRay ref href)
      + countMassShift counts ref hcounts href := by
  exact
    relativeModularHamiltonian_eq_relativeModularHamiltonianReadout_countRay_add_countMassShift
      (n := n) (counts := counts) (ref := ref) (hcounts := hcounts) (href := href)

end CountRaySplit

end InfoGeometry.Thermo.ModularKLDivergence
