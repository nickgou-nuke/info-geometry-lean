import InfoGeometry.GrandCanonical.Core
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SouriauThermodynamics

Source-faithful finite-state Souriau thermodynamics bridge.

This file records the part of the Souriau vocabulary that is already owned by
`InfoGeometry.GrandCanonical.Core`:

- a moment-map-shaped pair of observables `(energy, number)`,
- a geometric-temperature-shaped pair `(β, μ)`,
- the grand-canonical Gibbs weight and Massieu potential,
- the source-proved conjugacy laws
  `∂β log Z = -E[E - μN]` and `∂μ log Z = β E[N]`,
- the canonical one-observable Fisher/Hessian shadow
  `∂²β log Z = variance`.

It deliberately does not claim coadjoint-orbit equivariance, a full Souriau
metric tensor, or D1 commutator closure.  Those require separate owner
theorems.
-/

namespace InfoGeometry.Canonical.SouriauThermodynamics

open InfoGeometry.GrandCanonical

/--
Finite moment-map shadow: the two owner observables used by the
grand-canonical kernel.
-/
structure SouriauMomentMap (α : Type _) where
  energy : α → ℝ
  number : α → ℝ

/--
Finite geometric-temperature shadow: inverse temperature and chemical
potential as the two thermodynamic parameters already present in
`GrandCanonical.Core`.
-/
structure GeometricTemperature where
  beta : ℝ
  mu : ℝ

variable {α : Type _}

/-- Convert the finite Souriau moment-map shadow to the owner two-parameter data. -/
@[rep_depth thermo]
def toGrandCanonicalTwoParam (M : SouriauMomentMap α) :
    GrandCanonicalTwoParam α where
  energy := M.energy
  number := M.number

/-- Shifted observable `E - μN` in Souriau notation. -/
@[rep_depth thermo]
noncomputable def shiftedMomentReadout
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) : ℝ :=
  shiftedEnergy (toGrandCanonicalTwoParam M) T.mu x

/-- Souriau/Gibbs finite-state weight, definitionally the owner GC Gibbs weight. -/
@[rep_depth thermo]
noncomputable def souriauGibbsWeight
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) (x : α) : ℝ :=
  gibbsWeightGC (toGrandCanonicalTwoParam M) T.beta T.mu x

/-- Souriau/Massieu finite-state potential, definitionally the owner `potentialGC`. -/
@[rep_depth thermo]
noncomputable def souriauMassieuPotential
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  potentialGC (toGrandCanonicalTwoParam M) T.beta T.mu

/-- Mean shifted readout `E - μN` under the finite Souriau/Gibbs state. -/
@[rep_depth thermo]
noncomputable def souriauMeanShift
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  meanShift (toGrandCanonicalTwoParam M) T.beta T.mu

/-- Mean count/number readout under the finite Souriau/Gibbs state. -/
@[rep_depth thermo]
noncomputable def souriauMeanNumber
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) : ℝ :=
  meanNumber (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The `β` direction is conjugate to the shifted observable `E - μN`. -/
@[rep_depth thermo]
theorem souriau_beta_conjugate_shifted_readout
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    deriv (fun β => souriauMassieuPotential M { T with beta := β }) T.beta =
      -souriauMeanShift M T := by
  simpa [souriauMassieuPotential, souriauMeanShift, toGrandCanonicalTwoParam] using
    potentialGC_deriv_beta_eq_neg_meanShift
      (toGrandCanonicalTwoParam M) T.beta T.mu

/-- The `μ` direction is conjugate to the count observable `N`. -/
@[rep_depth thermo]
theorem souriau_mu_conjugate_number_readout
    [Fintype α] [Nonempty α]
    (M : SouriauMomentMap α) (T : GeometricTemperature) :
    deriv (fun μ => souriauMassieuPotential M { T with mu := μ }) T.mu =
      T.beta * souriauMeanNumber M T := by
  simpa [souriauMassieuPotential, souriauMeanNumber, toGrandCanonicalTwoParam] using
    potentialGC_deriv_mu_eq_beta_meanNumber
      (toGrandCanonicalTwoParam M) T.beta T.mu

/--
Canonical one-observable Fisher/Hessian shadow: the finite Souriau bridge
reduces to the existing owner theorem `hessian = variance` on the `μ = 0`
single-observable slice.
-/
@[rep_depth thermo]
theorem souriau_canonical_hessian_eq_variance
    [Fintype α] [Nonempty α]
    (energy : α → ℝ) (β : ℝ) :
    hessian ({ energy := energy } : GrandCanonicalParams α) β =
      variance ({ energy := energy } : GrandCanonicalParams α) β := by
  exact potential_second_derivative_eq_variance
    ({ energy := energy } : GrandCanonicalParams α) β

end InfoGeometry.Canonical.SouriauThermodynamics
