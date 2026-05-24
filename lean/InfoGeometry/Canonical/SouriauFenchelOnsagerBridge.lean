import InfoGeometry.Canonical.SouriauMetriplecticContext
import InfoGeometry.Potential.Thermo
import InfoGeometry.Meta.Architecture

/-!
# Souriau Fenchel-Onsager Bridge

This file connects the finite Souriau thermodynamics owner surface to the
repo's Fenchel-Legendre/Massieu model and the finite Onsager/metriplectic
second-law shadow.

In the current trunk doctrine this entire module is a finite/scalar translator
surface. It is intentionally not the owner for the noncommutative,
dimension-agnostic theory: the operatorial trunk and the infinite coadjoint
interface live elsewhere.

Boundary:

* `SouriauThermodynamics` owns the finite moment-map shadow, Gibbs-Souriau
  density, Massieu potential, and Souriau-Fisher/Onsager response matrix.
* `LogPotential.LegendreModel` owns Fenchel inequality, contact equality, and
  Fenchel-gap nonnegativity.
* `SouriauMetriplecticContext` owns the finite Casimir-plus-Onsager
  entropy-production theorem.

This module supplies only bridge contexts and projection theorems.  It does not
claim a full coadjoint-orbit Souriau theory or an infinite-dimensional
metriplectic flow.

Repository policy boundary:
this file defines abstract Souriau bridge mechanics only. It does not
instantiate concrete `G₂(2)` / `Spin(5,5)` coadjoint-orbit thermodynamic
models.
-/

namespace InfoGeometry.Canonical.SouriauFenchelOnsagerBridge

open InfoGeometry.Canonical.SouriauThermodynamics
open InfoGeometry.Canonical.SouriauMetriplectic

variable {α : Type _}

/-! ## Abstract coadjoint moment-map surface -/

/--
Proof-carrying coadjoint moment-map interface.

`G` represents the Lie algebra, `Gdual` its coadjoint/moment side, and `State`
the underlying phase/state carrier.  The pairing is kept abstract so this
structure can cover finite shadows, operator lanes, or later smooth orbit
models without identifying them prematurely.
-/
@[rep_depth transport]
structure CoadjointMomentMapData (G Gdual State : Type*) where
  moment : State → Gdual
  geometricTemperature : G
  pairing : G → Gdual → ℝ

namespace CoadjointMomentMapData

variable {G Gdual State : Type*}
variable (C : CoadjointMomentMapData G Gdual State)

/-- The Souriau action/readout pairing at one state. -/
@[rep_depth transport]
def actionAt (x : State) : ℝ :=
  C.pairing C.geometricTemperature (C.moment x)

@[rep_depth transport]
theorem actionAt_eq_pairing (x : State) :
    C.actionAt x = C.pairing C.geometricTemperature (C.moment x) :=
  rfl

end CoadjointMomentMapData

/-! ## Fenchel-Legendre bridge to finite Souriau Massieu potential -/

/--
Finite Souriau/Fenchel context.

The field `massieu_matches` is the explicit bridge assertion that the scalar
log-potential model is evaluating the same Massieu/log-partition value as the
finite Souriau grand-canonical package at the selected parameter `theta`.
This is a scalar-shadow matching field, not an owner-level derivation of the
Massieu potential from the operatorial modular lane.
-/
@[rep_depth transport]
structure SouriauFenchelContext [Fintype α] [Nonempty α] where
  M : SouriauMomentMap α
  T : GeometricTemperature
  model : InfoGeometry.LogPotential.LegendreModel
  theta : ℝ
  massieu_matches :
    model.massieu theta = souriauMassieuPotential M T

namespace SouriauFenchelContext

variable [Fintype α] [Nonempty α]
variable (C : SouriauFenchelContext (α := α))

/-- The Fenchel model partition reads `exp` of the finite Souriau Massieu potential. -/
@[rep_depth transport]
theorem partition_eq_exp_souriauMassieu :
    C.model.partition C.theta = Real.exp (souriauMassieuPotential C.M C.T) := by
  calc
    C.model.partition C.theta = Real.exp (C.model.massieu C.theta) := rfl
    _ = Real.exp (souriauMassieuPotential C.M C.T) := by
      rw [C.massieu_matches]

/-- The Fenchel gap is nonnegative for every dual coordinate. -/
@[rep_depth transport]
theorem fenchelGap_nonneg (eta : ℝ) :
    0 ≤ C.model.fenchelGap C.theta eta :=
  C.model.fenchelGap_nonneg C.theta eta

/-- The Fenchel gap vanishes on the Legendre contact locus. -/
@[rep_depth transport]
theorem fenchelGap_eq_zero_at_contact :
    C.model.fenchelGap C.theta (C.model.dualCoord C.theta) = 0 :=
  C.model.fenchelGap_eq_zero_at_contact C.theta

/-- Contact balance `ψ + φ = θη`, rewritten at the bridge parameter. -/
@[rep_depth transport]
theorem contact_balance :
    C.model.massieu C.theta +
        C.model.φ (C.model.dualCoord C.theta) =
      C.theta * C.model.dualCoord C.theta :=
  C.model.contact_balance C.theta

/-- The finite Souriau Massieu value satisfies the same contact balance. -/
@[rep_depth transport]
theorem souriauMassieu_contact_balance :
    souriauMassieuPotential C.M C.T +
        C.model.φ (C.model.dualCoord C.theta) =
      C.theta * C.model.dualCoord C.theta := by
  rw [← C.massieu_matches]
  exact C.contact_balance

/-- Scaled Fenchel defects are nonnegative at nonnegative scale. -/
@[rep_depth transport]
theorem scaledFenchelGap_nonneg
    (epsilon eta : ℝ) (heps : 0 ≤ epsilon) :
    0 ≤ C.model.scaledFenchelGap epsilon C.theta eta :=
  C.model.scaledFenchelGap_nonneg epsilon C.theta eta heps

end SouriauFenchelContext

/-! ## Onsager/metriplectic projections -/

namespace MetriplecticContext

variable [Fintype α] [Nonempty α]
variable (C : MetriplecticContext (α := α))

/-- The Onsager response matrix in the metriplectic context is symmetric. -/
@[rep_depth transport]
theorem souriauOnsager_response_symmetric :
    (souriauFisherResponseMatrix C.M C.T).Symmetric :=
  souriauFisherResponseMatrix_symmetric C.M C.T

/-- The reversible/Casimir channel contributes no entropy production. -/
@[rep_depth transport]
theorem casimir_channel_zero :
    C.reversibleEntropyProduction = 0 :=
  C.reversibleEntropyProduction_eq_zero

/--
Finite Souriau-Onsager second-law projection:
the total entropy production is nonnegative under the explicit Casimir and PSD
response hypotheses carried by the context.

This theorem is a truthful finite shadow, but not the full dimension-agnostic
or operatorial owner theorem.
-/
@[rep_depth transport]
theorem onsager_total_entropy_nonnegative :
    0 ≤ C.totalEntropyProduction :=
  C.totalEntropyProduction_nonneg

end MetriplecticContext

/-! ## Coadjoint Casimir-entropy invariance surface (Erlangen operator stage) -/

/--
Proof-carrying symmetry package for the coadjoint entropy lane.

This keeps the geometry-as-symmetry-invariants doctrine explicit:

* `moment_equivariant` records the chosen state-to-coadjoint transport law.
* `entropy_casimir_invariant` records Casimir-style entropy invariance on `Gdual`.
* downstream theorems can therefore read entropy invariance directly on state orbits.
-/
@[rep_depth transport]
structure CoadjointEntropySymmetryContext
    (Sym G Gdual State : Type*) where
  data : CoadjointMomentMapData G Gdual State
  stateAction : Sym → State → State
  coadjointAction : Sym → Gdual → Gdual
  moment_equivariant :
    ∀ s : Sym, ∀ x : State,
      data.moment (stateAction s x) = coadjointAction s (data.moment x)
  entropy : Gdual → ℝ
  entropy_casimir_invariant :
    ∀ s : Sym, ∀ ξ : Gdual,
      entropy (coadjointAction s ξ) = entropy ξ

namespace CoadjointEntropySymmetryContext

variable {Sym G Gdual State : Type*}
variable (C : CoadjointEntropySymmetryContext Sym G Gdual State)

/-- Entropy is constant along the coadjoint symmetry orbit by the Casimir law. -/
@[rep_depth transport]
theorem entropy_invariant_on_coadjoint_orbit
    (s : Sym) (ξ : Gdual) :
    C.entropy (C.coadjointAction s ξ) = C.entropy ξ :=
  C.entropy_casimir_invariant s ξ

/--
Entropy is constant on state orbits when transported through the moment map.

This is the theorem-facing bridge from state-space symmetry action to
coadjoint Casimir-style entropy invariance.
-/
@[rep_depth transport]
theorem entropy_invariant_on_state_orbit
    (s : Sym) (x : State) :
    C.entropy (C.data.moment (C.stateAction s x)) =
      C.entropy (C.data.moment x) := by
  rw [C.moment_equivariant s x]
  exact C.entropy_casimir_invariant s (C.data.moment x)

end CoadjointEntropySymmetryContext

end InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
