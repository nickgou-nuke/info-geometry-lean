import InfoGeometry.Canonical.SouriauMetriplecticContext
import InfoGeometry.Potential.Thermo
import InfoGeometry.Meta.Architecture

/-!
# Souriau Fenchel-Onsager Bridge

This file connects the finite Souriau thermodynamics owner surface to the
repo's Fenchel-Legendre/Massieu model and the finite Onsager/metriplectic
second-law shadow.

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
@[rep_depth thermo]
structure CoadjointMomentMapData (G Gdual State : Type*) where
  moment : State → Gdual
  geometricTemperature : G
  pairing : G → Gdual → ℝ

namespace CoadjointMomentMapData

variable {G Gdual State : Type*}
variable (C : CoadjointMomentMapData G Gdual State)

/-- The Souriau action/readout pairing at one state. -/
@[rep_depth thermo]
def actionAt (x : State) : ℝ :=
  C.pairing C.geometricTemperature (C.moment x)

@[rep_depth thermo]
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
-/
@[rep_depth thermo]
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
@[rep_depth thermo]
theorem partition_eq_exp_souriauMassieu :
    C.model.partition C.theta = Real.exp (souriauMassieuPotential C.M C.T) := by
  calc
    C.model.partition C.theta = Real.exp (C.model.massieu C.theta) := rfl
    _ = Real.exp (souriauMassieuPotential C.M C.T) := by
      rw [C.massieu_matches]

/-- The Fenchel gap is nonnegative for every dual coordinate. -/
@[rep_depth thermo]
theorem fenchelGap_nonneg (eta : ℝ) :
    0 ≤ C.model.fenchelGap C.theta eta :=
  C.model.fenchelGap_nonneg C.theta eta

/-- The Fenchel gap vanishes on the Legendre contact locus. -/
@[rep_depth thermo]
theorem fenchelGap_eq_zero_at_contact :
    C.model.fenchelGap C.theta (C.model.dualCoord C.theta) = 0 :=
  C.model.fenchelGap_eq_zero_at_contact C.theta

/-- Contact balance `ψ + φ = θη`, rewritten at the bridge parameter. -/
@[rep_depth thermo]
theorem contact_balance :
    C.model.massieu C.theta +
        C.model.φ (C.model.dualCoord C.theta) =
      C.theta * C.model.dualCoord C.theta :=
  C.model.contact_balance C.theta

/-- The finite Souriau Massieu value satisfies the same contact balance. -/
@[rep_depth thermo]
theorem souriauMassieu_contact_balance :
    souriauMassieuPotential C.M C.T +
        C.model.φ (C.model.dualCoord C.theta) =
      C.theta * C.model.dualCoord C.theta := by
  rw [← C.massieu_matches]
  exact C.contact_balance

/-- Scaled Fenchel defects are nonnegative at nonnegative scale. -/
@[rep_depth thermo]
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
@[rep_depth thermo]
theorem souriauOnsager_response_symmetric :
    (souriauFisherResponseMatrix C.M C.T).Symmetric :=
  souriauFisherResponseMatrix_symmetric C.M C.T

/-- The reversible/Casimir channel contributes no entropy production. -/
@[rep_depth thermo]
theorem casimir_channel_zero :
    C.reversibleEntropyProduction = 0 :=
  C.reversibleEntropyProduction_eq_zero

/--
Finite Souriau-Onsager second-law projection:
the total entropy production is nonnegative under the explicit Casimir and PSD
response hypotheses carried by the context.
-/
@[rep_depth thermo]
theorem onsager_total_entropy_nonnegative :
    0 ≤ C.totalEntropyProduction :=
  C.totalEntropyProduction_nonneg

end MetriplecticContext

end InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
