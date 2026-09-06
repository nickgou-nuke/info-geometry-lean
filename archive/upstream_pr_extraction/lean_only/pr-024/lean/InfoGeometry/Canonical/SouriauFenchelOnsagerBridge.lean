import InfoGeometry.Canonical.SouriauMetriplecticContext
import InfoGeometry.Canonical.SouriauCasimirInvariant
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

/-! ## Operatorial Fenchel-Legendre lift along affine coadjoint orbits -/

/--
Operatorial Fenchel defect.

This is the Lie-side analogue of the scalar Fenchel gap
`ψ(θ) + φ(η) - θη`.

Only an additive abelian group is required for the scalar target.
-/
def operatorFenchelGap
    {𝕜 Lie LieDual : Type*} [AddCommGroup 𝕜]
    (pair : LieDual → Lie → 𝕜)
    (massieu : Lie → 𝕜)
    (entropy : LieDual → 𝕜)
    (Q : LieDual) (ξ : Lie) : 𝕜 :=
  massieu ξ + entropy Q - pair Q ξ

/--
Operatorial Legendre-Fenchel gap invariance under paired adjoint /
affine-coadjoint transport.

With
`Ad#_g Q = coAd_g Q + θ(g)`,
this proves
`Gap(Ad#_g Q, Ad_g ξ) = Gap(Q, ξ)`.

The proof is only additive cancellation of the Souriau cocycle contribution.
-/
theorem operatorFenchelGap_affineCoAd_invariant
    {𝕜 G Lie LieDual : Type*}
    [AddCommGroup 𝕜] [AddCommGroup LieDual]
    (Ad : G → Lie → Lie)
    (coAd : G → LieDual → LieDual)
    (theta : G → LieDual)
    (pair : LieDual → Lie → 𝕜)
    (massieu : Lie → 𝕜)
    (entropy : LieDual → 𝕜)
    (hpair_add :
      ∀ Q R ξ,
        pair (Q + R) ξ = pair Q ξ + pair R ξ)
    (hpair_coAd_Ad :
      ∀ g Q ξ,
        pair (coAd g Q) (Ad g ξ) = pair Q ξ)
    (hmassieu_affine :
      ∀ g ξ,
        massieu (Ad g ξ) =
          massieu ξ + pair (theta g) (Ad g ξ))
    (hentropy_affine :
      ∀ g Q,
        entropy (coAd g Q + theta g) = entropy Q)
    (g : G) (Q : LieDual) (ξ : Lie) :
    operatorFenchelGap pair massieu entropy
        (coAd g Q + theta g) (Ad g ξ)
      =
    operatorFenchelGap pair massieu entropy Q ξ := by
  unfold operatorFenchelGap
  rw [hmassieu_affine g ξ]
  rw [hentropy_affine g Q]
  rw [hpair_add (coAd g Q) (theta g) (Ad g ξ)]
  rw [hpair_coAd_Ad g Q ξ]
  abel

/--
Entropy invariance from the operatorial Legendre-Fenchel readout.

Assume entropy is represented by the generalized Legendre transform
`S(Q) = <Q, β(Q)> - Φ(β(Q))`.
-/
theorem operatorLegendre_entropy_affineCoAd_invariant
    {𝕜 G Lie LieDual : Type*}
    [AddCommGroup 𝕜] [AddCommGroup LieDual]
    (Ad : G → Lie → Lie)
    (coAd : G → LieDual → LieDual)
    (theta : G → LieDual)
    (pair : LieDual → Lie → 𝕜)
    (massieu : Lie → 𝕜)
    (entropy : LieDual → 𝕜)
    (beta : LieDual → Lie)
    (hentropy_legendre :
      ∀ Q,
        entropy Q = pair Q (beta Q) - massieu (beta Q))
    (hbeta_affine :
      ∀ g Q,
        beta (coAd g Q + theta g) = Ad g (beta Q))
    (hpair_add :
      ∀ Q R ξ,
        pair (Q + R) ξ = pair Q ξ + pair R ξ)
    (hpair_coAd_Ad :
      ∀ g Q ξ,
        pair (coAd g Q) (Ad g ξ) = pair Q ξ)
    (hmassieu_affine :
      ∀ g ξ,
        massieu (Ad g ξ) =
          massieu ξ + pair (theta g) (Ad g ξ))
    (g : G) (Q : LieDual) :
    entropy (coAd g Q + theta g) = entropy Q := by
  rw [hentropy_legendre (coAd g Q + theta g)]
  rw [hentropy_legendre Q]
  rw [hbeta_affine g Q]
  rw [hpair_add (coAd g Q) (theta g) (Ad g (beta Q))]
  rw [hpair_coAd_Ad g Q (beta Q)]
  rw [hmassieu_affine g (beta Q)]
  abel

/--
Contact is preserved under affine coadjoint transport.

If the operatorial Fenchel gap vanishes at `(Q, ξ)`, then it also vanishes at
`(coAd g Q + theta g, Ad g ξ)` under the same affine-covariance hypotheses.
-/
theorem operatorFenchel_contact_affineCoAd_preserved
    {𝕜 G Lie LieDual : Type*}
    [AddCommGroup 𝕜] [AddCommGroup LieDual]
    (Ad : G → Lie → Lie)
    (coAd : G → LieDual → LieDual)
    (theta : G → LieDual)
    (pair : LieDual → Lie → 𝕜)
    (massieu : Lie → 𝕜)
    (entropy : LieDual → 𝕜)
    (hpair_add :
      ∀ Q R ξ,
        pair (Q + R) ξ = pair Q ξ + pair R ξ)
    (hpair_coAd_Ad :
      ∀ g Q ξ,
        pair (coAd g Q) (Ad g ξ) = pair Q ξ)
    (hmassieu_affine :
      ∀ g ξ,
        massieu (Ad g ξ) =
          massieu ξ + pair (theta g) (Ad g ξ))
    (hentropy_affine :
      ∀ g Q,
        entropy (coAd g Q + theta g) = entropy Q)
    (g : G) (Q : LieDual) (ξ : Lie)
    (hcontact : operatorFenchelGap pair massieu entropy Q ξ = 0) :
    operatorFenchelGap pair massieu entropy
        (coAd g Q + theta g) (Ad g ξ) = 0 := by
  rw [operatorFenchelGap_affineCoAd_invariant
      Ad coAd theta pair massieu entropy
      hpair_add hpair_coAd_Ad hmassieu_affine hentropy_affine g Q ξ]
  exact hcontact

/--
Affine coadjoint transport preserves the zero-Fenchel-contact locus exactly.

This is the bidirectional (`↔`) form of contact preservation:
the transported pair has zero gap iff the original pair has zero gap.
-/
theorem operatorFenchel_contact_affineCoAd_iff
    {𝕜 G Lie LieDual : Type*}
    [AddCommGroup 𝕜] [AddCommGroup LieDual]
    (Ad : G → Lie → Lie)
    (coAd : G → LieDual → LieDual)
    (theta : G → LieDual)
    (pair : LieDual → Lie → 𝕜)
    (massieu : Lie → 𝕜)
    (entropy : LieDual → 𝕜)
    (hpair_add :
      ∀ Q R ξ,
        pair (Q + R) ξ = pair Q ξ + pair R ξ)
    (hpair_coAd_Ad :
      ∀ g Q ξ,
        pair (coAd g Q) (Ad g ξ) = pair Q ξ)
    (hmassieu_affine :
      ∀ g ξ,
        massieu (Ad g ξ) =
          massieu ξ + pair (theta g) (Ad g ξ))
    (hentropy_affine :
      ∀ g Q,
        entropy (coAd g Q + theta g) = entropy Q)
    (g : G) (Q : LieDual) (ξ : Lie) :
    operatorFenchelGap pair massieu entropy
        (coAd g Q + theta g) (Ad g ξ) = 0
      ↔
    operatorFenchelGap pair massieu entropy Q ξ = 0 := by
  simpa [operatorFenchelGap_affineCoAd_invariant
      Ad coAd theta pair massieu entropy
      hpair_add hpair_coAd_Ad hmassieu_affine hentropy_affine g Q ξ]

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

/--
Concrete bridge contact equation:
the Souriau Massieu value at the bridge point satisfies the Fenchel contact
identity with the dual coordinate.
-/
@[rep_depth transport]
theorem souriau_contact_equation :
    souriauMassieuPotential C.M C.T
      + C.model.φ (C.model.dualCoord C.theta)
      - C.theta * C.model.dualCoord C.theta = 0 := by
  have hcb := C.souriauMassieu_contact_balance
  linarith

/--
Concrete bridge contact defect is zero.

This is the finite instantiation of the Legendre-contact/Fenchel bridge at the
selected Souriau Massieu basepoint.
-/
@[rep_depth transport]
theorem souriau_fenchelGap_eq_zero_at_bridge_contact :
    C.model.massieu C.theta
      + C.model.φ (C.model.dualCoord C.theta)
      - C.theta * C.model.dualCoord C.theta = 0 := by
  have hgap0 := C.fenchelGap_eq_zero_at_contact
  simpa [InfoGeometry.LogPotential.LegendreModel.fenchelGap] using hgap0

/--
Primal Bregman/Fenchel readout at the Souriau bridge basepoint.
-/
@[rep_depth transport]
theorem primalBregman_eq_fenchelGap_at_bridge_base
    (θ : ℝ)
    (hgrad : C.model.grad C.theta = deriv C.model.L.ψ C.theta) :
    C.model.primalBregman θ C.theta =
      C.model.fenchelGap θ (C.model.dualCoord C.theta) :=
  C.model.primalBregman_eq_fenchelGap_at_dualCoord_of_grad_eq_deriv θ C.theta hgrad

/--
Finite convex consequence at the Souriau bridge basepoint:
the primal Bregman divergence is nonnegative.
-/
@[rep_depth transport]
theorem primalBregman_nonneg_at_bridge_base
    (θ : ℝ)
    (hgrad : C.model.grad C.theta = deriv C.model.L.ψ C.theta) :
    0 ≤ C.model.primalBregman θ C.theta :=
  C.model.primalBregman_nonneg_of_grad_eq_deriv θ C.theta hgrad

/--
Bridge-contact specialization: primal Bregman divergence vanishes on the
diagonal at the selected Souriau basepoint.
-/
@[rep_depth transport]
theorem primalBregman_self_at_bridge_base :
    C.model.primalBregman C.theta C.theta = 0 := by
  unfold InfoGeometry.LogPotential.LegendreModel.primalBregman
  simp [InfoGeometry.LogPotential.bregman, InfoGeometry.bregmanDiv]

/--
Transverse Fenchel defect readout at the Souriau bridge basepoint.

This is the dual-flat transverse channel decomposition at fixed basepoint.
-/
@[rep_depth transport]
theorem transverse_fenchel_defect_at_bridge_base
    (eta : ℝ) :
    C.model.fenchelGap C.theta eta =
      C.model.φ eta - C.model.φ (C.model.dualCoord C.theta)
        + C.theta * (C.model.dualCoord C.theta - eta) :=
  C.model.fenchelGap_eq_dual_defect_add_pairing_defect C.theta eta

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

/-- Orbit-tangent entropy channel readout: entropy difference along a symmetry
orbit is exactly zero. -/
@[rep_depth transport]
theorem entropy_difference_on_state_orbit_eq_zero
    (s : Sym) (x : State) :
    C.entropy (C.data.moment (C.stateAction s x))
      - C.entropy (C.data.moment x) = 0 := by
  rw [C.entropy_invariant_on_state_orbit s x]
  ring

end CoadjointEntropySymmetryContext

end InfoGeometry.Canonical.SouriauFenchelOnsagerBridge
