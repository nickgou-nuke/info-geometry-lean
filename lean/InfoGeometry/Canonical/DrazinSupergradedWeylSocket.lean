import Mathlib
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.DrazinFierzBridge
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.SocketTarget

/-!
# Drazin supergraded Weyl socket

This module records the theorem-safe supergraded interpretation of the
expectation-only Drazin filter.

The intended dictionary is:

* `Δ₀` and `Δ₁₀` are killed by the Drazin filter;
* `Δ₁₀` may be interpreted as ghost/nilpotent noise only through an explicit
  supergraded compatibility assumption;
* `Δ₁₁` is the stable scaled-projector sector;
* a Weyl/KMS/Jaynes state assigns physical scale by expectation values, not
  traces.

No theorem here claims that all fermions are nilpotent noise, that CAR follows
from Drazin alone, or that CCR/CAR coupling is automatic.  Those identifications
are compatibility data.

In particular, this file keeps the key distinction explicit:

```text
odd nilpotent primitive / ghost direction  -> killed sector
even bilinear / chiral projector / current -> stable sector
```
-/

noncomputable section

namespace InfoGeometry.Canonical.DrazinSupergradedWeylSocket

open MeasureTheory
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.DrazinFierzBridge
open InfoGeometry.Canonical.DrazinModularPersistence

/-! ## 1. Supergraded labels and compatibility assumptions -/

/--
A supergrading implemented by an involutive algebra automorphism.

Even elements satisfy `γ x = x`; odd elements satisfy `γ x = -x`.
Oddness is not nilpotence.  Nilpotence is a separate predicate below.
-/
@[rep_depth operator]
structure SuperGrading
    (Obs : Type*) [Ring Obs] where
  gamma : Obs ≃+* Obs
  involutive :
    ∀ x : Obs, gamma (gamma x) = x

/-- Even element of a supergraded observable algebra. -/
@[rep_depth operator]
def IsEven
    {Obs : Type*} [Ring Obs]
    (G : SuperGrading Obs)
    (x : Obs) : Prop :=
  G.gamma x = x

/-- Odd element of a supergraded observable algebra. -/
@[rep_depth operator]
def IsOdd
    {Obs : Type*} [Ring Obs]
    (G : SuperGrading Obs)
    (x : Obs) : Prop :=
  G.gamma x = -x

/-- Bare nilpotent/noise predicate. -/
@[rep_depth operator]
def IsNilpotentNoise
    {Obs : Type*} [Mul Obs] [Zero Obs]
    (x : Obs) : Prop :=
  x * x = 0

/--
Primitive fermionic/ghost-like channel.

This models a raw odd nilpotent direction.  It is not the same thing as a
physical fermionic observable.
-/
@[rep_depth operator]
structure PrimitiveFermion
    (Obs : Type*) [Ring Obs] where
  grading : SuperGrading Obs
  op : Obs
  odd :
    IsOdd grading op
  nilpotent :
    IsNilpotentNoise op

/--
Stable scaled projector: the trace-free `Δ₁₁` pattern `P² = λ P`.
-/
@[rep_depth operator]
structure StableScaledProjector
    (Obs : Type*) [Mul Obs] [SMul ℂ Obs] where
  P : Obs
  lambda : ℂ
  lambda_ne_zero :
    lambda ≠ 0
  scaled_idempotent :
    P * P = lambda • P

/--
Physical fermionic observable candidate: even and stable.

Typical intended instances are number operators, chiral projectors, currents,
and Fierz bilinears.
-/
@[rep_depth operator]
structure StableFermionObservable
    (Obs : Type*) [Ring Obs] [SMul ℂ Obs] where
  grading : SuperGrading Obs
  obs : Obs
  even :
    IsEven grading obs
  stable :
    StableScaledProjector Obs
  obs_eq :
    obs = stable.P

/-- Drazin killing law for a primitive nilpotent input. -/
@[rep_depth operator]
def DrazinKillsPrimitiveNilpotent
    {Obs : Type*} [Ring Obs] [Star Obs]
    (D : DrazinSupportData Obs) : Prop :=
  D.A * D.A = 0 → D.AD = 0

namespace PrimitiveFermion

variable {Obs : Type*} [Ring Obs]

/-- A primitive fermion carries its nilpotent/noise witness without requiring a
separate square-zero hypothesis at the call site. -/
@[rep_depth operator]
theorem nilpotentNoise
    (F : PrimitiveFermion Obs) :
    IsNilpotentNoise F.op :=
  F.nilpotent

/-- A primitive fermion carries its oddness witness without requiring a separate
supergrading hypothesis at the call site. -/
@[rep_depth operator]
theorem odd_readback
    (F : PrimitiveFermion Obs) :
    IsOdd F.grading F.op :=
  F.odd

end PrimitiveFermion

/--
Constructive Drazin-kill route for a primitive fermion input: callers can pass
an explicit `PrimitiveFermion` package instead of re-supplying the bare
square-zero proof `D.A * D.A = 0`, when the Drazin input is definitionally the
primitive operator.
-/
@[rep_depth operator]
theorem drazinKillsPrimitiveFermion
    {Obs : Type*} [Ring Obs] [Star Obs]
    (D : DrazinSupportData Obs)
    (hD : DrazinKillsPrimitiveNilpotent D)
    (F : PrimitiveFermion Obs)
    (hA : D.A = F.op) :
    D.AD = 0 := by
  exact hD (by simpa [hA] using F.nilpotent)

/--
Drazin preservation law for a stable scaled projector.

For `P² = λP`, the rank-one Drazin formula is represented as
`λ⁻¹ * λ⁻¹ • P`.
-/
@[rep_depth operator]
def DrazinPreservesStableProjector
    {Obs : Type*} [Mul Obs] [SMul ℂ Obs]
    (P : StableScaledProjector Obs)
    (AD : Obs) : Prop :=
  AD = ((P.lambda)⁻¹ * (P.lambda)⁻¹) • P.P

/--
Supergraded role assigned to a local observable/fiber.

`nilpotentGhost` is deliberately separated from `fermionic`: a theorem-safe
formalization must not identify all odd/CAR data with ghost noise.
-/
@[rep_depth operator]
inductive SupergradedRole where
  | bosonic
  | fermionic
  | nilpotentGhost
  | stableComposite
  deriving DecidableEq, Repr

/--
Compatibility assumption connecting a supergraded interpretation to algebraic
fiber strata.

This is an assumption packet: it says which fibers are to be read as ghosts,
stable fermion bilinears, or bosonic kernels in a concrete model.
-/
@[rep_depth operator]
structure SupergradedStratumCompatibility
    (Φ : BSExpectationPhi)
    (σH : Set ℝ) where
  role : ℝ → SupergradedRole
  ghost_iff_delta10 :
    ∀ t : ℝ,
      t ∈ σH →
        role t = SupergradedRole.nilpotentGhost ↔ Φ.IsNilpotentNoiseFiber t
  stableComposite_iff_delta11 :
    ∀ t : ℝ,
      t ∈ σH →
        role t = SupergradedRole.stableComposite ↔ Φ.IsStableRankOneFiber t
  bosonicKernel_iff_delta0 :
    ∀ t : ℝ,
      t ∈ σH →
        role t = SupergradedRole.bosonic ↔ Φ.IsZeroFiber t

/-! ## 2. Drazin filter readbacks on supergraded strata -/

/--
Supergraded Drazin filter socket.

The actual Drazin action is supplied by the trace-free Böttcher--Spitkovsky
fiber data.  The supergraded meaning of the strata is supplied separately.
-/
@[socket_debt_tag, rep_depth operator]
structure SupergradedDrazinFilterSocket
    (Φ : BSExpectationPhi)
    (νH : Measure ℝ)
    (σH : Set ℝ) where
  drazin :
    BSExpectationPhi.NoTraceDrazinData Φ νH σH
  supergraded :
    SupergradedStratumCompatibility Φ σH

namespace SupergradedDrazinFilterSocket

variable {Φ : BSExpectationPhi}
variable {νH : Measure ℝ}
variable {σH : Set ℝ}
variable (S : SupergradedDrazinFilterSocket Φ νH σH)

/-- The zero stratum is killed by the supplied Drazin filter. -/
@[rep_depth operator]
theorem zero_stratum_killed_ae :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta0 σH →
        S.drazin.drazinFiber t = 0 :=
  S.drazin.zeroLaw

/-- The nilpotent/ghost stratum is killed by the supplied Drazin filter. -/
@[rep_depth operator]
theorem nilpotent_stratum_killed_ae :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta10 σH →
        S.drazin.drazinFiber t = 0 :=
  S.drazin.nilpotentLaw

/-- Stable scaled-projector fibers are retained by the supplied rank-one law. -/
@[rep_depth operator]
theorem stable_rank_one_filtered_ae :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta11 σH →
        S.drazin.drazinFiber t =
          ((S.drazin.lambdaRankOne t)⁻¹ * (S.drazin.lambdaRankOne t)⁻¹) •
            Φ.fiber t :=
  S.drazin.stableRankOneLaw

/-- Invertible fibers are inverted by the supplied Drazin filter. -/
@[rep_depth operator]
theorem invertible_stratum_inverted_ae :
    ∀ᵐ t ∂νH,
      t ∈ Φ.Delta2 σH →
        ∃ invM : FiberMatrix,
          Φ.fiber t * invM = 1 ∧
          invM * Φ.fiber t = 1 ∧
          S.drazin.drazinFiber t = invM :=
  S.drazin.invertibleLaw

end SupergradedDrazinFilterSocket

/-! ## 3. Weyl/expectation scale readouts -/

/--
Expectation scale of an observable.

This is the Weyl/KMS/Jaynes readout primitive.  It is not a trace.
-/
@[rep_depth operator]
def weylExpectationScale
    {Obs : Type*} [Ring Obs] [Star Obs]
    (φ : RealExpectationState Obs)
    (x : Obs) : ℝ :=
  φ.expect x

/-- Scale assigned to the Drazin support horizon. -/
@[rep_depth operator]
def drazinHorizonScale
    {Obs : Type*} [Ring Obs] [Star Obs]
    (φ : RealExpectationState Obs)
    (D : DrazinSupportData Obs) : ℝ :=
  φ.expect D.p

/-- Scale assigned to the Drazin-filtered inverse/output. -/
@[rep_depth operator]
def drazinFilteredScale
    {Obs : Type*} [Ring Obs] [Star Obs]
    (φ : RealExpectationState Obs)
    (D : DrazinSupportData Obs) : ℝ :=
  φ.expect D.AD

/-! ## 4. CAR/CCR compatibility as explicit model data -/

/--
Model-specific compatibility between Drazin-stabilized data and CAR/CCR
readouts.

This is intentionally an assumption structure.  The Drazin filter supplies
operator stabilization; a concrete representation must still prove that its
surviving sector satisfies the desired CAR/CCR laws.
-/
@[rep_depth operator]
structure DrazinCARCCRCompatibilityAssumption
    (Obs : Type*) [Ring Obs] [Star Obs] where
  state :
    RealExpectationState Obs
  grading :
    SuperGrading Obs
  boundary :
    DrazinSupportData Obs
  primitiveFermion :
    Obs → Prop
  stableFermionObservable :
    Obs → Prop
  carObservable :
    Obs → Prop
  ccrObservable :
    Obs → Prop
  ghostObservable :
    Obs → Prop
  ghost_square_zero :
    ∀ x : Obs,
      ghostObservable x →
        x * x = 0
  primitive_fermion_is_odd :
    ∀ x : Obs,
      primitiveFermion x →
        IsOdd grading x
  primitive_fermion_is_nilpotent :
    ∀ x : Obs,
      primitiveFermion x →
        x * x = 0
  stable_fermion_is_even :
    ∀ x : Obs,
      stableFermionObservable x →
        IsEven grading x
  stable_fermion_lives_on_horizon :
    ∀ x : Obs,
      stableFermionObservable x →
        boundary.p * x * boundary.p = x
  car_lives_on_horizon :
    ∀ x : Obs,
      carObservable x →
        boundary.p * x * boundary.p = x
  ccr_scale_readout :
    Obs → ℝ
  ccr_scale_eq_expectation :
    ∀ x : Obs,
      ccrObservable x →
        ccr_scale_readout x = state.expect x

namespace DrazinCARCCRCompatibilityAssumption

variable {Obs : Type*} [Ring Obs] [Star Obs]
variable (K : DrazinCARCCRCompatibilityAssumption Obs)

/-- Ghost observables are square-zero by the supplied compatibility assumption. -/
@[rep_depth operator]
theorem ghost_is_square_zero
    (x : Obs)
    (hx : K.ghostObservable x) :
    x * x = 0 :=
  K.ghost_square_zero x hx

/-- Primitive fermion channels are odd by compatibility. -/
@[rep_depth operator]
theorem primitive_fermion_odd_readback
    (x : Obs)
    (hx : K.primitiveFermion x) :
    IsOdd K.grading x :=
  K.primitive_fermion_is_odd x hx

/-- Primitive fermion channels are nilpotent by compatibility. -/
@[rep_depth operator]
theorem primitive_fermion_nilpotent_readback
    (x : Obs)
    (hx : K.primitiveFermion x) :
    x * x = 0 :=
  K.primitive_fermion_is_nilpotent x hx

/-- Stable fermionic observables are even by compatibility. -/
@[rep_depth operator]
theorem stable_fermion_even_readback
    (x : Obs)
    (hx : K.stableFermionObservable x) :
    IsEven K.grading x :=
  K.stable_fermion_is_even x hx

/-- Stable fermionic observables live on the Drazin horizon by compatibility. -/
@[rep_depth operator]
theorem stable_fermion_horizon_localized
    (x : Obs)
    (hx : K.stableFermionObservable x) :
    K.boundary.p * x * K.boundary.p = x :=
  K.stable_fermion_lives_on_horizon x hx

/-- CAR observables live on the supplied Drazin horizon by compatibility. -/
@[rep_depth operator]
theorem car_observable_horizon_localized
    (x : Obs)
    (hx : K.carObservable x) :
    K.boundary.p * x * K.boundary.p = x :=
  K.car_lives_on_horizon x hx

/-- CCR scale is an expectation value by compatibility. -/
@[rep_depth operator]
theorem ccr_scale_is_expectation
    (x : Obs)
    (hx : K.ccrObservable x) :
    K.ccr_scale_readout x = K.state.expect x :=
  K.ccr_scale_eq_expectation x hx

end DrazinCARCCRCompatibilityAssumption

end InfoGeometry.Canonical.DrazinSupergradedWeylSocket
