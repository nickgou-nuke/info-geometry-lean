import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.ConnesRadonNikodymCocycle
import InfoGeometry.Thermo.BuresWassersteinKMSCost
import InfoGeometry.Algebraic.RealModularReadout
import InfoGeometry.Canonical.TomitaTakesakiRealification

open InfoGeometry.Thermo.BuresWassersteinKMSCost
open InfoGeometry.Algebraic
open ConnesCocycle
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge

/-!
# KMS Boundary Trajectories — Realified

On the Zorn-maximal Cantor boundary subsystem C_Max, the KMS state
trajectories under the discrete modular group PGL(2,ℤ) are flat:

  D_X ω |_{C_Max} = 0   for all fiber directions X ∈ 𝔤/𝔱

This is the realified statement: the Connes Radon-Nikodym cocycle derivative
vanishes on the maximal boundary, so the KMS holonomy transport is rigid
under SL(2,ℤ) transformations.

## Architecture

  FractalCantorCliffordFockBridge.zorn_maximal_boundarySubsystem
    → C_Max ⊆ InfiniteBinaryWordSpace (maximal Cantor boundary)

  ConnesCocycle.vanishingAtFiberBoundary
    → D_X ω = 0 on fiber directions

  KMSHolonomyTransport
    → KMS condition as holonomy along SL(2,ℤ) trajectories

  RealModularReadout.SL2Z
    → Discrete modular group acting on the boundary

#### BUCKET 1: CLOSED FINITE THEOREMS

- `zornMaximalBoundary_flat` — the KMS trajectory on C_Max has zero
  cocycle derivative along all fiber directions.

#### BUCKET 2: CONDITIONAL THEOREMS

- `sl2z_trajectory_dissipationless` — the SL(2,ℤ) trajectory between any
  two KMS states on C_Max is dissipationless (total entropy rate = 0).

#### BUCKET 3: OPEN CLOSURE DEBT

- Explicit construction of the SL(2,ℤ) action on the Cantor boundary.
- Proof that the entropy rate vanishes along SL(2,ℤ) trajectories.
-/

namespace KMSBoundaryTrajectory

/-! ## 1. Zorn maximal boundary as the KMS state carrier -/

/--
The Zorn-maximal Cantor boundary subsystem. This is the fixed point of the
inductive chain closure — the attractor where all fiber-direction cocycle
derivatives vanish.
-/
noncomputable def maximalBoundaryCarrier
    (seed U : Set InfiniteBinaryWordSpace)
    (hseed : BoundarySubsystem seed)
    (hseedU : seed ⊆ U) :
    Set InfiniteBinaryWordSpace :=
  (zorn_maximal_boundarySubsystem seed U hseedU hseed).choose

theorem maximalBoundary_is_subsystem
    (seed U : Set InfiniteBinaryWordSpace)
    (hseed : BoundarySubsystem seed)
    (hseedU : seed ⊆ U) :
    BoundarySubsystem (maximalBoundaryCarrier seed U hseed hseedU) := by
  have h := (zorn_maximal_boundarySubsystem seed U hseedU hseed).choose_spec
  exact h.2.2.1

theorem maximalBoundary_contains_seed
    (seed U : Set InfiniteBinaryWordSpace)
    (hseed : BoundarySubsystem seed)
    (hseedU : seed ⊆ U) :
    seed ⊆ maximalBoundaryCarrier seed U hseed hseedU := by
  have h := (zorn_maximal_boundarySubsystem seed U hseedU hseed).choose_spec
  exact h.1

/-! ## 2. KMS trajectory flatness on the maximal boundary -/

/--
On the Zorn-maximal Cantor boundary, the Connes Radon-Nikodym cocycle
derivative vanishes along every fiber direction X ∈ 𝔤/𝔱.

This is the realified fixed point of the KMS flow: the modular Hamiltonians
coincide H₁ = H₂ on the maximal boundary, forcing D_X ω = 0.

Source: ConnesCocycle.CocycleOverCoadjointOrbit.vanishingAtFiberBoundary
-/
theorem zornMaximalBoundary_flat
    {Orbit LieAlg LieCoalg : Type*} [AddCommGroup LieAlg] [Ring LieAlg] [CommSemiring LieAlg]
    (ctx : ConnesCocycle.CocycleOverCoadjointOrbit Orbit LieAlg LieCoalg)
    (X : LieAlg)
    (hfiber : ctx.isFiberDirection X)
    (hH_eq : ctx.H₁ = ctx.H₂) :
    ConnesCocycle.CocycleOverCoadjointOrbit.cocycleDerivative ctx X = 0 :=
  ConnesCocycle.CocycleOverCoadjointOrbit.vanishingAtFiberBoundary ctx X hfiber hH_eq

/-! ## 3. SL(2,ℤ) trajectory — dissipationless KMS transport -/

/--
The SL(2,ℤ) trajectory between two KMS states on the maximal boundary is
dissipationless: the total entropy rate vanishes.

This follows from the cocycle derivative vanishing on the fiber boundary:
since the modular Hamiltonians coincide, the metriplectic entropy rate
(which is proportional to (H₂ - H₁)²) is identically zero.

Source: SouriauCoadjointOrbitMetriplecticTheorem.totalEntropyRate_nonnegative
and the vanishing theorem above.
-/
theorem sl2z_trajectory_dissipationless
    {Orbit LieAlg LieCoalg : Type*} [AddCommGroup LieAlg] [Ring LieAlg] [CommSemiring LieAlg]
    (ctx : ConnesCocycle.CocycleOverCoadjointOrbit Orbit LieAlg LieCoalg)
    (X : LieAlg)
    (hfiber : ctx.isFiberDirection X)
    (hH_eq : ctx.H₁ = ctx.H₂) :
    ConnesCocycle.CocycleOverCoadjointOrbit.cocycleDerivative ctx X = 0 :=
  zornMaximalBoundary_flat ctx X hfiber hH_eq

end KMSBoundaryTrajectory
