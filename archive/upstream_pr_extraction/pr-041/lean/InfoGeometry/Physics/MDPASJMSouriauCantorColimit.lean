import Mathlib.Tactic
import InfoGeometry.Physics.MDPASJMSouriauDigest
import InfoGeometry.Canonical.FractalCantorCliffordFockBridge
import InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge

/-!
# MDPAS/JMSouriau direct limit as Cantor fractal boundary

The repo already owns the symbolic Cantor fractal limit carrier in
`FractalCantorCliffordFockBridge` as the infinite binary boundary
`(ℕ → Bool) = ℕ → Bool`, together with prefix/tail reconstruction.

This file proves the missing bridge: any compatible finite-stage MDPAS/JM tower
whose finite stages have compatible Cantor addresses descends uniquely through
the genuine quotient direct-limit carrier to the established Cantor boundary.

#### BUCKET 1: CLOSED FINITE THEOREMS

* finite-stage compatible addresses descend through the quotient carrier;
* finite Cantor-prefix projections read back from every finite stage;
* every descended Cantor point reconstructs from every finite prefix and tail.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

The bridge is conditional on an explicit `MDPASCantorAddressSystem`, whose
`address_bond` field is a concrete equation over the bonding maps.

#### BUCKET 3: OPEN CLOSURE DEBT

No theorem here constructs the full Stone dual equivalence, a topological
compact Hausdorff instance, or an analytic Cantor measure.  The proved carrier
is the repo-owned symbolic Cantor boundary and its finite-prefix inverse-system
readback.
-/

namespace InfoGeometry
namespace Physics
namespace MDPASJMSouriauCantorColimit

open InfoGeometry.Physics.MDPASJMSouriauDigest
open InfoGeometry.Physics.MDPASJMSouriauDigest.FiniteMDPASJMDirectSystem
open InfoGeometry.Canonical.FractalCantorCliffordFockBridge
open InfoGeometry.Canonical.UHFBooleanProjectionCantorBridge
open InfoGeometry.Topology.ThermodynamicGauge

/-- The Turing-tape carrier is the same repo-owned Cantor boundary: infinite binary words. -/
abbrev TuringTape := (ℕ → Bool)

/-- A finite observation window on an infinite Turing tape. -/
def turingWindow (n : ℕ) (τ : TuringTape) : List Bool :=
  boundaryPrefix n τ

@[simp] theorem turingWindow_length (n : ℕ) (τ : TuringTape) :
    (turingWindow n τ).length = n := by
  simp [turingWindow]

/-- The zero-width Turing observation sees the empty prefix. -/
@[simp] theorem turingWindow_zero (τ : TuringTape) :
    turingWindow 0 τ = [] := by
  rfl

/--
A finite MDPAS/JM direct system equipped with compatible addresses in the
repo-owned Cantor fractal boundary.
-/
structure MDPASCantorAddressSystem
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (Op : Type*) [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]
    (State LieAlgebra LieDual : Type*) [AddMonoid LieAlgebra] where
  direct : FiniteMDPASJMDirectSystem ι Op State LieAlgebra LieDual
  address : ∀ _n : ℕ, Op → (ℕ → Bool)
  address_bond : ∀ n x, address (n + 1) (direct.bond n x) = address n x

namespace MDPASCantorAddressSystem

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {Op : Type*} [NormedRing Op] [NormedAlgebra ℝ Op] [CompleteSpace Op]
variable {State LieAlgebra LieDual : Type*} [AddMonoid LieAlgebra]

/-- The proper infinite carrier is the established Cantor fractal boundary. -/
abbrev ProperCantorCarrier (_T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual) : Type :=
  (ℕ → Bool)

/-- The unique map from the MDPAS quotient carrier into the Cantor fractal limit. -/
def cantorLimitMap (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual) :
    FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct → ProperCantorCarrier T :=
  compatibleLift T.direct T.address T.address_bond

/-- Physics-facing name: the MDPAS direct-limit carrier reads as an infinite Turing tape. -/
def turingTapeReadout (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual) :
    FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct → TuringTape :=
  T.cantorLimitMap

/-- The Turing tape readout is definitionally the Cantor direct-limit map. -/
theorem turingTapeReadout_eq_cantorLimitMap
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual) :
    T.turingTapeReadout = T.cantorLimitMap :=
  rfl

/-- The Cantor limit map has the prescribed finite-stage values. -/
theorem cantorLimitMap_ofStage
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (n : ℕ) (x : Op) :
    T.cantorLimitMap (ofStage T.direct n x) = T.address n x :=
  compatibleLift_ofStage T.direct T.address T.address_bond n x

/-- The map to the Cantor boundary is unique among compatible finite-stage maps. -/
theorem cantorLimitMap_unique
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (Φ : FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct → (ℕ → Bool))
    (hΦ : ∀ n x, Φ (ofStage T.direct n x) = T.address n x) :
    Φ = T.cantorLimitMap :=
  compatibleLift_unique T.direct T.address T.address_bond Φ hΦ

/-- Every point in the Cantor limit has the repo-owned head/tail fractal recursion. -/
theorem cantorLimitMap_recursive_decomposition
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (q : FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct) :
    T.cantorLimitMap q =
      boundaryCons (boundaryHead (T.cantorLimitMap q))
        (boundaryTail (T.cantorLimitMap q)) :=
  boundary_recursive_decomposition (T.cantorLimitMap q)

/-- Every Cantor-limit image reconstructs from finite prefixes at every depth. -/
theorem cantorLimitMap_finite_reconstruction
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (q : FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct)
    (n : ℕ) :
    T.cantorLimitMap q =
      boundaryConsList (boundaryPrefix n (T.cantorLimitMap q))
        (boundaryIterateTail n (T.cantorLimitMap q)) :=
  boundary_finite_reconstruction n (T.cantorLimitMap q)

/-- The Cantor limit also factors through the repo-owned Boolean Bratteli path space. -/
def cantorBratteliPathMap (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual) :
    FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct → CoherentBitPath :=
  boundaryToCoherentPath ∘ T.cantorLimitMap

/-- The Bratteli path map recovers the Cantor limit under the proven equivalence. -/
theorem cantorBratteliPathMap_recover
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (q : FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct) :
    coherentPathEquivCantorBoundary (T.cantorBratteliPathMap q) = T.cantorLimitMap q := by
  simpa [cantorBratteliPathMap] using
    coherentPathToBoundary_boundaryToCoherentPath (T.cantorLimitMap q)

/-- Finite-stage addresses become finite Bratteli prefixes after the Boolean lift. -/
theorem cantorBratteliPathMap_ofStage
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (n : ℕ) (x : Op) :
    boundaryPrefix n (coherentPathEquivCantorBoundary (T.cantorBratteliPathMap (ofStage T.direct n x))) =
      boundaryPrefix n (T.address n x) := by
  rw [cantorBratteliPathMap_recover T (ofStage T.direct n x)]
  exact congrArg
    (InfoGeometry.Canonical.FractalCantorCliffordFockBridge.boundaryPrefix n)
    (cantorLimitMap_ofStage T n x)

/-- The Witt bits in the UHF Bratteli path model are exactly the Cantor prefixes of the MDPAS limit. -/
theorem mdpas_witt_bits_eq_cantor_prefix
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (q : FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct) (n : ℕ) :
    boundaryPrefix n (coherentPathEquivCantorBoundary (T.cantorBratteliPathMap q)) =
      boundaryPrefix n (T.cantorLimitMap q) := by
  simpa using congrArg (boundaryPrefix n) (cantorBratteliPathMap_recover T q)

/-- Finite prefix projection from the quotient carrier to the depth-`n` Cantor cylinder. -/
def cantorPrefixProjection
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (n : ℕ) :
    FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct → List Bool :=
  fun q => boundaryPrefix n (T.cantorLimitMap q)

@[simp] theorem cantorPrefixProjection_length
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (n : ℕ)
    (q : FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct) :
    (T.cantorPrefixProjection n q).length = n := by
  simp [cantorPrefixProjection]

@[simp] theorem cantorPrefixProjection_zero
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (q : FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct) :
    T.cantorPrefixProjection 0 q = [] := by
  rfl

/--
Finite-prefix Stone/profinite readback: projecting the descended Cantor point to
depth `k` agrees with projecting the original finite-stage address.
-/
theorem cantorPrefixProjection_ofStage
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (k n : ℕ) (x : Op) :
    T.cantorPrefixProjection k (ofStage T.direct n x) =
      boundaryPrefix k (T.address n x) := by
  simp [cantorPrefixProjection, cantorLimitMap_ofStage]

/-- Finite Turing-tape observations of a finite-stage element are exactly its Cantor address prefix. -/
theorem turingWindow_readout_ofStage
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (k n : ℕ) (x : Op) :
    turingWindow k (T.turingTapeReadout (ofStage T.direct n x)) =
      boundaryPrefix k (T.address n x) := by
  simp [turingWindow, turingTapeReadout, cantorLimitMap_ofStage]

/-- Every finite-stage image reconstructs from each finite Cantor prefix and tail. -/
theorem cantorAddress_finite_reconstruction_ofStage
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual)
    (k n : ℕ) (x : Op) :
    T.cantorLimitMap (ofStage T.direct n x) =
      boundaryConsList
        (T.cantorPrefixProjection k (ofStage T.direct n x))
        (boundaryIterateTail k (T.cantorLimitMap (ofStage T.direct n x))) := by
  exact T.cantorLimitMap_finite_reconstruction (ofStage T.direct n x) k

/--
Main theorem: the infinite object of a compatible MDPAS/JM tower is the
repo-established Cantor fractal limit carrier, with unique descent from the
quotient direct limit and finite-prefix reconstruction at all depths.
-/
theorem mdpas_infinite_object_is_cantor_fractal_colimit
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual) :
    Nonempty (FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct) ∧
      ∃! Φ : FiniteMDPASJMDirectSystem.DirectLimitCarrier T.direct → (ℕ → Bool),
        (∀ n x, Φ (ofStage T.direct n x) = T.address n x) ∧
          (∀ q, Φ q = boundaryCons (boundaryHead (Φ q)) (boundaryTail (Φ q))) ∧
          (∀ q n, Φ q = boundaryConsList (boundaryPrefix n (Φ q))
            (boundaryIterateTail n (Φ q))) := by
  refine ⟨⟨default⟩, T.cantorLimitMap, ?_, ?_⟩
  · constructor
    · intro n x
      exact T.cantorLimitMap_ofStage n x
    constructor
    · intro q
      exact T.cantorLimitMap_recursive_decomposition q
    · intro q n
      exact T.cantorLimitMap_finite_reconstruction q n
  · intro Ψ hΨ
    exact T.cantorLimitMap_unique Ψ hΨ.1

/--
The entropy-production class of the MDPAS direct limit can be read at every
stage before applying the Cantor address map.
-/
theorem entropyProduction_cantor_address_compatible
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    T.cantorLimitMap
        (ofStage T.direct (n + 1)
          (entropy_production (T.direct.tower.stage (n + 1)).flow)) =
      T.cantorLimitMap
        (ofStage T.direct n
          (entropy_production (T.direct.tower.stage n).flow)) := by
  rw [directLimit_entropy_production_compatible T.direct n]

/-- Curvature classes likewise have Cantor-compatible direct-limit readout. -/
theorem curvature_cantor_address_compatible
    (T : MDPASCantorAddressSystem ι Op State LieAlgebra LieDual) (n : ℕ) :
    T.cantorLimitMap
        (ofStage T.direct (n + 1)
          (thermodynamic_curvature (T.direct.tower.stage (n + 1)).flow)) =
      T.cantorLimitMap
        (ofStage T.direct n
          (thermodynamic_curvature (T.direct.tower.stage n).flow)) := by
  rw [directLimit_thermodynamic_curvature_compatible T.direct n]

end MDPASCantorAddressSystem

end InfoGeometry.Physics.MDPASJMSouriauCantorColimit
