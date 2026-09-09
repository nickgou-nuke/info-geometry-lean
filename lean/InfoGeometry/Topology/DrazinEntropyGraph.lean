import Mathlib.Tactic
import InfoGeometry.Canonical.RegularSupportSecondLaw
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Topology.DrazinEntropyGraph

Thermodynamically admissible Drazin transition graph.

This module is downstream of `RegularSupportSecondLaw`.

The base legal arrow is deliberately weak:

* support-preserving;
* regular-corner-preserving;
* modular-covariant.

For such arrows, target entropy nonnegativity is derived from the target
Second Law.  The stronger irreversible order
`EP_source x ≤ EP_target (map x)` is packaged separately by
`DrazinEntropyMonotoneArrow`.
-/

noncomputable section

set_option linter.dupNamespace false

namespace InfoGeometry.Topology.DrazinEntropyGraph

open InfoGeometry.Canonical.RegularSupportSecondLaw

/-! ## 1. Drazin thermodynamic frames -/

/--
A Drazin thermodynamic frame over a fixed operator algebra `Op`.

It packages a Drazin regular support, a modular flow fixing that support, a
compressed regular expectation state, a regular Onsager dissipator, and a
separate defect memory readout.
-/
@[rep_depth krein]
structure DrazinThermoFrame
    (Op : Type*) [Ring Op] [Star Op] [SMul ℝ Op] where
  support : DrazinRegularSupport Op
  flow : ModularFlow Op
  fixedSupport : ModularFixedSupport flow support
  compressedState : RealExpectationState Op
  dissipator : RegularOnsagerDissipator Op
  defectReadout : DefectMemoryReadout Op support

namespace DrazinThermoFrame

variable {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]

/-- Entropy production attached to a Drazin thermodynamic frame. -/
@[rep_depth krein]
def entropyProduction
    (F : DrazinThermoFrame Op)
    (x : Op) : ℝ :=
  InfoGeometry.Canonical.RegularSupportSecondLaw.entropyProduction
    F.compressedState F.dissipator x

/-- Convert a graph frame into the canonical Second Law certificate. -/
@[rep_depth krein]
def toSecondLawCertificate
    (F : DrazinThermoFrame Op) :
    RegularSupportSecondLawCertificate Op where
  state := F.compressedState
  flow := F.flow
  support := F.support
  dissipator := F.dissipator
  support_fixed := F.fixedSupport

/-- Every regular-corner force has nonnegative entropy production. -/
@[rep_depth krein]
theorem second_law
    (F : DrazinThermoFrame Op)
    (x : Op)
    (hx : InRegularCorner F.support x) :
    0 ≤ F.entropyProduction x := by
  simpa [DrazinThermoFrame.entropyProduction] using
    certificate_second F.toSecondLawCertificate x hx

/-- Modular fixedness gives two-sided no leakage. -/
@[rep_depth krein]
theorem no_leakage
    (F : DrazinThermoFrame Op) :
    (∀ t : ℝ, leakageOperator F.flow F.support t = 0)
      ∧
    (∀ t : ℝ, rightLeakageOperator F.flow F.support t = 0) :=
  certificate_no_leakage F.toSecondLawCertificate

/-- The defect complement is modularly fixed. -/
@[rep_depth krein]
theorem defect_modular_fixed
    (F : DrazinThermoFrame Op) :
    ∀ t : ℝ, F.flow.sigma t F.support.q = F.support.q :=
  certificate_defect_modular_fixed F.toSecondLawCertificate

/-- Left leakage energy vanishes. -/
@[rep_depth krein]
theorem leakage_energy_zero
    (F : DrazinThermoFrame Op) :
    ∀ t : ℝ, leakageEnergy F.compressedState F.flow F.support t = 0 :=
  certificate_leakage_energy_zero F.toSecondLawCertificate

end DrazinThermoFrame

/-- Entropy production attached to a Drazin thermodynamic frame. -/
@[rep_depth krein]
def frameEntropyProduction
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (F : DrazinThermoFrame Op)
    (x : Op) : ℝ :=
  F.entropyProduction x

/-- Second Law readout for a Drazin thermodynamic frame. -/
@[rep_depth krein]
theorem frame_second
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (F : DrazinThermoFrame Op)
    (x : Op)
    (hx : InRegularCorner F.support x) :
    0 ≤ frameEntropyProduction F x :=
  F.second_law x hx

/--
Frame-level no leakage.

The upstream theorem derives orthogonality from `q = 1 - p` and `p * p = p`,
so no orthogonality witnesses are needed downstream.
-/
@[rep_depth krein]
theorem frame_no_leakage
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (F : DrazinThermoFrame Op) :
    (∀ t : ℝ, leakageOperator F.flow F.support t = 0)
      ∧
    (∀ t : ℝ, rightLeakageOperator F.flow F.support t = 0) :=
  no_leakage_of_modular_fixed_support
    F.flow F.support F.fixedSupport

/-! ## 2. Base legal arrows -/

/--
A base legal Drazin entropy arrow.

This weaker arrow notion preserves the regular lane and the selected modular
clock.  It is enough to derive target entropy nonnegativity, but not enough to
compare target entropy production against source entropy production.
-/
@[rep_depth krein]
structure DrazinEntropyArrow
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (F G : DrazinThermoFrame Op) where
  /-- Underlying transition map on observables. -/
  map : Op → Op
  /-- The transition preserves identity enough for the current graph layer. -/
  map_one : map 1 = 1
  /-- The transition sends the source regular support to the target support. -/
  support_preserving :
    map F.support.p = G.support.p
  /-- Regular-corner preservation. -/
  regular_preserving :
    ∀ x : Op,
      InRegularCorner F.support x →
        InRegularCorner G.support (map x)
  /-- Modular covariance. -/
  modular_covariant :
    ∀ (t : ℝ) (x : Op),
      map (F.flow.sigma t x) =
        G.flow.sigma t (map x)

namespace DrazinEntropyArrow

variable {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]

/-- Identity legal arrow on a Drazin thermodynamic frame. -/
@[rep_depth krein]
def idArrow
    (F : DrazinThermoFrame Op) :
    DrazinEntropyArrow F F where
  map := id
  map_one := rfl
  support_preserving := rfl
  regular_preserving := by
    intro x hx
    exact hx
  modular_covariant := by
    intro t x
    rfl

/-- Composition of base legal arrows. -/
@[rep_depth krein]
def compArrow
    {F G H : DrazinThermoFrame Op}
    (α : DrazinEntropyArrow F G)
    (β : DrazinEntropyArrow G H) :
    DrazinEntropyArrow F H where
  map := fun x => β.map (α.map x)
  map_one := by
    rw [α.map_one, β.map_one]
  support_preserving := by
    rw [α.support_preserving, β.support_preserving]
  regular_preserving := by
    intro x hx
    exact β.regular_preserving (α.map x) (α.regular_preserving x hx)
  modular_covariant := by
    intro t x
    rw [α.modular_covariant t x]
    rw [β.modular_covariant t (α.map x)]

/-- A legal arrow sends regular forces to regular forces. -/
@[rep_depth krein]
theorem arrow_regular_preserving
    {F G : DrazinThermoFrame Op}
    (α : DrazinEntropyArrow F G)
    (x : Op)
    (hx : InRegularCorner F.support x) :
    InRegularCorner G.support (α.map x) :=
  α.regular_preserving x hx

/-- A legal arrow is modular-covariant. -/
@[rep_depth krein]
theorem arrow_modular_covariant
    {F G : DrazinThermoFrame Op}
    (α : DrazinEntropyArrow F G)
    (t : ℝ)
    (x : Op) :
    α.map (F.flow.sigma t x) =
      G.flow.sigma t (α.map x) :=
  α.modular_covariant t x

/--
Target entropy nonnegativity derived from the target Second Law.

This proves `0 ≤ EP_B (α x)`, not the stronger comparison
`EP_A x ≤ EP_B (α x)`.
-/
@[rep_depth krein]
theorem arrow_target_entropy_nonnegative
    {F G : DrazinThermoFrame Op}
    (α : DrazinEntropyArrow F G)
    (x : Op)
    (hx : InRegularCorner F.support x) :
    0 ≤ frameEntropyProduction G (α.map x) :=
  frame_second G (α.map x) (α.regular_preserving x hx)

/-- Left identity law for arrow maps. -/
@[rep_depth krein]
theorem comp_id_left_map
    {F G : DrazinThermoFrame Op}
    (α : DrazinEntropyArrow F G)
    (x : Op) :
    (compArrow (idArrow F) α).map x = α.map x :=
  rfl

/-- Right identity law for arrow maps. -/
@[rep_depth krein]
theorem comp_id_right_map
    {F G : DrazinThermoFrame Op}
    (α : DrazinEntropyArrow F G)
    (x : Op) :
    (compArrow α (idArrow G)).map x = α.map x :=
  rfl

/-- Associativity law for arrow maps. -/
@[rep_depth krein]
theorem comp_assoc_map
    {E F G H : DrazinThermoFrame Op}
    (α : DrazinEntropyArrow E F)
    (β : DrazinEntropyArrow F G)
    (γ : DrazinEntropyArrow G H)
    (x : Op) :
    (compArrow (compArrow α β) γ).map x =
      (compArrow α (compArrow β γ)).map x :=
  rfl

end DrazinEntropyArrow

/-! ## 3. Entropy-monotone arrows -/

/--
Stronger irreversible transition packet.

This extends the base arrow with the actual entropy-order witness
`EP_source x ≤ EP_target (map x)`.
-/
@[rep_depth krein]
structure DrazinEntropyMonotoneArrow
    {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]
    (F G : DrazinThermoFrame Op) where
  base : DrazinEntropyArrow F G
  entropy_nondecreasing :
    ∀ x : Op,
      InRegularCorner F.support x →
        frameEntropyProduction F x ≤
          frameEntropyProduction G (base.map x)

namespace DrazinEntropyMonotoneArrow

variable {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]

/-- Identity monotone arrow. -/
@[rep_depth krein]
def idMonotoneArrow
    (F : DrazinThermoFrame Op) :
    DrazinEntropyMonotoneArrow F F where
  base := DrazinEntropyArrow.idArrow F
  entropy_nondecreasing := by
    intro x _hx
    exact le_rfl

/-- Composition of monotone arrows. -/
@[rep_depth krein]
def compMonotoneArrow
    {F G H : DrazinThermoFrame Op}
    (α : DrazinEntropyMonotoneArrow F G)
    (β : DrazinEntropyMonotoneArrow G H) :
    DrazinEntropyMonotoneArrow F H where
  base := DrazinEntropyArrow.compArrow α.base β.base
  entropy_nondecreasing := by
    intro x hx
    have hα :
        frameEntropyProduction F x ≤
          frameEntropyProduction G (α.base.map x) :=
      α.entropy_nondecreasing x hx
    have hαx : InRegularCorner G.support (α.base.map x) :=
      α.base.regular_preserving x hx
    have hβ :
        frameEntropyProduction G (α.base.map x) ≤
          frameEntropyProduction H (β.base.map (α.base.map x)) :=
      β.entropy_nondecreasing (α.base.map x) hαx
    exact le_trans hα hβ

/-- Readback of the supplied entropy monotonicity witness. -/
@[rep_depth krein]
theorem arrow_entropy_nondecreasing
    {F G : DrazinThermoFrame Op}
    (α : DrazinEntropyMonotoneArrow F G)
    (x : Op)
    (hx : InRegularCorner F.support x) :
    frameEntropyProduction F x ≤
      frameEntropyProduction G (α.base.map x) :=
  α.entropy_nondecreasing x hx

/-- Monotone arrows also satisfy target entropy nonnegativity. -/
@[rep_depth krein]
theorem target_entropy_nonnegative
    {F G : DrazinThermoFrame Op}
    (α : DrazinEntropyMonotoneArrow F G)
    (x : Op)
    (hx : InRegularCorner F.support x) :
    0 ≤ frameEntropyProduction G (α.base.map x) :=
  α.base.arrow_target_entropy_nonnegative x hx

end DrazinEntropyMonotoneArrow

/-! ## 4. Graph-level structures -/

/--
A Drazin entropy graph over one operator algebra.

Vertices are thermodynamic frames.  Edges realize as base legal arrows; stronger
entropy monotonicity is represented separately by `DrazinEntropyMonotoneArrow`.
-/
@[rep_depth krein]
structure DrazinEntropyGraph
    (Op : Type*) [Ring Op] [Star Op] [SMul ℝ Op] where
  Vertex : Type
  frame : Vertex → DrazinThermoFrame Op
  Edge : Vertex → Vertex → Type
  realize :
    ∀ {u v : Vertex},
      Edge u v → DrazinEntropyArrow (frame u) (frame v)

/-- A path in a Drazin entropy graph. -/
@[rep_depth krein]
inductive DrazinEntropyPath
    {Op : Type*}
    [Ring Op] [Star Op] [SMul ℝ Op]
    (G : DrazinEntropyGraph Op) :
    G.Vertex → G.Vertex → Type* where
  | nil (v : G.Vertex) :
      DrazinEntropyPath G v v
  | cons {u v w : G.Vertex}
      (e : G.Edge u v)
      (rest : DrazinEntropyPath G v w) :
      DrazinEntropyPath G u w

namespace DrazinEntropyPath

variable {Op : Type*} [Ring Op] [Star Op] [SMul ℝ Op]

/-- Realization of a graph path as a base legal transition. -/
@[rep_depth krein]
def realize
    {G : DrazinEntropyGraph Op}
    {u v : G.Vertex}
    (p : DrazinEntropyPath G u v) :
    DrazinEntropyArrow (G.frame u) (G.frame v) :=
  match p with
  | nil u => DrazinEntropyArrow.idArrow (G.frame u)
  | cons e rest =>
      DrazinEntropyArrow.compArrow (G.realize e) (realize rest)

/--
Every path sends regular source forces to target regular forces, hence target
entropy production is nonnegative.
-/
@[rep_depth krein]
theorem path_target_entropy_nonnegative
    {G : DrazinEntropyGraph Op}
    {u v : G.Vertex}
    (p : DrazinEntropyPath G u v)
    (x : Op)
    (hx : InRegularCorner (G.frame u).support x) :
    0 ≤ frameEntropyProduction (G.frame v) ((realize p).map x) :=
  (realize p).arrow_target_entropy_nonnegative x hx

end DrazinEntropyPath

/-! ## 5. Memory loops and heat paths -/

/--
A zero-entropy loop at a vertex.

This is the theorem-safe carrier for a memory loop: an admissible closed path
whose entropy production readout is unchanged on all regular forces.
-/
@[rep_depth krein]
structure ZeroEntropyLoop
    {Op : Type*}
    [Ring Op] [Star Op] [SMul ℝ Op]
    (G : DrazinEntropyGraph Op)
    (v : G.Vertex) where
  path : DrazinEntropyPath G v v
  entropy_preserved :
    ∀ (x : Op) (_hx : InRegularCorner (G.frame v).support x),
      frameEntropyProduction (G.frame v) ((DrazinEntropyPath.realize path).map x)
        =
      frameEntropyProduction (G.frame v) x

/--
A positive-entropy path.

This is the theorem-safe carrier for a heat-flow channel: an admissible path
whose entropy production strictly increases for a chosen regular force.
-/
@[rep_depth krein]
structure PositiveEntropyPath
    {Op : Type*}
    [Ring Op] [Star Op] [SMul ℝ Op]
    (G : DrazinEntropyGraph Op)
    (u v : G.Vertex) where
  path : DrazinEntropyPath G u v
  witnessForce : Op
  witnessRegular :
    InRegularCorner (G.frame u).support witnessForce
  entropy_strict :
    frameEntropyProduction (G.frame u) witnessForce
      <
    frameEntropyProduction (G.frame v) ((DrazinEntropyPath.realize path).map witnessForce)

end InfoGeometry.Topology.DrazinEntropyGraph
