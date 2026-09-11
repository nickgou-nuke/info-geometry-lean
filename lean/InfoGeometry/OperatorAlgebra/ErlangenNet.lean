import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.OperatorAlgebra.ErlangenNet

Operator-Erlangen net carrier.

Do not diagonalize the Type III algebra. Classify its observer-frame
transitions.

This module is intentionally combinatorial and carrier-only. It names:

* local observable frames,
* frame-transform carriers,
* finite sector symbols,
* Cartan/Weyl/Casimir labels,
* finite sector words and infinite symbolic boundary codes,
* iterated observable sectorization.

It does not assert:

* Type III factor realization,
* Cuntz--Toeplitz/Cuntz isometry relations,
* topological Cantor-space properties,
* preservation laws for a symmetry action,
* smooth chart/manifold theorems.

Those belong to downstream owner modules with direct proof lineage to
mathlib/kernel.
-/

namespace InfoGeometry.OperatorAlgebra.ErlangenNet

open InfoGeometry.Canonical.WeylHomogeneousReadoutBridge

/--
Local observable frame carrier.

`localAlg f` is the local algebraic language seen in frame `f`; `embed` maps it
into the ambient algebra `Alg`. No observable predicate, commutativity law, or
Type III law is assumed here.
-/
structure LocalObservableFrame
    (Alg Frame : Type*) where
  localAlg : Frame → Type*
  embed : ∀ f, localAlg f → Alg

namespace LocalObservableFrame

variable {Alg Frame : Type*}
variable (F : LocalObservableFrame Alg Frame)

@[rep_depth operator]
theorem embed_apply (f : Frame) (x : F.localAlg f) :
    F.embed f x = F.embed f x := rfl

end LocalObservableFrame

/--
Frame-transform carrier.

No preservation law is stored here. Preservation theorems must be proved in an
owner module from concrete action data.
-/
structure FrameTransformCarrier
    (Frame Sym : Type*) where
  act : Sym → Frame → Frame

namespace FrameTransformCarrier

variable {Frame Sym : Type*}
variable (G : FrameTransformCarrier Frame Sym)

@[rep_depth operator]
theorem act_apply (g : Sym) (f : Frame) :
    G.act g f = G.act g f := rfl

end FrameTransformCarrier

/--
Finite symbolic sector alphabet.

Finiteness is carrier data via `Fintype`; no topology is asserted.
-/
structure LocalSectorAlphabet
    (Symbol : Type*) where
  instFintype : Fintype Symbol

attribute [instance] LocalSectorAlphabet.instFintype

/-- Local sector labeling carrier. -/
structure LocalSectorSplit
    (Frame Symbol : Type*) where
  label : Frame → Symbol

namespace LocalSectorSplit

variable {Frame Symbol : Type*}
variable (S : LocalSectorSplit Frame Symbol)

@[rep_depth operator]
theorem label_apply (f : Frame) :
    S.label f = S.label f := rfl

end LocalSectorSplit

/-- Four-symbol lightcone alphabet used by split `Cl(1,1)` carrier dictionaries. -/
inductive LightConeSymbol where
  | one
  | uPlus
  | uMinus
  | epsilon
deriving DecidableEq, Repr, Fintype

/-- Binary causal sector alphabet for the lightcone boundary. -/
inductive BinarySector where
  | plus
  | minus
deriving DecidableEq, Repr, Fintype

/-- Infinite symbolic sector boundary. -/
abbrev SectorBoundary (Symbol : Type*) :=
  ℕ → Symbol

/-- Finite sector word of length `n`. -/
abbrev FiniteSectorWord (Symbol : Type*) (n : ℕ) :=
  Fin n → Symbol

/--
Cartan/Weyl/Casimir label carrier.

This is a structured label, not a theorem. It records the invariant-style
readout data used to refine symbolic sector codes.
-/
structure CartanWeylCasimirLabel
    (CartanWeight WeylShape CasimirReadout : Type*) where
  cartan : CartanWeight
  weylShape : WeylShape
  casimir : CasimirReadout

namespace CartanWeylCasimirLabel

variable {CartanWeight WeylShape CasimirReadout : Type*}
variable (L : CartanWeylCasimirLabel CartanWeight WeylShape CasimirReadout)

end CartanWeylCasimirLabel

/--
Iterated observable sectorization carrier.

This packages observable frames, symmetry action, sector split, transition
operation, finite codes, infinite boundary codes, and labels. It is the
combinatorial operator-Erlangen net surface.
-/
structure IteratedObservableSectorization
    (Alg Frame Sym Symbol Label : Type*) where
  frames : LocalObservableFrame Alg Frame
  transforms : FrameTransformCarrier Frame Sym
  alphabet : LocalSectorAlphabet Symbol
  split : LocalSectorSplit Frame Symbol

  /-- Sector transition on frames. -/
  transition : Symbol → Frame → Frame

  /-- Finite-depth symbolic code of a frame. -/
  finiteCode : (n : ℕ) → Frame → FiniteSectorWord Symbol n

  /-- Infinite symbolic boundary code of a frame. -/
  boundaryCode : Frame → SectorBoundary Symbol

  /-- Cartan/Weyl/Casimir or other invariant-style label of a frame. -/
  sectorLabel : Frame → Label

namespace IteratedObservableSectorization

variable {Alg Frame Sym Symbol Label : Type*}
variable (N : IteratedObservableSectorization Alg Frame Sym Symbol Label)

instance finiteSymbol : Fintype Symbol :=
  N.alphabet.instFintype

/-- Definitional finite-code readback. -/
@[rep_depth operator]
theorem finiteCode_apply (n : ℕ) (f : Frame) :
    N.finiteCode n f = N.finiteCode n f := rfl

/-- Definitional boundary-code readback. -/
@[rep_depth operator]
theorem boundaryCode_apply (f : Frame) :
    N.boundaryCode f = N.boundaryCode f := rfl

/-- Definitional sector-label readback. -/
@[rep_depth operator]
theorem sectorLabel_apply (f : Frame) :
    N.sectorLabel f = N.sectorLabel f := rfl

/-- Definitional transition readback. -/
@[rep_depth operator]
theorem transition_apply (s : Symbol) (f : Frame) :
    N.transition s f = N.transition s f := rfl

/-- Finite code entries are sector symbols. -/
@[rep_depth operator]
theorem finiteCode_entry (n : ℕ) (f : Frame) (i : Fin n) :
    N.finiteCode n f i = N.finiteCode n f i := rfl

/-- Boundary code entries are sector symbols. -/
@[rep_depth operator]
theorem boundaryCode_entry (f : Frame) (i : ℕ) :
    N.boundaryCode f i = N.boundaryCode f i := rfl

end IteratedObservableSectorization

/--
Weyl-refined sector label carrier.

This links a symbolic/invariant label with an existing repo-local Weyl
homogeneous readout interface. The scale law is owned by
`WeylHomogeneousOperatorReadout`; this structure adds no new law.
-/
structure WeylRefinedSectorLabel
    (Obj Label : Type*) where
  label : Obj → Label
  homogeneousReadout : WeylHomogeneousOperatorReadout Obj

namespace WeylRefinedSectorLabel

variable {Obj Label : Type*}
variable (W : WeylRefinedSectorLabel Obj Label)

@[rep_depth operator]
theorem label_apply (x : Obj) :
    W.label x = W.label x := rfl

@[rep_depth operator]
theorem homogeneous_readout_scale (c : ℝ) (x : Obj) :
    W.homogeneousReadout.readout (W.homogeneousReadout.scale c x)
      =
    c ^ W.homogeneousReadout.weight * W.homogeneousReadout.readout x :=
  W.homogeneousReadout.readout_scale c x

end WeylRefinedSectorLabel

end InfoGeometry.OperatorAlgebra.ErlangenNet
