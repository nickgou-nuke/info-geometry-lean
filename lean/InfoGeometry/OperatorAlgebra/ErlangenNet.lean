import InfoGeometry.Canonical.WeylHomogeneousReadoutBridge
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

/-- Native dependent carrier for local algebras and their embeddings. -/
abbrev LocalObservableFrame (Alg Frame : Type*) :=
  Σ localAlg : Frame → Type*, (∀ f, localAlg f → Alg)

abbrev LocalObservableFrame.localAlg
    {Alg Frame : Type*} (F : LocalObservableFrame Alg Frame) := F.1

abbrev LocalObservableFrame.embed
    {Alg Frame : Type*} (F : LocalObservableFrame Alg Frame) :
    ∀ f, F.localAlg f → Alg := F.2

def LocalObservableFrame.mk
    {Alg Frame : Type*}
    (localAlg : Frame → Type*)
    (embed : ∀ f, localAlg f → Alg) : LocalObservableFrame Alg Frame :=
  ⟨localAlg, embed⟩

namespace LocalObservableFrame

variable {Alg Frame : Type*}
variable (F : LocalObservableFrame Alg Frame)

@[rep_depth operator]
theorem embed_apply (f : Frame) (x : F.localAlg f) :
    F.embed f x = F.embed f x := rfl

end LocalObservableFrame

/-- A frame transform is natively an action-shaped function. -/
abbrev FrameTransformCarrier (Frame Sym : Type*) := Sym → Frame → Frame

abbrev FrameTransformCarrier.act
    {Frame Sym : Type*} (G : FrameTransformCarrier Frame Sym) := G

def FrameTransformCarrier.mk
    {Frame Sym : Type*} (act : Sym → Frame → Frame) :
    FrameTransformCarrier Frame Sym := act

namespace FrameTransformCarrier

variable {Frame Sym : Type*}
variable (G : FrameTransformCarrier Frame Sym)

@[rep_depth operator]
theorem act_apply (g : Sym) (f : Frame) :
    G.act g f = G.act g f := rfl

end FrameTransformCarrier

/-! `LocalSectorAlphabet` is only an adapter around Mathlib's native `Fintype`. -/
abbrev LocalSectorAlphabet (Symbol : Type*) := Fintype Symbol

abbrev LocalSectorAlphabet.instFintype
    {Symbol : Type*} (A : LocalSectorAlphabet Symbol) : Fintype Symbol := A

def LocalSectorAlphabet.mk
    {Symbol : Type*} (instFintype : Fintype Symbol) :
    LocalSectorAlphabet Symbol := instFintype

attribute [instance] LocalSectorAlphabet.instFintype

/-- A local sector split is natively a labeling function. -/
abbrev LocalSectorSplit (Frame Symbol : Type*) := Frame → Symbol

abbrev LocalSectorSplit.label
    {Frame Symbol : Type*} (S : LocalSectorSplit Frame Symbol) := S

def LocalSectorSplit.mk
    {Frame Symbol : Type*} (label : Frame → Symbol) :
    LocalSectorSplit Frame Symbol := label

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

/-- Native triple carrier for Cartan, Weyl, and Casimir readouts. -/
abbrev CartanWeylCasimirLabel
    (CartanWeight WeylShape CasimirReadout : Type*) :=
  CartanWeight × (WeylShape × CasimirReadout)

abbrev CartanWeylCasimirLabel.cartan
    {CartanWeight WeylShape CasimirReadout : Type*}
    (L : CartanWeylCasimirLabel CartanWeight WeylShape CasimirReadout) := L.1

abbrev CartanWeylCasimirLabel.weylShape
    {CartanWeight WeylShape CasimirReadout : Type*}
    (L : CartanWeylCasimirLabel CartanWeight WeylShape CasimirReadout) := L.2.1

abbrev CartanWeylCasimirLabel.casimir
    {CartanWeight WeylShape CasimirReadout : Type*}
    (L : CartanWeylCasimirLabel CartanWeight WeylShape CasimirReadout) := L.2.2

def CartanWeylCasimirLabel.mk
    {CartanWeight WeylShape CasimirReadout : Type*}
    (cartan : CartanWeight) (weylShape : WeylShape) (casimir : CasimirReadout) :
    CartanWeylCasimirLabel CartanWeight WeylShape CasimirReadout :=
  (cartan, (weylShape, casimir))


/-- Native product carrier for the iterated observable sectorization surface. -/
abbrev IteratedObservableSectorization
    (Alg Frame Sym Symbol Label : Type*) :=
  LocalObservableFrame Alg Frame ×
    (FrameTransformCarrier Frame Sym ×
      (LocalSectorAlphabet Symbol ×
        (LocalSectorSplit Frame Symbol ×
          ((Symbol → Frame → Frame) ×
            (((n : ℕ) → Frame → FiniteSectorWord Symbol n) ×
              ((Frame → SectorBoundary Symbol) × (Frame → Label)))))))

abbrev IteratedObservableSectorization.frames
    {Alg Frame Sym Symbol Label : Type*}
    (N : IteratedObservableSectorization Alg Frame Sym Symbol Label) := N.1

abbrev IteratedObservableSectorization.transforms
    {Alg Frame Sym Symbol Label : Type*}
    (N : IteratedObservableSectorization Alg Frame Sym Symbol Label) := N.2.1

abbrev IteratedObservableSectorization.alphabet
    {Alg Frame Sym Symbol Label : Type*}
    (N : IteratedObservableSectorization Alg Frame Sym Symbol Label) := N.2.2.1

abbrev IteratedObservableSectorization.split
    {Alg Frame Sym Symbol Label : Type*}
    (N : IteratedObservableSectorization Alg Frame Sym Symbol Label) := N.2.2.2.1

abbrev IteratedObservableSectorization.transition
    {Alg Frame Sym Symbol Label : Type*}
    (N : IteratedObservableSectorization Alg Frame Sym Symbol Label) := N.2.2.2.2.1

abbrev IteratedObservableSectorization.finiteCode
    {Alg Frame Sym Symbol Label : Type*}
    (N : IteratedObservableSectorization Alg Frame Sym Symbol Label) := N.2.2.2.2.2.1

abbrev IteratedObservableSectorization.boundaryCode
    {Alg Frame Sym Symbol Label : Type*}
    (N : IteratedObservableSectorization Alg Frame Sym Symbol Label) := N.2.2.2.2.2.2.1

abbrev IteratedObservableSectorization.sectorLabel
    {Alg Frame Sym Symbol Label : Type*}
    (N : IteratedObservableSectorization Alg Frame Sym Symbol Label) := N.2.2.2.2.2.2.2

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

/-- Native product of a symbolic label and the existing Weyl readout owner. -/
abbrev WeylRefinedSectorLabel (Obj Label : Type*) :=
  (Obj → Label) × WeylHomogeneousOperatorReadout Obj

abbrev WeylRefinedSectorLabel.label
    {Obj Label : Type*} (W : WeylRefinedSectorLabel Obj Label) := W.1

abbrev WeylRefinedSectorLabel.homogeneousReadout
    {Obj Label : Type*} (W : WeylRefinedSectorLabel Obj Label) := W.2

def WeylRefinedSectorLabel.mk
    {Obj Label : Type*} (label : Obj → Label)
    (homogeneousReadout : WeylHomogeneousOperatorReadout Obj) :
    WeylRefinedSectorLabel Obj Label := (label, homogeneousReadout)

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
