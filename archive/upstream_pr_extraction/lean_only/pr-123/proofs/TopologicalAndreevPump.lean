import proofs.StimulatedScatteringAmplituhedron
import InfoGeometry.External.Auto.BuresInformationGeodesicFlow
import proofs.OpticalAndreevSpinor
import proofs.UHFInductiveColimit
import proofs.ChiralConeAlgebraFinality

/-!
# Topological Andreev pump

Finite Lean interface for the nonlinear topological-superconductor reading of
the vacuum amplifier:

* the self-concordant/log-det barrier is represented as a finite interface;
* Andreev reflection maps a parafermion lane to its modular-`J` conjugate
  hole and injects a Majorana pair;
* the diagonal UHF/Cantor colimit supplies the finite cylinder compatibility;
* stimulated gain, Bures/modular zero-time flow, Dikin/Onsager bookkeeping,
  and `p6m`/`O(5,5)` counts remain connected;
* actual superconductivity, BEC condensation, Standard-Model phase locking,
  lossless supercurrents, and continuum nonlinear optics are kept as named
  finite-model interfaces.
-/

noncomputable section

namespace TopologicalAndreevPump

/-- Four local parafermion lanes: one singlet plus three color lanes. -/
inductive ParafermionLane where
  | singlet
  | red
  | green
  | blue
  deriving DecidableEq, Repr

/-- All finite parafermion lanes used by the Andreev pump toy. -/
def parafermionLanes : List ParafermionLane :=
  [.singlet, .red, .green, .blue]

@[simp] theorem parafermion_lane_count : parafermionLanes.length = 4 := rfl

/-- Modular `J`/hole conjugation on the finite color lanes. -/
def modularJLane : ParafermionLane → ParafermionLane
  | .singlet => .singlet
  | .red => .green
  | .green => .red
  | .blue => .blue

@[simp] theorem modularJLane_involutive (ψ : ParafermionLane) :
    modularJLane (modularJLane ψ) = ψ := by
  cases ψ <;> rfl

/-- The finite log-det/self-concordant barrier interface. -/
inductive SelfConcordantBarrier where
  | logDetQ
  deriving DecidableEq, Repr

/-- Majorana pair injected into the colimit by an Andreev hit. -/
structure MajoranaPair where
  electron : ParafermionLane
  hole : ParafermionLane
  injected : Bool
  deriving Repr

/-- The canonical Majorana pair attached to a parafermion lane. -/
def majoranaPair (ψ : ParafermionLane) : MajoranaPair :=
  { electron := ψ, hole := modularJLane ψ, injected := true }

@[simp] theorem majorana_pair_hole (ψ : ParafermionLane) :
    (majoranaPair ψ).hole = modularJLane ψ := rfl

@[simp] theorem majorana_pair_injected (ψ : ParafermionLane) :
    (majoranaPair ψ).injected = true := rfl

/-- Finite Andreev reflection record: reflected hole plus injected pair. -/
structure AndreevReflection where
  reflectedHole : ParafermionLane
  pair : MajoranaPair
  barrier : SelfConcordantBarrier
  topological : Bool
  deriving Repr

/-- Topological Andreev reflection at the log-det barrier. -/
def andreevReflect (ψ : ParafermionLane)
    (B : SelfConcordantBarrier) : AndreevReflection :=
  { reflectedHole := modularJLane ψ,
    pair := majoranaPair ψ,
    barrier := B,
    topological := true }

@[simp] theorem andreev_reflect_hole (ψ : ParafermionLane)
    (B : SelfConcordantBarrier) :
    (andreevReflect ψ B).reflectedHole = modularJLane ψ := rfl

@[simp] theorem andreev_reflect_pair (ψ : ParafermionLane)
    (B : SelfConcordantBarrier) :
    (andreevReflect ψ B).pair = majoranaPair ψ := rfl

@[simp] theorem andreev_reflect_topological (ψ : ParafermionLane)
    (B : SelfConcordantBarrier) :
    (andreevReflect ψ B).topological = true := rfl

/-- Phase labels for the phase-locked condensate toy. -/
inductive GenerationPhase where
  | p2
  | p3
  | p5
  deriving DecidableEq, Repr

/-- Three generation phases in the finite phase-locking toy. -/
def generationPhases : List GenerationPhase := [.p2, .p3, .p5]

@[simp] theorem generation_phase_count : generationPhases.length = 3 := rfl

/-- A phase-locked mode in the finite BEC layer. -/
def phaseLocked (_φ : GenerationPhase) : Bool := true

@[simp] theorem all_generation_phases_locked :
    phaseLocked GenerationPhase.p2 = true ∧
    phaseLocked GenerationPhase.p3 = true ∧
    phaseLocked GenerationPhase.p5 = true := by
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

/-- Toy gain-minus-loss margin: Andreev stimulated gain minus Onsager loss. -/
def gainMinusLoss (gain loss : ℝ) : ℝ := gain - loss

@[simp] theorem gain_overcomes_loss_iff_positive_margin (gain loss : ℝ) :
    0 < gainMinusLoss gain loss ↔ loss < gain := by
  constructor
  · intro h
    dsimp [gainMinusLoss] at h
    linarith
  · intro h
    dsimp [gainMinusLoss]
    linarith



end TopologicalAndreevPump

end noncomputable section
