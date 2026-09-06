import InfoGeometry.Canonical.PhotonicParabolicChannel
import InfoGeometry.Canonical.GeneralizedOperatorChiral

/-!
# InfoGeometry.Canonical.PhotonicScatteringParabolicBridge

Scattering-side bridge for parabolic contraction:
if `Ω² = 0`, the two chiral transmission lanes (`S₊`, `S₋`) collapse to one
parabolic transport class.
-/

namespace InfoGeometry.Canonical.PhotonicScatteringParabolicBridge

open GeneralizedOperatorChiral
open GeneralizedOperator
open PhotonicParabolicChannel

abbrev ParOp := GeneralizedOperator 0

/-- Minimal typed readout for a two-channel slab scattering model. -/
structure ScatteringPair where
  Splus : ChiralChannel
  Sminus : ChiralChannel
deriving Repr, DecidableEq

/-- Under a fixed `Ω`, both scattering lanes are read from the same local classifier. -/
noncomputable def scatteringOfOmega (Ω : ParOp) : ScatteringPair :=
  { Splus := channelOfOmega Ω
    Sminus := channelOfOmega Ω }

/-- Transport class quotient: either split chiral or collapsed parabolic. -/
inductive TransportClass
  | Split
  | Parabolic
deriving Repr, DecidableEq

/-- Classify scattering pair into transport class. -/
def transportClass (S : ScatteringPair) : TransportClass :=
  if _h : S.Splus = ChiralChannel.Parabolic ∧ S.Sminus = ChiralChannel.Parabolic
  then TransportClass.Parabolic
  else TransportClass.Split

/-- Under `Ω² = 0`, both scattering lanes are parabolic. -/
theorem scattering_channels_collapse
    (Ω : ParOp) (h_nilpotent : mul Ω Ω = zero) :
    (scatteringOfOmega Ω).Splus = ChiralChannel.Parabolic ∧
    (scatteringOfOmega Ω).Sminus = ChiralChannel.Parabolic := by
  constructor <;>
    simpa [scatteringOfOmega] using chiral_collapse_to_parabolic Ω h_nilpotent

/-- Scattering-side bridge theorem: `S₊/S₋` collapse to one parabolic class. -/
theorem scattering_transportClass_parabolic_of_nilpotent
    (Ω : ParOp) (h_nilpotent : mul Ω Ω = zero) :
    transportClass (scatteringOfOmega Ω) = TransportClass.Parabolic := by
  unfold transportClass
  simp [scattering_channels_collapse Ω h_nilpotent]

/-- The concrete scattering classifier detects nilpotence exactly. -/
theorem scattering_transportClass_parabolic_iff_nilpotent
    (Ω : ParOp) :
    transportClass (scatteringOfOmega Ω) = TransportClass.Parabolic ↔
      mul Ω Ω = zero := by
  constructor
  · intro hclass
    classical
    by_cases hchannels :
        (scatteringOfOmega Ω).Splus = ChiralChannel.Parabolic ∧
          (scatteringOfOmega Ω).Sminus = ChiralChannel.Parabolic
    · have hplus : channelOfOmega Ω = ChiralChannel.Parabolic := by
        simpa [scatteringOfOmega] using hchannels.1
      exact PhotonicParabolicChannel.nilpotent_of_chiral_collapse Ω hplus
    · simp [transportClass, hchannels] at hclass
  · intro h_nilpotent
    exact scattering_transportClass_parabolic_of_nilpotent Ω h_nilpotent

/--
Witness-based packet (owner-side): no global collapse claim without hypotheses.
`collapseWitness` explicitly certifies that both channels are parabolic.
-/
structure ScatteringParabolicPacket where
  Splus : ChiralChannel
  Sminus : ChiralChannel
  collapseWitness :
    Splus = ChiralChannel.Parabolic ∧ Sminus = ChiralChannel.Parabolic

/-- Induced common transport class from the explicit property packet. -/
def ScatteringParabolicPacket.commonTransportClass
    (_P : ScatteringParabolicPacket) : TransportClass :=
  TransportClass.Parabolic

/-- Both channels map to the same parabolic class. -/
theorem ScatteringParabolicPacket.both_channels_map_to_common_class
    (P : ScatteringParabolicPacket) :
    (P.Splus = ChiralChannel.Parabolic ∧ P.Sminus = ChiralChannel.Parabolic) ∧
      P.commonTransportClass = TransportClass.Parabolic := by
  constructor
  · exact P.collapseWitness
  · rfl

/-- Constructor from the local `Ω² = 0` property into a packet property. -/
noncomputable def mk_packet_of_nilpotent (Ω : ParOp) (h_nilpotent : mul Ω Ω = zero) :
    ScatteringParabolicPacket := by
  refine
    { Splus := (scatteringOfOmega Ω).Splus
      Sminus := (scatteringOfOmega Ω).Sminus
      collapseWitness := ?_ }
  exact scattering_channels_collapse Ω h_nilpotent

/--
Finite-slab interface packet:
entry/exit channel readouts are explicit, and the collapse property is local to
this packet (no global claim).
-/
structure FiniteSlabParabolicPacket where
  entryPlus : ChiralChannel
  entryMinus : ChiralChannel
  exitPlus : ChiralChannel
  exitMinus : ChiralChannel
  entryCollapseWitness :
    entryPlus = ChiralChannel.Parabolic ∧ entryMinus = ChiralChannel.Parabolic
  exitCollapseWitness :
    exitPlus = ChiralChannel.Parabolic ∧ exitMinus = ChiralChannel.Parabolic

/-- Induced slab transport class from the explicit interface witnesses. -/
def FiniteSlabParabolicPacket.transportClass
    (_P : FiniteSlabParabolicPacket) : TransportClass :=
  TransportClass.Parabolic

/-- Slab-level theorem: both entry and exit channels map to one parabolic class. -/
theorem FiniteSlabParabolicPacket.channels_map_to_parabolic_class
    (P : FiniteSlabParabolicPacket) :
    (P.entryPlus = ChiralChannel.Parabolic ∧ P.entryMinus = ChiralChannel.Parabolic) ∧
    (P.exitPlus = ChiralChannel.Parabolic ∧ P.exitMinus = ChiralChannel.Parabolic) ∧
    P.transportClass = TransportClass.Parabolic := by
  constructor
  · exact P.entryCollapseWitness
  constructor
  · exact P.exitCollapseWitness
  · rfl

/-- Build a finite-slab packet from a single local nilpotent property `Ω² = 0`. -/
noncomputable def mk_finiteSlab_packet_of_nilpotent
    (Ω : ParOp) (h_nilpotent : mul Ω Ω = zero) : FiniteSlabParabolicPacket := by
  let S := scatteringOfOmega Ω
  refine
    { entryPlus := S.Splus
      entryMinus := S.Sminus
      exitPlus := S.Splus
      exitMinus := S.Sminus
      entryCollapseWitness := ?_
      exitCollapseWitness := ?_ }
  · exact scattering_channels_collapse Ω h_nilpotent
  · exact scattering_channels_collapse Ω h_nilpotent

/--
Finite-slab interface packet with explicit boundary maps and a collapse property.
The property asserts that entry/exit preserve the chiral lane labels used in the
scattering pair.
-/
structure FiniteSlabParabolicInterfacePacket where
  slabScattering : ScatteringPair
  entry : ChiralChannel → ChiralChannel
  exit : ChiralChannel → ChiralChannel
  boundaryCompatibility :
    entry slabScattering.Splus = slabScattering.Splus ∧
    exit slabScattering.Sminus = slabScattering.Sminus
  collapseWitness :
    slabScattering.Splus = ChiralChannel.Parabolic ∧
    slabScattering.Sminus = ChiralChannel.Parabolic

/--
Slab-level `S₊/S₋` transport classes coincide in the parabolic regime.
-/
theorem FiniteSlabParabolicInterfacePacket.slab_transport_classes_coincide
    (P : FiniteSlabParabolicInterfacePacket) :
    P.slabScattering.Splus = ChiralChannel.Parabolic ∧
    P.slabScattering.Sminus = ChiralChannel.Parabolic := by
  exact P.collapseWitness

/--
Corollary: the slab carries a single parabolic transport class.
-/
theorem FiniteSlabParabolicInterfacePacket.single_parabolic_slab_transport_class
    (P : FiniteSlabParabolicInterfacePacket) :
    transportClass P.slabScattering = TransportClass.Parabolic := by
  unfold transportClass
  simp [P.collapseWitness]

/--
Real owner-side implication (no property field):
if slab boundary maps preserve the local scattering labels and both boundary
readouts are parabolic, then the underlying carrier is nilpotent (`Ω² = 0`).
-/
theorem slab_boundary_parabolic_implies_nilpotent
    (Ω : ParOp)
    (entry exit : ChiralChannel → ChiralChannel)
    (hCompat :
      entry (scatteringOfOmega Ω).Splus = (scatteringOfOmega Ω).Splus ∧
      exit (scatteringOfOmega Ω).Sminus = (scatteringOfOmega Ω).Sminus)
    (hBoundary :
      entry (scatteringOfOmega Ω).Splus = ChiralChannel.Parabolic ∧
      exit (scatteringOfOmega Ω).Sminus = ChiralChannel.Parabolic) :
    mul Ω Ω = zero := by
  have hPlus : (scatteringOfOmega Ω).Splus = ChiralChannel.Parabolic := by
    calc
      (scatteringOfOmega Ω).Splus
          = entry (scatteringOfOmega Ω).Splus := by simpa [hCompat.1] using (hCompat.1).symm
      _ = ChiralChannel.Parabolic := hBoundary.1
  have hChan : channelOfOmega Ω = ChiralChannel.Parabolic := by
    simpa [scatteringOfOmega] using hPlus
  exact PhotonicParabolicChannel.nilpotent_of_chiral_collapse Ω hChan

/--
Stronger owner-side consequence:
if one compatible slab boundary readout is parabolic, then the carrier is
nilpotent and both scattering lanes collapse to parabolic.
-/
theorem slab_entry_parabolic_implies_full_collapse
    (Ω : ParOp)
    (entry exit : ChiralChannel → ChiralChannel)
    (hCompat :
      entry (scatteringOfOmega Ω).Splus = (scatteringOfOmega Ω).Splus ∧
      exit (scatteringOfOmega Ω).Sminus = (scatteringOfOmega Ω).Sminus)
    (hEntryParabolic : entry (scatteringOfOmega Ω).Splus = ChiralChannel.Parabolic) :
    mul Ω Ω = zero ∧
    (scatteringOfOmega Ω).Splus = ChiralChannel.Parabolic ∧
    (scatteringOfOmega Ω).Sminus = ChiralChannel.Parabolic := by
  have hPlus : (scatteringOfOmega Ω).Splus = ChiralChannel.Parabolic := by
    calc
      (scatteringOfOmega Ω).Splus
          = entry (scatteringOfOmega Ω).Splus := by simpa [hCompat.1] using (hCompat.1).symm
      _ = ChiralChannel.Parabolic := hEntryParabolic
  have hChan : channelOfOmega Ω = ChiralChannel.Parabolic := by
    simpa [scatteringOfOmega] using hPlus
  have hNil : mul Ω Ω = zero :=
    PhotonicParabolicChannel.nilpotent_of_chiral_collapse Ω hChan
  refine ⟨hNil, ?_, ?_⟩
  · exact hPlus
  · have hMinus : (scatteringOfOmega Ω).Sminus = ChiralChannel.Parabolic := by
      simpa [scatteringOfOmega] using
        PhotonicParabolicChannel.chiral_collapse_to_parabolic Ω hNil
    exact hMinus

end InfoGeometry.Canonical.PhotonicScatteringParabolicBridge
