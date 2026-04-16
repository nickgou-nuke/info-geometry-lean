import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.CertifiedInverseKernel
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SignedParticleBridge

Signed-particle language is treated here as a computational shadow of the
Doubled/Krein projector lane, not as a primitive owner ontology.

This file is a translator/Rosetta surface. It records a minimal correspondence
between signed phase-space language and repo-native projector grammar.
-/

namespace InfoGeometry.Canonical.SignedParticleBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinKreinCompatibility
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Op" => DoubledSpace E →L[ℝ] DoubledSpace E

/--
Wigner phase-space carrier in repo language:
the doubled real Krein space.
-/
@[rep_depth operator]
abbrev WignerCarrier := DoubledSpace E

/--
Symmetrically split phase-space shell on the doubled carrier.

This is a translator shell, not an owner-side symmetric-space construction.
-/
@[rep_depth operator]
structure SplitSymmetricPhaseSpace where
  plusProjector : Op
  minusProjector : Op
  splitCompleteness : plusProjector + minusProjector = (1 : Op)

/--
Self-dual cone shadow on the doubled carrier.

`selfDualWitness` is intentionally abstract at this translator layer.
-/
@[rep_depth operator]
structure SelfDualConeShadow where
  carrier : Set (WignerCarrier (E := E))
  selfDualWitness : Prop

/-- Kramers-pair shadow carried on the doubled real phase space. -/
@[rep_depth operator]
structure KramersPairShadow where
  state : WignerCarrier (E := E)
  partner : WignerCarrier (E := E)

/-- Minimal signed contribution object: positive or negative transport weight. -/
@[rep_depth operator]
structure SignedContribution where
  sign : Bool

/-- Positive lane predicate. -/
@[rep_depth operator]
def SignedContribution.isPositive (s : SignedContribution) : Prop :=
  s.sign = true

/-- Negative lane predicate. -/
@[rep_depth operator]
def SignedContribution.isNegative (s : SignedContribution) : Prop :=
  s.sign = false

/--
A signed-particle shadow packet over a doubled carrier operator package.

This is only a translator surface: it does not define owner dynamics.
-/
@[rep_depth operator]
structure SignedParticleShadow (T TD : Op) (k : ℕ) where
  compat : KreinGradedDrazinCompatibility (E := E) T TD k
  positiveSector : Op
  negativeSector : Op

/-- Cancellation/annihilation shadow: opposite-sign overlap contributes zero. -/
@[rep_depth operator]
def annihilationShadow {T TD : Op} {k : ℕ}
    (S : SignedParticleShadow (E := E) T TD k) : Prop :=
  S.positiveSector * S.negativeSector = 0

/--
Regular classical-shadow transport lives on the Drazin regular projector.
-/
@[rep_depth operator]
def classicalShadowOnRegularCore {T TD : Op} {k : ℕ}
    (S : SignedParticleShadow (E := E) T TD k) : Prop :=
  Preg T TD * S.positiveSector = S.positiveSector

/--
Nonclassical correction is measured by spectral/metric mismatch.

This is only the translator statement; the owner is `MoorePenrose.chiralAnomaly`.
-/
@[rep_depth operator]
def nonclassicalShadow
    {R : Type*} [Ring R] [StarRing R] (a a_d a_mp : R) : R :=
  chiralAnomaly a a_d a_mp

/--
Wigner-representation shadow packet over the projector lane.

This bundles the split shell, cone shell, Kramers shell, and the signed
projector shadow into one translator surface.
-/
@[rep_depth operator]
structure WignerRepresentationShadow (T TD : Op) (k : ℕ) where
  split : SplitSymmetricPhaseSpace (E := E)
  cone : SelfDualConeShadow (E := E)
  kramers : KramersPairShadow (E := E)
  signed : SignedParticleShadow (E := E) T TD k

/-- Minimal Wigner algebra shadow on doubled real operators. -/
@[rep_depth operator]
abbrev WignerAlgebra := Op

/-- Wigner commutator-shadow bracket. -/
@[rep_depth operator]
noncomputable def wignerBracket (A B : WignerAlgebra (E := E)) : WignerAlgebra (E := E) :=
  A * B - B * A

/--
Translator-level nonclassical readout:
Wigner bracket plus anomaly lane correction.
-/
@[rep_depth operator]
noncomputable def wignerNonclassicalReadout
    (A B : WignerAlgebra (E := E))
    (a a_d a_mp : WignerAlgebra (E := E)) : WignerAlgebra (E := E) :=
  wignerBracket (E := E) A B + nonclassicalShadow a a_d a_mp

/-! ## Task bridge: packet negativity ↔ anomaly -/

/--
Packet negativity readout (nontrivial lane):
spectral-vs-metric routing residual on the positive sector of a signed shadow.
-/
@[rep_depth operator]
noncomputable def packetNegativity
    (CIK : CertifiedInverseKernel (DoubledSpace E))
    {T TD : Op} {k : ℕ}
    (S : SignedParticleShadow (E := E) T TD k) : ℝ :=
  ‖(CIK.spectralProjector * S.positiveSector * CIK.spectralProjector)
      - (CIK.metricProjector * S.positiveSector * CIK.metricProjector)‖

/--
Mismatch closure implies vanishing packet negativity.
-/
@[rep_depth operator]
theorem packetNegativity_eq_zero_of_projectorMismatch_eq_zero
    (CIK : CertifiedInverseKernel (DoubledSpace E))
    {T TD : Op} {k : ℕ}
    (hΔ : CIK.projectorMismatch = 0)
    (S : SignedParticleShadow (E := E) T TD k) :
    packetNegativity (E := E) CIK S = 0 := by
  unfold packetNegativity
  have hProj : CIK.spectralProjector = CIK.metricProjector :=
    (CIK.projectorMismatch_eq_zero_iff).1 hΔ
  simp [hProj]

/--
Task assumptions for proving a nontrivial packet-level equivalence
`packetNegativity = 0 ↔ chiralAnomaly = 0`.
-/
@[rep_depth operator]
structure PacketNegativityTaskAssumptions
    (CIK : CertifiedInverseKernel (DoubledSpace E))
    (T TD : Op) (k : ℕ) where
  anomaly_zero_implies_projectorMismatch_zero :
    CIK.chiralAnomaly = 0 → CIK.projectorMismatch = 0
  packetNegativity_zero_implies_anomaly_zero :
    ∀ S : SignedParticleShadow (E := E) T TD k,
      packetNegativity (E := E) CIK S = 0 → CIK.chiralAnomaly = 0

/--
Nontrivial task theorem: under task assumptions, packet negativity and anomaly
vanishing are equivalent.
-/
@[rep_depth operator]
theorem packetNegativity_zero_iff_anomaly_zero_of_taskAssumptions
    (CIK : CertifiedInverseKernel (DoubledSpace E))
    {T TD : Op} {k : ℕ}
    (A : PacketNegativityTaskAssumptions (E := E) CIK T TD k)
    (S : SignedParticleShadow (E := E) T TD k) :
    packetNegativity (E := E) CIK S = 0 ↔ CIK.chiralAnomaly = 0 := by
  constructor
  · intro hNeg
    exact A.packetNegativity_zero_implies_anomaly_zero S hNeg
  · intro hχ
    have hΔ : CIK.projectorMismatch = 0 := A.anomaly_zero_implies_projectorMismatch_zero hχ
    exact packetNegativity_eq_zero_of_projectorMismatch_eq_zero (E := E) (CIK := CIK) (hΔ := hΔ) S

/--
Bridge package using the nontrivial packet negativity as the negativity
functional, discharged by task assumptions.
-/
@[rep_depth operator]
structure NegativityAnomalyBridge
    (CIK : CertifiedInverseKernel (DoubledSpace E))
    (T TD : Op) (k : ℕ) where
  negativity : SignedParticleShadow (E := E) T TD k → ℝ
  negativity_zero_iff_anomaly_zero :
    ∀ S : SignedParticleShadow (E := E) T TD k,
      negativity S = 0 ↔ CIK.chiralAnomaly = 0

/--
Canonical constructor from task assumptions for the nontrivial bridge.
-/
@[rep_depth operator]
noncomputable def packetNegativityAnomalyBridgeOfTaskAssumptions
    (CIK : CertifiedInverseKernel (DoubledSpace E))
    {T TD : Op} {k : ℕ}
    (A : PacketNegativityTaskAssumptions (E := E) CIK T TD k) :
    NegativityAnomalyBridge (E := E) CIK T TD k where
  negativity := packetNegativity (E := E) CIK
  negativity_zero_iff_anomaly_zero := by
    intro S
    exact packetNegativity_zero_iff_anomaly_zero_of_taskAssumptions
      (E := E) (CIK := CIK) A S

end InfoGeometry.Canonical.SignedParticleBridge
