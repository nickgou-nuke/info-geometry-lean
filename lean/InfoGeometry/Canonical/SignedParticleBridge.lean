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

end InfoGeometry.Canonical.SignedParticleBridge
