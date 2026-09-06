import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.SignedParticleBridge

Signed-particle language is treated here as a computational shadow of the
Doubled/Krein projector lane, not as a primitive owner ontology.

Rosetta/translator surface between signed phase-space particle language and the
repo-native doubled/Krein projector language.

This file is not an owner of modular or Wigner ontology.
It only records a controlled correspondence surface.
-/

namespace InfoGeometry.Canonical.SignedParticleBridge

open InfoGeometry.Canonical
open InfoGeometry.Canonical.DrazinKreinCompatibility
open InfoGeometry.Canonical.MoorePenrose
open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Op" => DoubledSpace E →L[ℝ] DoubledSpace E

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
This is only the translator statement; the owner is `chiralAnomaly`.
-/
@[rep_depth operator]
def nonclassicalShadow
    {R : Type*} [Ring R] [StarRing R] (a a_d a_mp : R) : R :=
  chiralAnomaly a a_d a_mp

end InfoGeometry.Canonical.SignedParticleBridge
