import InfoGeometry.Canonical.FiniteJaynesFormalism

/-!
# InfoGeometry.Canonical.FiniteJaynesInductiveFormalism

Finite Jaynes formalism under explicit stage-to-stage transport.

This module adds the theorem-safe induction/compatibility layer for finite
Jaynes data.  The key point is deliberately modest:

* if a finite profile map preserves subtraction;
* and sends the reference profile and observation profile at one stage to the
  next stage;
* then it sends the additive centered score to the next additive centered
  score.

With an additional explicit mass-preservation property, equal-mass Jaynes
pairs transport to equal-mass Jaynes pairs.

No probability measure limit.
No entropy convergence theorem.
No MaxEnt optimizer transport theorem.
No AF/von-Neumann/state uniqueness theorem.
-/

namespace InfoGeometry.Canonical.FiniteJaynesInductiveFormalism

open Finset
open FiniteJaynesCenteredScoreBridge
open FiniteJaynesCenteredScoreBridge.FiniteReferenceStateOps
open FiniteJaynesFormalism

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A finite profile transport map between two finite atom sets. -/
abbrev ProfileTransport (ι κ : Type*) :=
  FiniteProfile ι → FiniteProfile κ

/-- A profile transport preserves subtraction pointwise. -/
def PreservesSub (Φ : ProfileTransport ι κ) : Prop :=
  ∀ f g : FiniteProfile ι, Φ (fun i => f i - g i) = fun j => Φ f j - Φ g j

/-- A profile transport preserves total mass. -/
def PreservesMass (Φ : ProfileTransport ι κ) : Prop :=
  ∀ f : FiniteProfile ι, (∑ j : κ, Φ f j) = ∑ i : ι, f i

/-- A profile transport sends one finite reference state to another. -/
def MapsReference (Φ : ProfileTransport ι κ)
    (R : FiniteReferenceState ι) (S : FiniteReferenceState κ) : Prop :=
  Φ R = S

/-- A profile transport sends one observation profile to another. -/
def MapsObservation (Φ : ProfileTransport ι κ)
    (obs : FiniteProfile ι) (obs' : FiniteProfile κ) : Prop :=
  Φ obs = obs'

omit [Fintype ι] [Fintype κ] in
/--
Transport of additive centered scores under an explicitly compatible finite
profile map.
-/
theorem map_centeredScore
    (Φ : ProfileTransport ι κ)
    (R : FiniteReferenceState ι) (S : FiniteReferenceState κ)
    (obs : FiniteProfile ι) (obs' : FiniteProfile κ)
    (hsub : PreservesSub Φ)
    (href : MapsReference Φ R S)
    (hobs : MapsObservation Φ obs obs') :
    Φ (centeredScore R obs) = centeredScore S obs' := by
  unfold centeredScore
  rw [hsub obs R, hobs, href]

/-- Equal-mass Jaynes compatibility transports along a mass-preserving map. -/
theorem map_equal_mass
    (Φ : ProfileTransport ι κ)
    (R : FiniteReferenceState ι) (S : FiniteReferenceState κ)
    (obs : FiniteProfile ι) (obs' : FiniteProfile κ)
    (hmassΦ : PreservesMass Φ)
    (href : MapsReference Φ R S)
    (hobs : MapsObservation Φ obs obs')
    (hmass : observationMass R obs = referenceMass R) :
    observationMass S obs' = referenceMass S := by
  unfold observationMass referenceMass
  calc
    ∑ j : κ, obs' j = ∑ j : κ, (Φ obs) j := by rw [hobs]
    _ = ∑ i : ι, obs i := hmassΦ obs
    _ = ∑ i : ι, R i := hmass
    _ = ∑ j : κ, (Φ R) j := by rw [hmassΦ R]
    _ = ∑ j : κ, S j := by rw [href]

/-- Build the next finite Jaynes pair from a compatible mass-preserving transport. -/
def transportJaynesPair
    (Φ : ProfileTransport ι κ)
    (P : FiniteJaynesPair ι)
    (S : FiniteReferenceState κ)
    (obs' : FiniteProfile κ)
    (hmassΦ : PreservesMass Φ)
    (href : MapsReference Φ P.reference S)
    (hobs : MapsObservation Φ P.observation obs') :
    FiniteJaynesPair κ :=
  ⟨{ reference := S
     observation := obs' }, by
      exact map_equal_mass Φ P.reference S P.observation obs' hmassΦ href hobs P.equal_mass⟩

/-- The transported Jaynes pair has the transported centered score. -/
theorem transportJaynesPair_centeredScore
    (Φ : ProfileTransport ι κ)
    (P : FiniteJaynesPair ι)
    (S : FiniteReferenceState κ)
    (obs' : FiniteProfile κ)
    (hmassΦ : PreservesMass Φ)
    (href : MapsReference Φ P.reference S)
    (hobs : MapsObservation Φ P.observation obs')
    (hsub : PreservesSub Φ) :
    Φ (centeredScore P.reference P.observation) =
      centeredScore (transportJaynesPair Φ P S obs' hmassΦ href hobs).reference
        (transportJaynesPair Φ P S obs' hmassΦ href hobs).observation := by
  change Φ (centeredScore P.reference P.observation) = centeredScore S obs'
  exact map_centeredScore Φ P.reference S P.observation obs' hsub href hobs

omit [Fintype ι] in
/-- Identity transport preserves subtraction. -/
theorem id_preservesSub :
    PreservesSub (fun f : FiniteProfile ι => f) := by
  intro f g
  rfl

/-- Identity transport preserves mass. -/
theorem id_preservesMass :
    PreservesMass (fun f : FiniteProfile ι => f) := by
  intro f
  rfl

omit [Fintype ι] in
/-- Identity transport preserves centered scores. -/
theorem id_map_centeredScore
    (R : FiniteReferenceState ι) (obs : FiniteProfile ι) :
    (fun f : FiniteProfile ι => f) (centeredScore R obs) = centeredScore R obs :=
  rfl

end InfoGeometry.Canonical.FiniteJaynesInductiveFormalism
