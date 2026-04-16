import InfoGeometry.Canonical.Fierz
import InfoGeometry.Canonical.QuantumPresentation
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.FierzReadout

Translator surface from operator/spinor channels to scalar readouts via Fierz
identities.

This file does not introduce new Clifford owners. It packages existing Fierz
channels as a typed readout interface and connects that interface to
`QuantumPresentation`.
-/

namespace InfoGeometry.Canonical.FierzReadout

open InfoGeometry.Canonical.Fierz
open InfoGeometry.Canonical.QuantumPresentation

/--
Typed Fierz readout package.

It records scalar channels and the algebraic closure identity they must satisfy.
-/
@[rep_depth operator]
structure FierzChannelReadout where
  State : Type
  scalar : State → ℝ
  symplectic : State → ℝ
  hilbert : State → ℝ
  area : State → ℝ
  fierzIdentity :
    ∀ ψ, (hilbert ψ)^2 = (scalar ψ)^2 + (symplectic ψ)^2 + 4 * (area ψ)

namespace FierzChannelReadout

/-- Majorana-shadow predicate on a Fierz readout package. -/
@[rep_depth operator]
def IsMajoranaShadow (R : FierzChannelReadout) (ψ : R.State) : Prop :=
  R.area ψ = 0

/-- Fierz identity restricted to the zero-area (Majorana-shadow) lane. -/
@[rep_depth operator]
theorem fierz_majorana
    (R : FierzChannelReadout)
    (ψ : R.State)
    (hMajorana : R.IsMajoranaShadow ψ) :
    (R.hilbert ψ)^2 = (R.scalar ψ)^2 + (R.symplectic ψ)^2 := by
  have hBase := R.fierzIdentity ψ
  unfold IsMajoranaShadow at hMajorana
  rw [hMajorana] at hBase
  simpa using hBase

/--
Translator map from Fierz readout package to the generic presentation
interface.

This keeps Fierz scalar channels as readouts while leaving support/generator as
minimal interface placeholders.
-/
@[rep_depth operator]
def toQuantumPresentation (R : FierzChannelReadout) : QuantumPresentation where
  Scalar := ℝ
  State := R.State
  Observable := R.State → R.State
  act := fun A ψ => A ψ
  support := fun _ => True
  generator := fun ψ => ψ
  metricReadout := R.hilbert
  phaseReadout := R.symplectic

@[rep_depth operator]
theorem toQuantumPresentation_metricReadout
    (R : FierzChannelReadout) (ψ : R.State) :
    (R.toQuantumPresentation.metricReadout ψ) = R.hilbert ψ := by
  rfl

@[rep_depth operator]
theorem toQuantumPresentation_phaseReadout
    (R : FierzChannelReadout) (ψ : R.State) :
    (R.toQuantumPresentation.phaseReadout ψ) = R.symplectic ψ := by
  rfl

end FierzChannelReadout

section DoubledCarrier

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => InfoGeometry.Krein.DoubledSpace E

/--
Canonical doubled-carrier Fierz readout package from existing owner channels.
-/
@[rep_depth operator]
noncomputable def doubledFierzReadout : FierzChannelReadout where
  State := H₂
  scalar := infoScalar (E := E)
  symplectic := infoSymplectic (E := E)
  hilbert := infoHilbert (E := E)
  area := infoArea (E := E)
  fierzIdentity := information_fierz_identity (E := E)

/-- Tagged presentation witness for the doubled/Krein Fierz lane. -/
@[rep_depth operator]
noncomputable def taggedDoubledFierzPresentation : TaggedPresentation where
  lane := PresentationLane.doubledKrein
  data := (doubledFierzReadout (E := E)).toQuantumPresentation

@[rep_depth operator]
theorem doubledFierz_majorana
    (ψ : H₂)
    (hMajorana : (doubledFierzReadout (E := E)).IsMajoranaShadow ψ) :
    ((doubledFierzReadout (E := E)).hilbert ψ)^2
      = ((doubledFierzReadout (E := E)).scalar ψ)^2
        + ((doubledFierzReadout (E := E)).symplectic ψ)^2 := by
  exact FierzChannelReadout.fierz_majorana (R := doubledFierzReadout (E := E)) ψ hMajorana

end DoubledCarrier

end InfoGeometry.Canonical.FierzReadout
