import InfoGeometry.Quantum.Fierz
import InfoGeometry.Algebra.FiniteSpinAlgebra
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

open InfoGeometry.Quantum.Fierz
open QuantumPresentation

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
  hilbert_nonneg : ∀ ψ, 0 ≤ hilbert ψ
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

This keeps Fierz scalar channels as readouts while making the support/generator
lane explicit at the call site.
-/
@[rep_depth operator]
def toQuantumPresentationWith
    (R : FierzChannelReadout)
    (support : R.State → Prop)
    (generator : R.State → R.State) :
    Presentation where
  Scalar := ℝ
  State := R.State
  Observable := R.State → R.State
  act := fun A ψ => A ψ
  support := support
  generator := generator
  metricReadout := R.hilbert
  phaseReadout := R.symplectic

/--
Default support lane used by lightweight translator consumers.
-/
@[rep_depth operator]
def defaultSupport (R : FierzChannelReadout) : R.State → Prop :=
  fun ψ => 0 ≤ R.hilbert ψ

/--
Default generator lane used by lightweight translator consumers.
-/
@[rep_depth operator]
def defaultGenerator (R : FierzChannelReadout) : R.State → R.State :=
  fun ψ => ψ

/--
Default translator map preserving scalar readout channels.
-/
@[rep_depth operator]
def toQuantumPresentation (R : FierzChannelReadout) : Presentation :=
  toQuantumPresentationWith R (defaultSupport R) (defaultGenerator R)

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
  hilbert_nonneg := InfoGeometry.Quantum.Fierz.infoHilbert_nonneg (E := E)
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
