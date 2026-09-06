import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Krein.DoubledAdjoint
import InfoGeometry.Krein.CarrierTransport

/-!
# Primon/Krein ring constraints

This module records explicit algebraic constraints for doubled real operator lanes:

- `γ₅`/grading anti-commutation (off-block-diagonal constraint),
- Krein-self-adjointness via the doubled Krein adjoint,
- one-parameter flow law preserving the doubled Krein pairing.

It contains only finite operator predicates and their consequences.
-/

noncomputable section

namespace InfoGeometry.Algebraic.PrimonKreinRingConstraints

open InfoGeometry.Krein

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Endomorphisms on the doubled real carrier. -/
abbrev EndH : Type _ := DoubledEnd E

/--
Canonical grading operator (`γ₅` in the doubled real basis):
`(x, ξ) ↦ (x, -ξ)`.
-/
noncomputable abbrev gamma5 : DoubledSpace E →L[ℝ] DoubledSpace E :=
  spectral_epsilon (E := E)

/-- Doubled Krein pairing induced by `gamma5`. -/
noncomputable def doubledKreinInner (u v : DoubledSpace E) : ℝ :=
  inner ℝ ((gamma5 (E := E)) u) v

/-- Off-block-diagonal (chiral) constraint: anti-commutation with `γ₅`. -/
def IsOffBlockDiagonal (L : EndH (E := E)) : Prop :=
  L.comp (gamma5 (E := E)) = -((gamma5 (E := E)).comp L)

/--
Krein-self-adjointness on doubled space: `L♯ = L`.

This is definitionally aligned with `KreinSpace.IsKreinSelfAdjoint` on
`DoubledSpace E`.
-/
def IsKreinSelfAdjoint (L : EndH (E := E)) : Prop :=
  doubledKreinAdjoint (E := E) L = L

/--
`doubledKreinInner` agrees with the canonical `KreinSpace.kreinInner` on
`DoubledSpace E`.
-/
lemma doubledKreinInner_eq_kreinInner (u v : DoubledSpace E) :
    doubledKreinInner (E := E) u v = KreinSpace.kreinInner (H := DoubledSpace E) u v := by
  rfl

/--
`doubledKreinAdjoint` agrees with the canonical `KreinSpace.kreinAdjoint` on
`DoubledSpace E`.
-/
lemma doubledKreinAdjoint_eq_kreinAdjoint (L : EndH (E := E)) :
    doubledKreinAdjoint (E := E) L = KreinSpace.kreinAdjoint (H := DoubledSpace E) L := by
  rfl

/--
Characterization of doubled Krein-self-adjointness via the doubled Krein pairing.
-/
theorem isKreinSelfAdjoint_iff_doubledKreinInner
    (L : EndH (E := E)) :
    IsKreinSelfAdjoint (E := E) L ↔
      ∀ u v : DoubledSpace E,
        doubledKreinInner (E := E) (L u) v = doubledKreinInner (E := E) u (L v) := by
  constructor
  · intro h u v
    have hK : KreinSpace.IsKreinSelfAdjoint (H := DoubledSpace E) L := by
      simpa [IsKreinSelfAdjoint, doubledKreinAdjoint_eq_kreinAdjoint] using h
    have hk := (KreinSpace.isKreinSelfAdjoint_iff (H := DoubledSpace E) L).1 hK u v
    simpa [doubledKreinInner_eq_kreinInner] using hk
  · intro h
    have hK : KreinSpace.IsKreinSelfAdjoint (H := DoubledSpace E) L := by
      apply (KreinSpace.isKreinSelfAdjoint_iff (H := DoubledSpace E) L).2
      intro u v
      have hk := h u v
      simpa [doubledKreinInner_eq_kreinInner] using hk
    simpa [IsKreinSelfAdjoint, doubledKreinAdjoint_eq_kreinAdjoint] using hK

/--
The subtype of doubled real operators satisfying the two finite constraints.
-/
abbrev PrimonOperatorConstraint : Type _ :=
  Σ' op : EndH (E := E),
    IsOffBlockDiagonal (E := E) op ∧
      IsKreinSelfAdjoint (E := E) op

namespace PrimonOperatorConstraint

variable (constraint : PrimonOperatorConstraint (E := E))

abbrev op : EndH (E := E) := constraint.1
abbrev offBlockDiagonal : IsOffBlockDiagonal (E := E) constraint.1 := constraint.2.1
abbrev kreinSelfAdjoint : IsKreinSelfAdjoint (E := E) constraint.1 := constraint.2.2

end PrimonOperatorConstraint

/--
One-parameter doubled flow with explicit Krein-invariance law.

`U_add` is the additive-parameter composition law.
-/
structure HyperbolicPrimonFlow where
  U : ℝ → EndH (E := E)
  U_zero : U 0 = ContinuousLinearMap.id ℝ (DoubledSpace E)
  U_add : ∀ s t, U (s + t) = (U s).comp (U t)
  preservesKreinInner :
    ∀ t u v,
      doubledKreinInner (E := E) (U t u) (U t v) =
        doubledKreinInner (E := E) u v

/--
Generator-level constrained flow.

This keeps all operatorial constraints explicit and local to the doubled carrier.
-/
structure HyperbolicPrimonFlowWithGenerator extends HyperbolicPrimonFlow (E := E) where
  generator : EndH (E := E)
  generator_offBlockDiagonal : IsOffBlockDiagonal (E := E) generator
  generator_kreinSelfAdjoint : IsKreinSelfAdjoint (E := E) generator

/-- Any constrained generator has an off-block-diagonal generator. -/
theorem generator_is_offBlockDiagonal
    (F : HyperbolicPrimonFlowWithGenerator (E := E)) :
    IsOffBlockDiagonal (E := E) F.generator :=
  F.generator_offBlockDiagonal

/-- Any constrained generator has a Krein-self-adjoint generator. -/
theorem generator_is_kreinSelfAdjoint
    (F : HyperbolicPrimonFlowWithGenerator (E := E)) :
    IsKreinSelfAdjoint (E := E) F.generator :=
  F.generator_kreinSelfAdjoint

/--
Read a `HyperbolicPrimonFlow` as a `CarrierTransport` on the canonical
`doubledCarrier`.

Since `doubledCarrier` stores the ambient Hilbert bilinear pairing, this bridge
requires an explicit pairing-preservation property for that pairing.
-/
noncomputable def HyperbolicPrimonFlow.toCarrierTransport
    (F : HyperbolicPrimonFlow (E := E))
    (hCarrierPairing :
      ∀ t u v,
        (doubledCarrier (E := E)).kreinPairing (F.U t u) (F.U t v) =
          (doubledCarrier (E := E)).kreinPairing u v) :
    CarrierTransport (doubledCarrier (E := E)) where
  transport := F.U
  transport_zero := F.U_zero
  transport_add := F.U_add
  transport_preserves_pairing := hCarrierPairing

end InfoGeometry.Algebraic.PrimonKreinRingConstraints
