/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Krein.DoubledAdjoint
import InfoGeometry.Krein.CarrierTransport

/-!
# Primon/Krein ring constraints (Lean-safe socket)

This module records explicit algebraic constraints for doubled real operator lanes:

- `γ₅`/grading anti-commutation (off-block-diagonal constraint),
- Krein-self-adjointness via the doubled Krein adjoint,
- one-parameter flow law preserving the doubled Krein pairing.

It is a structural packet surface: no analytic zeta/RH/zero-location claims.
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

/-- The local doubled pairing and adjoint are the canonical Krein operations,
and the transported adjoint satisfies the genuine pairing identity. This
collects the definitional carrier compatibility together with its operational
consequence, rather than exporting the compatibility equalities separately. -/
theorem doubledKrein_pairing_adjoint_compatibility
    (L : EndH (E := E)) :
    (∀ u v : DoubledSpace E,
      doubledKreinInner (E := E) u v =
        KreinSpace.kreinInner (H := DoubledSpace E) u v) ∧
    doubledKreinAdjoint (E := E) L =
      KreinSpace.kreinAdjoint (H := DoubledSpace E) L ∧
    (∀ u v : DoubledSpace E,
      doubledKreinInner (E := E) (L u) v =
        doubledKreinInner (E := E) u (doubledKreinAdjoint (E := E) L v)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    rfl
  · rfl
  · intro u v
    change KreinSpace.kreinInner (H := DoubledSpace E) (L u) v =
      KreinSpace.kreinInner (H := DoubledSpace E) u
        (KreinSpace.kreinAdjoint (H := DoubledSpace E) L v)
    exact KreinSpace.kreinInner_kreinAdjoint (H := DoubledSpace E) L u v

/--
Characterization of doubled Krein-self-adjointness via the doubled Krein pairing.
-/
theorem isKreinSelfAdjoint_iff_doubledKreinInner
    (L : EndH (E := E)) :
    IsKreinSelfAdjoint (E := E) L ↔
      ∀ u v : DoubledSpace E,
        doubledKreinInner (E := E) (L u) v = doubledKreinInner (E := E) u (L v) :=
  KreinSpace.isKreinSelfAdjoint_iff (H := DoubledSpace E) L

/-- Conjugation by the doubled grading is an involution on endomorphisms. -/
theorem gamma5Conjugation_involutive (L : EndH (E := E)) :
    (gamma5 (E := E)).comp
        (((gamma5 (E := E)).comp (L.comp (gamma5 (E := E)))).comp
          (gamma5 (E := E))) = L := by
  apply ContinuousLinearMap.ext
  intro u
  have hε (x : DoubledSpace E) :
      gamma5 (E := E) (gamma5 (E := E) x) = x := by
    have h := congrArg (fun T : EndH (E := E) => T x)
      (spectral_epsilon_involution E)
    simpa [gamma5, ContinuousLinearMap.comp_apply] using h
  change gamma5 (E := E)
      (gamma5 (E := E) (L (gamma5 (E := E) (gamma5 (E := E) u))) ) = L u
  rw [hε u]
  exact hε (L u)

/-- Anticommutation with the grading is equivalent to conjugation by the grading
being minus the operator. This is the operator-level passage from a chiral
off-block condition to a Hilbert skew-adjointness calculation. -/
theorem isOffBlockDiagonal_iff_gamma5Conjugate_eq_neg
    (L : EndH (E := E)) :
    IsOffBlockDiagonal (E := E) L ↔
      (gamma5 (E := E)).comp (L.comp (gamma5 (E := E))) = -L := by
  constructor
  · intro hOff
    apply ContinuousLinearMap.ext
    intro u
    have hε : gamma5 (E := E) (gamma5 (E := E) u) = u := by
      have h := congrArg (fun T : EndH (E := E) => T u)
        (spectral_epsilon_involution E)
      simpa [gamma5, ContinuousLinearMap.comp_apply] using h
    have h := congrArg (fun T : EndH (E := E) => T (gamma5 (E := E) u)) hOff
    change L (gamma5 (E := E) (gamma5 (E := E) u)) =
      -(gamma5 (E := E) (L (gamma5 (E := E) u))) at h
    rw [hε] at h
    simpa using (congrArg (fun x : DoubledSpace E => -x) h).symm
  · intro hConj
    apply ContinuousLinearMap.ext
    intro u
    have hε : gamma5 (E := E) (gamma5 (E := E) u) = u := by
      have h := congrArg (fun T : EndH (E := E) => T u)
        (spectral_epsilon_involution E)
      simpa [gamma5, ContinuousLinearMap.comp_apply] using h
    have h := congrArg (fun T : EndH (E := E) => T (gamma5 (E := E) u)) hConj
    change gamma5 (E := E)
        (L (gamma5 (E := E) (gamma5 (E := E) u))) =
      -(L (gamma5 (E := E) u)) at h
    rw [hε] at h
    simpa using (congrArg (fun x : DoubledSpace E => -x) h).symm

/-- On the doubled operator carrier, the off-block and Krein-self-adjoint
conditions together are exactly the off-block and Hilbert-skew-adjoint
conditions. The grading conjugation supplies the sign change between the two
adjoints. -/
theorem offBlock_kreinSelfAdjoint_iff_offBlock_hilbertSkewAdjoint
    (L : EndH (E := E)) :
    (IsOffBlockDiagonal (E := E) L ∧ IsKreinSelfAdjoint (E := E) L) ↔
      (IsOffBlockDiagonal (E := E) L ∧
        ContinuousLinearMap.adjoint L = -L) := by
  constructor
  · rintro ⟨hOff, hKrein⟩
    have hK : (gamma5 (E := E)).comp
        ((ContinuousLinearMap.adjoint L).comp (gamma5 (E := E))) = L := by
      change doubledKreinAdjoint (E := E) L = L at hKrein
      exact hKrein
    have hAdjConj : (gamma5 (E := E)).comp
        (L.comp (gamma5 (E := E))) = ContinuousLinearMap.adjoint L := by
      calc
        (gamma5 (E := E)).comp (L.comp (gamma5 (E := E))) =
            (gamma5 (E := E)).comp
              (((gamma5 (E := E)).comp
                ((ContinuousLinearMap.adjoint L).comp (gamma5 (E := E)))).comp
                (gamma5 (E := E))) := by rw [hK]
        _ = ContinuousLinearMap.adjoint L := gamma5Conjugation_involutive
          (E := E) (ContinuousLinearMap.adjoint L)
    exact ⟨hOff,
      hAdjConj.symm.trans
        ((isOffBlockDiagonal_iff_gamma5Conjugate_eq_neg (E := E) L).mp hOff)⟩
  · rintro ⟨hOff, hAdj⟩
    refine ⟨hOff, ?_⟩
    change doubledKreinAdjoint (E := E) L = L
    calc
      (gamma5 (E := E)).comp
          ((ContinuousLinearMap.adjoint L).comp (gamma5 (E := E))) =
        (gamma5 (E := E)).comp ((-L).comp (gamma5 (E := E))) := by rw [hAdj]
      _ = -((gamma5 (E := E)).comp (L.comp (gamma5 (E := E)))) := by
        apply ContinuousLinearMap.ext
        intro u
        simp [ContinuousLinearMap.comp_apply]
      _ = -(-L) := by
        rw [(isOffBlockDiagonal_iff_gamma5Conjugate_eq_neg (E := E) L).mp hOff]
      _ = L := by simp

/--
Static ring-constraint packet for a doubled real operator.

This is the minimal algebraic surface needed for the hyperbolic/chiral lane.
-/
abbrev PrimonOperatorConstraintPacket : Type _ :=
  Σ' op : EndH (E := E),
    IsOffBlockDiagonal (E := E) op ∧
      IsKreinSelfAdjoint (E := E) op

namespace PrimonOperatorConstraintPacket

variable (packet : PrimonOperatorConstraintPacket (E := E))

abbrev op : EndH (E := E) := packet.1
abbrev offBlockDiagonal : IsOffBlockDiagonal (E := E) packet.1 := packet.2.1
abbrev kreinSelfAdjoint : IsKreinSelfAdjoint (E := E) packet.1 := packet.2.2

end PrimonOperatorConstraintPacket

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
Generator-level constrained flow packet.

This keeps all operatorial constraints explicit and local to the doubled carrier.
-/
structure HyperbolicPrimonFlowWithGenerator extends HyperbolicPrimonFlow (E := E) where
  generator : EndH (E := E)
  generator_offBlockDiagonal : IsOffBlockDiagonal (E := E) generator
  generator_kreinSelfAdjoint : IsKreinSelfAdjoint (E := E) generator

/-- A generator satisfying the chiral and Krein constraints is skew-adjoint
for the ambient Hilbert inner product. -/
theorem generator_hilbertSkewAdjoint
    (F : HyperbolicPrimonFlowWithGenerator (E := E)) :
    ContinuousLinearMap.adjoint F.generator = -F.generator := by
  exact ((offBlock_kreinSelfAdjoint_iff_offBlock_hilbertSkewAdjoint
    (E := E) F.generator).mp
      ⟨F.generator_offBlockDiagonal, F.generator_kreinSelfAdjoint⟩).2

/--
Bridge: read a `HyperbolicPrimonFlow` as a `CarrierTransport` on the canonical
`doubledCarrier`.

Since `doubledCarrier` stores the ambient Hilbert bilinear pairing, this bridge
requires an explicit pairing-preservation witness for that pairing.
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
