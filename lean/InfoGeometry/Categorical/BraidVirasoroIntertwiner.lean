/- SPDX-License-Identifier: Apache-2.0 -/

/-
# Braid--Virasoro intertwiner interface

This module supplies the missing carrier-level interface.  It does not invent a
representation of the categorical braid colimit on a Fock carrier.  Such a
representation remains an explicit input.

The commutator theorem is stated in the correct form: commuting with each
Virasoro mode implies commuting with their commutator.  The stronger-looking
identity
  [U Lₘ, U Lₙ] = U [Lₘ,Lₙ]
would require extra hypotheses and is not asserted.
-/

import InfoGeometry.Categorical.BraidHestenesKreinVirasoroBridge
import Mathlib.Algebra.Module.End

noncomputable section

namespace InfoGeometry.Categorical.BraidVirasoroIntertwiner

universe u v

/-- Virasoro modes acting on a linear carrier. -/
abbrev VirasoroGenerator
    (𝕜 : Type u) (V : Type v)
    [Semiring 𝕜] [AddCommMonoid V] [Module 𝕜 V] :=
  ℤ → Module.End 𝕜 V

/-- A braid representation together with modewise Virasoro invariance. -/
structure BraidVirasoroIntertwiner
    (𝕜 : Type u) (V : Type v)
    [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (B : Type v) [Group B]
    (L : VirasoroGenerator 𝕜 V) where
  braidRep : B →* (V ≃ₗ[𝕜] V)
  intertwine : ∀ (b : B) (m : ℤ),
    Commute ((braidRep b : V →ₗ[𝕜] V)) (L m)

/-- The commutator in the endomorphism ring. -/
def commutator
    {𝕜 : Type u} {V : Type v}
    [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (A B : Module.End 𝕜 V) : Module.End 𝕜 V :=
  A * B - B * A

namespace BraidVirasoroIntertwiner

variable {𝕜 : Type u} {V : Type v}
variable [CommRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
variable {B : Type v} [Group B]
variable {L : VirasoroGenerator 𝕜 V}
variable (I : BraidVirasoroIntertwiner 𝕜 V B L)

/-- A braid operator commutes with every Virasoro commutator. -/
theorem commutes_with_commutator (b : B) (m n : ℤ) :
    Commute
      ((I.braidRep b : V →ₗ[𝕜] V))
      (commutator (L m) (L n)) := by
  change
    (I.braidRep b : V →ₗ[𝕜] V) *
          (L m * L n - L n * L m) =
      (L m * L n - L n * L m) *
          (I.braidRep b : V →ₗ[𝕜] V)
  have hm := (I.intertwine b m).eq
  have hn := (I.intertwine b n).eq
  calc
    (I.braidRep b : V →ₗ[𝕜] V) *
          (L m * L n - L n * L m) =
        (I.braidRep b : V →ₗ[𝕜] V) * L m * L n -
          (I.braidRep b : V →ₗ[𝕜] V) * L n * L m := by
            rw [mul_sub]
    _ = L m * (I.braidRep b : V →ₗ[𝕜] V) * L n -
          L n * (I.braidRep b : V →ₗ[𝕜] V) * L m := by
            rw [hm, hn]
    _ = L m * L n * (I.braidRep b : V →ₗ[𝕜] V) -
          L n * L m * (I.braidRep b : V →ₗ[𝕜] V) := by
            rw [hn, hm]
    _ = (L m * L n - L n * L m) *
          (I.braidRep b : V →ₗ[𝕜] V) := by
            rw [sub_mul]

/-- The modewise intertwining law extends to the Virasoro commutator. -/
theorem commutator_intertwining (b : B) (m n : ℤ) :
    Commute
      ((I.braidRep b : V →ₗ[𝕜] V))
      (commutator (L m) (L n)) :=
  I.commutes_with_commutator b m n

/-- The representation law makes finite products of braid operators available
to the same carrier-level interface. -/
theorem representation_mul (b c : B) :
    I.braidRep (b * c) = I.braidRep b * I.braidRep c := by
  exact map_mul I.braidRep b c

end BraidVirasoroIntertwiner

/-- A closure packet combining the existing audited bridge with an explicit
carrier-level intertwiner input. -/
structure CertifiedBraidVirasoroClosure
    (Bridge Carrier : Type*)
    [CommRing Carrier]
    (𝕜 : Type*) [CommRing 𝕜]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    (B : Type*) [Group B]
    (L : VirasoroGenerator 𝕜 Carrier) where
  bridge : Bridge
  intertwiner : BraidVirasoroIntertwiner 𝕜 Carrier B L

/-- The existing cross-lane bridge can be extended once a genuine intertwiner
is supplied.  No intertwiner is constructed here. -/
def attach
    {Bridge Carrier : Type*}
    [CommRing Carrier]
    {𝕜 : Type*} [CommRing 𝕜]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {B : Type*} [Group B]
    {L : VirasoroGenerator 𝕜 Carrier}
    (bridge : Bridge)
    (intertwiner : BraidVirasoroIntertwiner 𝕜 Carrier B L) :
    CertifiedBraidVirasoroClosure Bridge Carrier 𝕜 B L :=
  ⟨bridge, intertwiner⟩

end InfoGeometry.Categorical.BraidVirasoroIntertwiner
