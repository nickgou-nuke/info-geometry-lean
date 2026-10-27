/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornRegularOperators
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.Abel

/-!
# Canonical Zorn derivations on regular multiplication operators

The primitive left-regular declarations are relocated from
`SplitOctonionChiralOperatorSupergrading` under their original namespace.
The identity is a direct consequence of the existing Leibniz law and does
not require a Cartan basis or a CAR representation.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading

open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-- The native left-regular operator, reusing the genuine circular Peirce
owner rather than creating a second multiplication representation. -/
noncomputable def leftRegular (x : CZ) : EndCZ :=
  leftMultiplication x

@[simp] theorem leftRegular_apply (x y : CZ) :
    leftRegular x y = x * y :=
  rfl

/-- A genuine derivation acts on the left-regular representation by the
expected commutator identity `[D,Lₓ] = L_(D x)`.  No associativity assumption
is used; the proof is exactly the Leibniz law. -/
theorem derivation_lie_leftRegular
    (D : EndCZ) (hD : IsDerivation D) (x : CZ) :
    ⁅D, leftRegular x⁆ = leftRegular (D x) := by
  rw [LieRing.of_associative_ring_bracket]
  apply LinearMap.ext
  intro y
  change D (x * y) - x * D y = D x * y
  rw [hD x y]
  abel

end InfoGeometry.Lie.SplitOctonionChiralOperatorSupergrading
