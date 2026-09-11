/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2RootPCAlignment
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport

/-!
# Concrete PC words for canonical residual coordinates

This file embeds a root-indexed residual Boolean family into the verified six
PC coordinates.  Coordinates outside the inversion set are set to `false`.
It deliberately does not identify this image with the Chevalley residual
subgroup: that requires ordered root products and their native injectivity.
-/

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords

open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2RootPCAlignment
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable def residualToPCExponent (w : G2WeylElement)
    (e : CanonicalResidualExponent w) (i : Fin 6) : Bool :=
  if h : ∃ α : { α : G2PositiveRoot // α ∈ canonicalSignedInversionRoots w },
      rootPCAlignment α.1 = i then
    e (Classical.choose h)
  else
    false

theorem residualToPCExponent_at (w : G2WeylElement)
    (e : CanonicalResidualExponent w)
    (α : { α : G2PositiveRoot // α ∈ canonicalSignedInversionRoots w }) :
    residualToPCExponent w e (rootPCAlignment α.1) = e α := by
  classical
  let h : ∃ β : { α : G2PositiveRoot //
      α ∈ canonicalSignedInversionRoots w }, rootPCAlignment β.1 =
      rootPCAlignment α.1 := ⟨α, rfl⟩
  rw [residualToPCExponent, dif_pos h]
  congr 1
  apply Subtype.ext
  exact rootPCAlignment.injective (Classical.choose_spec h)

noncomputable def canonicalResidualPCWord (w : G2WeylElement)
    (e : CanonicalResidualExponent w) : SplitOctF2Aut :=
  pcWord (residualToPCExponent w e)

theorem canonicalResidualPCWord_mem_pcSubgroup (w : G2WeylElement)
    (e : CanonicalResidualExponent w) :
    canonicalResidualPCWord w e ∈ pcSubgroup := by
  exact pcWord_mem_pcSubgroup _

theorem canonicalResidualPCWord_injective (w : G2WeylElement) :
    Function.Injective (canonicalResidualPCWord w) := by
  intro e₁ e₂ h
  apply funext
  intro α
  have hExp : residualToPCExponent w e₁ = residualToPCExponent w e₂ := by
    apply pcWord_injective_concrete
    simpa [canonicalResidualPCWord] using h
  have hpc := congrFun hExp (rootPCAlignment α.1)
  rw [residualToPCExponent_at, residualToPCExponent_at] at hpc
  exact hpc

theorem canonicalResidualPCWord_range_card (w : G2WeylElement) :
    Nat.card (Set.range (canonicalResidualPCWord w)) =
      2 ^ weylLength w := by
  rw [Nat.card_range_of_injective (canonicalResidualPCWord_injective w)]
  simp [CanonicalResidualExponent, canonicalSignedInversionRoots_card w]

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualPCWords
