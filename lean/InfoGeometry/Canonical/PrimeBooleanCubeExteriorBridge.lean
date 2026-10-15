import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeExteriorRepresentation
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip

/-!
# InfoGeometry.Canonical.PrimeBooleanCubeExteriorBridge

Finite bridge from the prime Boolean-cube owner surface to the exterior
square-free carrier.

This file is finite-only. It does not assert an infinite Euler product,
analytic continuation, OPE/CFT data, or any Hilbert--Polya claim.

The purpose is representation coherence:

* the Boolean-cube vertex and the exterior square-free state are the same
  finite occupied set, viewed through two presentation layers;
* the Majorana bit-flip is preserved under that transport;
* cardinality, chirality, state product, and logarithmic energy are preserved.
-/

noncomputable section

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace InfoGeometry.Canonical.PrimeBooleanCubeExteriorBridge

open InfoGeometry.Arithmetic.PrimeBooleanCube
open InfoGeometry.Arithmetic.PrimeExteriorRepresentation
open InfoGeometry.Arithmetic.PrimeMajoranaBitFlip

/-- The finite prime cutoff used by the Boolean cube and exterior bridge. -/
abbrev PrimeCutoff := InfoGeometry.Arithmetic.PrimeBitWittenIndex.PrimeRegister

/-- The prime-mode labels of the transported exterior carrier. -/
abbrev PrimeMode (P : PrimeCutoff) := {p : ℕ // p ∈ P.primes}

/-- The transported exterior carrier over a prime cutoff. -/
abbrev ExteriorState (P : PrimeCutoff) := SquareFreePrimeState (PrimeMode P)

/-- Embedding from attached Boolean-cube vertices into the transported carrier. -/
def toPrimeModeEmbedding {P : PrimeCutoff} (v : Vertex P) :
    {n // n ∈ v.val} ↪ PrimeMode P :=
  ⟨fun p => ⟨p.1, v.property p.2⟩, by
    intro a b h
    cases a
    cases b
    simp at h
    apply Subtype.ext
    exact h⟩

/-- Boolean-cube vertex transported to the exterior prime-mode carrier. -/
def toExteriorState {P : PrimeCutoff} (v : Vertex P) :
    ExteriorState P :=
  v.val.attach.map
    ⟨fun p => ⟨p.1, v.property p.2⟩,
      by
        intro a b h
        cases a
        cases b
        simp at h
        apply Subtype.ext
        exact h⟩

/-- The transported exterior carrier viewed as a product of prime labels. -/
def stateNat {P : PrimeCutoff} (S : ExteriorState P) : ℕ :=
  Finset.prod S fun p => p.1

/-- The transported exterior carrier viewed as a logarithmic energy sum. -/
def exteriorEnergy {P : PrimeCutoff} (S : ExteriorState P) : ℝ :=
  Finset.sum S fun p => Real.log p.1

/-- The transported exterior carrier has the same cardinality. -/
theorem boolState_to_finset_preserves_card
    {P : PrimeCutoff} (v : Vertex P) :
    (toExteriorState v).card = v.val.card := by
  unfold toExteriorState
  simpa using
    (Finset.card_map
      (fun p : {n // n ∈ v.val} => ⟨p.1, v.property p.2⟩)
      (s := v.val.attach))

/-- The transported exterior carrier has the same finite state product. -/
theorem boolState_to_finset_preserves_stateNat
    {P : PrimeCutoff} (v : Vertex P) :
    stateNat (toExteriorState v) = representedNat v := by
  change (∏ x ∈ v.val.attach.map (toPrimeModeEmbedding (v := v)), x.1) =
    ∏ p ∈ v.val, p
  calc
    (∏ x ∈ v.val.attach.map (toPrimeModeEmbedding (v := v)), x.1) =
        ∏ p ∈ v.val.attach, (toPrimeModeEmbedding (v := v) p).1 := by
      rw [Finset.prod_map]
    _ = ∏ p ∈ v.val.attach, p.1 := by
      apply Finset.prod_congr rfl
      intro p hp
      rfl
    _ = ∏ p ∈ v.val, p := by
      simpa using (Finset.prod_attach v.val (fun p : ℕ => p))

/-- The transported exterior carrier preserves the Möbius/chirality readout. -/
theorem boolState_to_finset_preserves_chirality
    {P : PrimeCutoff} (v : Vertex P) :
    ArithmeticFunction.moebius
        (stateNat (toExteriorState v)) =
      globalChirality P v.val := by
  rw [boolState_to_finset_preserves_stateNat]
  exact mobius_representedNat_eq_globalChirality P v

/-- The transported exterior carrier preserves the finite logarithmic energy. -/
theorem boolState_to_finset_preserves_energy
    {P : PrimeCutoff} (v : Vertex P) :
    exteriorEnergy (toExteriorState v) =
      Finset.sum v.val (fun p => Real.log p) := by
  change (∑ x ∈ v.val.attach.map (toPrimeModeEmbedding (v := v)), Real.log x.1) =
    ∑ p ∈ v.val, Real.log p
  calc
    (∑ x ∈ v.val.attach.map (toPrimeModeEmbedding (v := v)), Real.log x.1) =
        ∑ p ∈ v.val.attach, Real.log (toPrimeModeEmbedding (v := v) p).1 := by
      rw [Finset.sum_map]
    _ = ∑ p ∈ v.val.attach, Real.log p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      rfl
    _ = ∑ p ∈ v.val, Real.log p := by
      simpa using (Finset.sum_attach v.val (fun p : ℕ => Real.log p))

end InfoGeometry.Canonical.PrimeBooleanCubeExteriorBridge
