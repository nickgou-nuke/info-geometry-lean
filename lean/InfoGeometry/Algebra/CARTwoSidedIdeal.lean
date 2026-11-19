/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import InfoGeometry.Physics.SplitCliffordAlgebras
import InfoGeometry.Algebra.CPTComplexStructure

/-!
# Two-sided ideal obstruction for a unit anticommutator

In an arbitrary associative ring, `a * b + b * a = 1` implies that a
two-sided ideal containing either `a` or `b` is the whole ring. Neither
square-zero hypotheses nor simplicity of the ring are required. The quotient
is Mathlib's native `RingCon.Quotient` associated with `TwoSidedIdeal.ringCon`.

A unital ring homomorphism killing either generator has a subsingleton target;
surjectivity is not needed. The final compatibility map packages the existing
`Cl11Atom` isotropic sheets as the existing `SplitClifford.CARPair`, then applies
the quotient obstruction. No new Clifford or CAR representation is introduced.
-/

namespace InfoGeometry.Algebra.CARTwoSidedIdeal

variable {R S : Type*} [Ring R] [Ring S] {a b : R}

/-- Either left or right multiplication of `a` stays in a two-sided ideal,
so the unit anticommutator makes that ideal full. -/
theorem eq_top_of_anticommutator_mem_left
    (h : a * b + b * a = 1) (I : TwoSidedIdeal R) (ha : a ∈ I) :
    I = ⊤ := by
  apply (TwoSidedIdeal.one_mem_iff I).mp
  rw [← h]
  exact I.add_mem (I.mul_mem_right a b ha) (I.mul_mem_left b a ha)

/-- The same obstruction applies when the second generator belongs to the ideal. -/
theorem eq_top_of_anticommutator_mem_right
    (h : a * b + b * a = 1) (I : TwoSidedIdeal R) (hb : b ∈ I) :
    I = ⊤ := by
  apply (TwoSidedIdeal.one_mem_iff I).mp
  rw [← h]
  exact I.add_mem (I.mul_mem_left a b hb) (I.mul_mem_right b a hb)

/-- Each single generator already generates the whole two-sided ideal. -/
theorem singleton_spans_eq_top (h : a * b + b * a = 1) :
    TwoSidedIdeal.span ({a} : Set R) = ⊤ ∧
      TwoSidedIdeal.span ({b} : Set R) = ⊤ := by
  constructor
  · exact eq_top_of_anticommutator_mem_left h _
      (TwoSidedIdeal.subset_span (Set.mem_singleton a))
  · exact eq_top_of_anticommutator_mem_right h _
      (TwoSidedIdeal.subset_span (Set.mem_singleton b))

/-- Quotienting by a two-sided ideal that kills either generator gives the
zero ring, expressed by subsingleton of the actual quotient carrier. -/
theorem quotient_subsingleton_of_anticommutator_mem
    (h : a * b + b * a = 1) (I : TwoSidedIdeal R)
    (hmem : a ∈ I ∨ b ∈ I) : Subsingleton I.ringCon.Quotient := by
  have htop : I = ⊤ := hmem.elim
    (eq_top_of_anticommutator_mem_left h I)
    (eq_top_of_anticommutator_mem_right h I)
  apply (RingCon.subsingleton_quotient (c := I.ringCon)).mpr
  exact congrArg (fun J : TwoSidedIdeal R => J.ringCon) htop

/-- Unitality alone forces the entire target to be subsingleton if either
generator is killed; the homomorphism need not be surjective. -/
theorem codomain_subsingleton_of_anticommutator_map_zero
    (h : a * b + b * a = 1) (f : R →+* S)
    (hzero : f a = 0 ∨ f b = 0) : Subsingleton S := by
  apply subsingleton_of_zero_eq_one
  have hmap := congrArg f h
  rcases hzero with ha | hb
  · simpa only [map_add, map_mul, map_one, ha, zero_mul, mul_zero, add_zero] using hmap
  · simpa only [map_add, map_mul, map_one, hb, zero_mul, mul_zero, add_zero] using hmap

/-- The native quotient obstruction for the repository's existing CAR interface. -/
theorem car_quotient_subsingleton (P : SplitClifford.CARPair R)
    (I : TwoSidedIdeal R) (hmem : P.ann ∈ I ∨ P.cre ∈ I) :
    Subsingleton I.ringCon.Quotient :=
  quotient_subsingleton_of_anticommutator_mem P.anti I hmem

/-- Killing either mode of an existing CAR pair trivializes a unital target. -/
theorem car_codomain_subsingleton (P : SplitClifford.CARPair R)
    (f : R →+* S) (hzero : f P.ann = 0 ∨ f P.cre = 0) : Subsingleton S :=
  codomain_subsingleton_of_anticommutator_map_zero P.anti f hzero

end InfoGeometry.Algebra.CARTwoSidedIdeal

namespace InfoGeometry.Algebra.CPT.Cl11Atom

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The existing isotropic sheet construction supplies the existing one-mode
CAR interface by its already established square and anticommutator identities. -/
noncomputable def toCARPair (atom : Cl11Atom R) : SplitClifford.CARPair R where
  ann := isotropicSheetPlus atom
  cre := isotropicSheetMinus atom
  ann_sq := isotropicSheetPlus_sq atom
  cre_sq := isotropicSheetMinus_sq atom
  anti := isotropicSheets_anticommute atom

/-- A quotient killing either isotropic sheet of a represented `Cl(1,1)` atom
is subsingleton. This uses the explicit compatibility map to the CAR interface. -/
theorem sheet_quotient_subsingleton (atom : Cl11Atom R)
    (I : TwoSidedIdeal R)
    (hmem : isotropicSheetPlus atom ∈ I ∨ isotropicSheetMinus atom ∈ I) :
    Subsingleton I.ringCon.Quotient :=
  InfoGeometry.Algebra.CARTwoSidedIdeal.car_quotient_subsingleton atom.toCARPair I hmem

end InfoGeometry.Algebra.CPT.Cl11Atom
