import InfoGeometry.Canonical.CantorBoundaryReadoutTopCat
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
import InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat

/-!
# Kernel quotient of the binary Cantor readout

The binary series readout has a canonical quotient by equality of readout
values.  This owner records the resulting `TopCat` map and its injectivity.
It does not identify the quotient with the unit interval: that requires a
separate surjectivity and topology theorem.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat

open CategoryTheory
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryTopology
open InfoGeometry.Canonical.CantorBoundaryFiniteReadout
open InfoGeometry.Canonical.CantorBoundaryReadoutBounds
open InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat

def readoutSetoid : Setoid CantorBoundary where
  r x y := realBinaryReadout x = realBinaryReadout y
  iseqv := {
    refl := fun x => rfl
    symm := fun {x y} h => h.symm
    trans := fun {x y z} hxy hyz => hxy.trans hyz }

abbrev ReadoutQuotient := BoundaryQuotient (A := Bool) readoutSetoid

def quotientMap : CantorBoundary → ReadoutQuotient :=
  boundaryQuotientMap (A := Bool) readoutSetoid

def quotientReadout : ReadoutQuotient → ℝ :=
  InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.quotientReadout
    (A := Bool) readoutSetoid realBinaryReadout (by
      intro x y h
      exact h)

theorem quotientMap_continuous : Continuous quotientMap := by
  exact continuous_boundaryQuotientMap (A := Bool) readoutSetoid

theorem quotientMap_isQuotientMap :
    Topology.IsQuotientMap quotientMap := by
  exact isQuotientMap_boundaryQuotientMap (A := Bool) readoutSetoid

theorem quotientMap_surjective : Function.Surjective quotientMap := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨x, rfl⟩

theorem quotientReadout_continuous : Continuous quotientReadout := by
  exact InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.continuous_quotientReadout
    (A := Bool) readoutSetoid realBinaryReadout
    continuous_realBinaryReadout (by
      intro x y h
      exact h)

@[simp] theorem quotientReadout_comp (x : CantorBoundary) :
    quotientReadout (quotientMap x) = realBinaryReadout x := by
  exact InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.quotientReadout_mk
    (A := Bool) readoutSetoid realBinaryReadout (by
      intro x y h
      exact h) x

theorem quotientMap_eq_iff (x y : CantorBoundary) :
    quotientMap x = quotientMap y ↔
      realBinaryReadout x = realBinaryReadout y := by
  constructor
  · intro h
    simpa using congrArg quotientReadout h
  · intro h
    exact Quotient.sound h

theorem quotientReadout_injective :
    Function.Injective quotientReadout := by
  intro q₁
  refine Quotient.inductionOn q₁ ?_
  intro x q₂
  refine Quotient.inductionOn q₂ ?_
  intro y h
  have hxy : realBinaryReadout x = realBinaryReadout y := by
    simpa [quotientReadout] using h
  apply Quotient.sound
  exact hxy

theorem quotientReadout_eq_iff (q₁ q₂ : ReadoutQuotient) :
    quotientReadout q₁ = quotientReadout q₂ ↔ q₁ = q₂ := by
  constructor
  · intro h
    exact quotientReadout_injective h
  · intro h
    exact congrArg quotientReadout h

theorem quotientReadout_mem_unitInterval (q : ReadoutQuotient) :
    quotientReadout q ∈ Set.Icc (0 : ℝ) 1 := by
  refine Quotient.inductionOn q ?_
  intro x
  simpa [quotientReadout] using
    (realBinaryReadout_mem_unitInterval x)

theorem quotient_compact :
    IsCompact (Set.univ : Set ReadoutQuotient) := by
  have himage : IsCompact (Set.range quotientMap) := by
    have hsource : IsCompact (Set.univ : Set CantorBoundary) := cantorBoundary_compact
    simpa using hsource.image quotientMap_continuous
  rw [Set.range_eq_univ.2 quotientMap_surjective] at himage
  exact himage

noncomputable def quotientReadoutTopCatHom :
    TopCat.of ReadoutQuotient ⟶ TopCat.of ℝ :=
  InfoGeometry.Topology.NaryTreeBoundaryQuotientTopCat.quotientReadoutTopCatHom
    (A := Bool) readoutSetoid realBinaryReadout
    continuous_realBinaryReadout (by
      intro x y h
      exact h)

end InfoGeometry.Canonical.CantorBoundaryReadoutKernelQuotientTopCat
