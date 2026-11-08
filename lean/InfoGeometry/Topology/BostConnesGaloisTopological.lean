import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BostConnesGalois

/-!
# Topological readout for the Bost--Connes Galois lane

This file packages the algebraic Galois / cyclotomic data of the Bost--Connes
owner as a discrete topological readout.  It does not add new arithmetic
structure; it only records continuity and local constancy of the existing
generator and automorphism maps.
-/

namespace InfoGeometry.Topology.BostConnesGaloisTopological

open InfoGeometry.Canonical.BostConnesGalois

noncomputable section

universe u

variable {C_comm : Type u} [CommRing C_comm] [StarRing C_comm] [Algebra ℂ C_comm]
variable {G : Type u} [GaloisActionData G]

instance commutativeBoundaryAlgebraTopologicalSpace :
    TopologicalSpace C_comm := ⊥

instance commutativeBoundaryAlgebraDiscreteTopology :
    DiscreteTopology C_comm := ⟨rfl⟩

instance rationalTopologicalSpace : TopologicalSpace ℚ := ⊥

instance rationalDiscreteTopology : DiscreteTopology ℚ := ⟨rfl⟩

instance galoisGroupTopologicalSpace : TopologicalSpace G := ⊥

instance galoisGroupDiscreteTopology : DiscreteTopology G := ⟨rfl⟩

instance unitTopologicalSpace : TopologicalSpace ℕ+ := ⊥

instance unitDiscreteTopology : DiscreteTopology ℕ+ := ⟨rfl⟩

/-- The generator representation `e(r)` viewed as a discrete topological map. -/
def topologicalGroupElementRepresentation
    (e_rep : GroupElementRepresentation C_comm) :
    ℚ → C_comm :=
  e_rep.e

@[simp] theorem topologicalGroupElementRepresentation_eq
    (e_rep : GroupElementRepresentation C_comm) :
    topologicalGroupElementRepresentation (C_comm := C_comm) e_rep = e_rep.e := by
  rfl

theorem continuous_topologicalGroupElementRepresentation
    (e_rep : GroupElementRepresentation C_comm) :
    Continuous (topologicalGroupElementRepresentation (C_comm := C_comm) e_rep) := by
  simpa [topologicalGroupElementRepresentation] using
    (continuous_of_discreteTopology :
      Continuous (topologicalGroupElementRepresentation (C_comm := C_comm) e_rep))

theorem isLocallyConstant_topologicalGroupElementRepresentation
    (e_rep : GroupElementRepresentation C_comm) :
    IsLocallyConstant (topologicalGroupElementRepresentation (C_comm := C_comm) e_rep) := by
  simpa [topologicalGroupElementRepresentation] using
    (IsLocallyConstant.of_discrete
      (f := topologicalGroupElementRepresentation (C_comm := C_comm) e_rep))

/-- The semigroup action on boundary generators, viewed as a discrete readout. -/
def topologicalSemigroupAction
    (e_rep : GroupElementRepresentation C_comm)
    (semigroup : SemigroupEndomorphismAction C_comm e_rep) :
    ℕ+ → C_comm → C_comm :=
  semigroup.α

@[simp] theorem topologicalSemigroupAction_eq
    (e_rep : GroupElementRepresentation C_comm)
    (semigroup : SemigroupEndomorphismAction C_comm e_rep) :
    topologicalSemigroupAction (C_comm := C_comm) e_rep semigroup = semigroup.α := by
  rfl

theorem continuous_topologicalSemigroupAction
    (e_rep : GroupElementRepresentation C_comm)
    (semigroup : SemigroupEndomorphismAction C_comm e_rep) :
    Continuous (fun n : ℕ+ =>
      topologicalSemigroupAction (C_comm := C_comm) e_rep semigroup n) := by
  simpa [topologicalSemigroupAction] using
    (continuous_of_discreteTopology :
      Continuous (fun n : ℕ+ =>
        topologicalSemigroupAction (C_comm := C_comm) e_rep semigroup n))

theorem isLocallyConstant_topologicalSemigroupAction
    (e_rep : GroupElementRepresentation C_comm)
    (semigroup : SemigroupEndomorphismAction C_comm e_rep) :
    IsLocallyConstant (fun n : ℕ+ =>
      topologicalSemigroupAction (C_comm := C_comm) e_rep semigroup n) := by
  simpa [topologicalSemigroupAction] using
    (IsLocallyConstant.of_discrete
      (f := fun n : ℕ+ =>
        topologicalSemigroupAction (C_comm := C_comm) e_rep semigroup n))

/-- The Galois action on boundary generators, viewed as a discrete topological readout. -/
def topologicalGaloisGeneratorAction
    (e_rep : GroupElementRepresentation C_comm)
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G)) :
    G → ℚ → C_comm :=
  fun g r => galoisAut.galoisAut g (e_rep.e r)

@[simp] theorem topologicalGaloisGeneratorAction_eq
    (e_rep : GroupElementRepresentation C_comm)
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G)) :
    topologicalGaloisGeneratorAction (C_comm := C_comm) e_rep galoisAut =
      fun g r => galoisAut.galoisAut g (e_rep.e r) := by
  rfl

theorem continuous_topologicalGaloisGeneratorAction
    (e_rep : GroupElementRepresentation C_comm)
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G)) :
    Continuous (fun g : G =>
      topologicalGaloisGeneratorAction (C_comm := C_comm) e_rep galoisAut g) := by
  simpa [topologicalGaloisGeneratorAction] using
    (continuous_of_discreteTopology :
      Continuous (fun g : G =>
        topologicalGaloisGeneratorAction (C_comm := C_comm) e_rep galoisAut g))

theorem isLocallyConstant_topologicalGaloisGeneratorAction
    (e_rep : GroupElementRepresentation C_comm)
    (galoisAut : GaloisAlgebraAutomorphism C_comm e_rep (G := G)) :
    IsLocallyConstant (fun g : G =>
      topologicalGaloisGeneratorAction (C_comm := C_comm) e_rep galoisAut g) := by
  simpa [topologicalGaloisGeneratorAction] using
    (IsLocallyConstant.of_discrete
      (f := fun g : G =>
        topologicalGaloisGeneratorAction (C_comm := C_comm) e_rep galoisAut g))

end
end InfoGeometry.Topology.BostConnesGaloisTopological
