import InfoGeometry.Canonical.HeckeBraidTopologicalBridge
import InfoGeometry.Physics.JonesBraidB3

/-!
# Topological transport of the explicit Jones `B₃` representation

The finite 8-by-8 Jones owner already proves the Artin relation for its
Temperley--Lieb generators.  This file exposes the same operators as
continuous endomorphisms of their noncommutative matrix carrier.  It adds no
new matrix identity and makes no continuum claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.JonesBraidB3TopologicalBridge

open CategoryTheory
open InfoGeometry.Canonical.HeckeBraidTopologicalBridge
open InfoGeometry.Physics.JonesBraidB3

abbrev JonesCarrier : Type := Matrix (Fin 8) (Fin 8) ℂ

variable [TopologicalSpace JonesCarrier] [ContinuousMul JonesCarrier]

/-- Topological left action of the first explicit Jones braid generator. -/
def s0LeftTopCatHom : TopCat.of JonesCarrier ⟶ TopCat.of JonesCarrier :=
  leftMulTopCatHom s0

/-- Topological left action of the second explicit Jones braid generator. -/
def s1LeftTopCatHom : TopCat.of JonesCarrier ⟶ TopCat.of JonesCarrier :=
  leftMulTopCatHom s1

@[simp] theorem s0LeftTopCatHom_apply (x : JonesCarrier) :
    s0LeftTopCatHom x = s0 * x :=
  rfl

@[simp] theorem s1LeftTopCatHom_apply (x : JonesCarrier) :
    s1LeftTopCatHom x = s1 * x :=
  rfl

/-- The explicit 8-dimensional Jones representation satisfies the Artin
relation after passage to continuous maps. -/
theorem artin_braid_relation_topological :
    s0LeftTopCatHom ≫ s1LeftTopCatHom ≫ s0LeftTopCatHom =
      s1LeftTopCatHom ≫ s0LeftTopCatHom ≫ s1LeftTopCatHom := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change s0 * (s1 * (s0 * x)) = s1 * (s0 * (s1 * x))
  simpa only [mul_assoc] using
    congrArg (fun z : JonesCarrier => z * x) artin_braid_relation

/-- The topological braid relation is the image of the finite algebraic one,
not an independent postulate. -/
theorem artin_braid_relation_topological_factorization :
    s0LeftTopCatHom ≫ s1LeftTopCatHom ≫ s0LeftTopCatHom =
      leftMulTopCatHom (s0 * s1 * s0) ∧
    s1LeftTopCatHom ≫ s0LeftTopCatHom ≫ s1LeftTopCatHom =
      leftMulTopCatHom (s1 * s0 * s1) := by
  constructor <;>
    dsimp [s0LeftTopCatHom, s1LeftTopCatHom] <;>
    rw [leftMulTopCatHom_comp, leftMulTopCatHom_comp]

end InfoGeometry.Canonical.JonesBraidB3TopologicalBridge
