import InfoGeometry.Canonical.FilteredCompatibleOperatorColimit
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import Mathlib.Topology.Algebra.LinearMapCompletion

set_option synthInstance.maxHeartbeats 80000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

noncomputable section

namespace InfoGeometry.Canonical.NoncommutativeStarDirectLimit

open InfoGeometry.Canonical.FilteredCompatibleOperatorColimit

universe u v

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I] [DecidableEq I]
variable {A : I → Type u} [∀ i, Ring (A i)] [∀ i, StarRing (A i)] [∀ i, Algebra ℂ (A i)]
variable [∀ i, StarModule ℂ (A i)]

/-- A directed system of ℂ-star-algebras over a directed index set I. -/
structure StarAlgebraDirectedSystem where
  map : ∀ {i j : I}, i ≤ j → A i →ₐ[ℂ] A j
  map_self : ∀ (i : I) (x : A i), map (le_refl i) x = x
  map_trans : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : A i),
    map (le_trans hij hjk) x = map hjk (map hij x)
  map_star : ∀ {i j : I} (hij : i ≤ j) (x : A i),
    map hij (star x) = star (map hij x)

variable (sys : StarAlgebraDirectedSystem (I := I) (A := A))

/-- Stagewise Star-Algebra Homomorphism Family into a Target Star-Algebra B. -/
structure CompatibleStarHomFamily (B : Type v) [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] where
  hom : ∀ i, A i →ₐ[ℂ] B
  intertwines : ∀ {i j : I} (hij : i ≤ j) (x : A i),
    hom j (sys.map hij x) = hom i x
  hom_star : ∀ (i : I) (x : A i),
    hom i (star x) = star (hom i x)

namespace UniversalProperty

/-- **Theorem**: Universal Cocone Intertwining:
    For any compatible star-algebra homomorphism family into B,
    the representation of an evolved element matches the initial stage representation. -/
theorem compatible_hom_intertwine
    {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (F : CompatibleStarHomFamily sys B) {i j : I} (hij : i ≤ j) (x : A i) :
    F.hom j (sys.map hij x) = F.hom i x :=
  F.intertwines hij x

/-- **Theorem**: Star-Involution Intertwining:
    The target representation preserves the star-involution at every stage. -/
theorem compatible_hom_star
    {B : Type v} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (F : CompatibleStarHomFamily sys B) (i : I) (x : A i) :
    F.hom i (star x) = star (F.hom i x) :=
  F.hom_star i x

end UniversalProperty

end InfoGeometry.Canonical.NoncommutativeStarDirectLimit
