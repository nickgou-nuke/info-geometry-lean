import InfoGeometry.Canonical.CStarAlgebraStateColimit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.CStarCuntzTensorQuotient

/-!
# Cuntz star-inductive-system interface

The algebraic `CuntzAlg` quotient has no C⋆ norm.  This file therefore does not
invent one.  Instead it packages the exact completion data required before
the generic filtered GNS owners can be instantiated: a C⋆ realization at each
finite cutoff, coherent star-algebra transition maps, and preservation of the
old Cuntz generators.

The resulting `ContinuousStarInductiveSystem` is a genuine categorical input;
existence of a particular tower remains an explicit mathematical obligation.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzStarInductiveSystem

open InfoGeometry.Physics.CStarCuntzTensorQuotient
open CStarStateColimit.Native

variable (Stage : ℕ → Type)
variable [∀ n, CStarAlgebra (Stage n)]
variable [∀ n, PartialOrder (Stage n)]
variable [∀ n, StarOrderedRing (Stage n)]

/-- C⋆ realizations of the finite Cuntz stages with coherent embeddings.

The `family` field records the finite Cuntz generators in each realization;
`map_generator` says that an old generator is carried to the corresponding
generator at every later cutoff.  The `Fin.castLE` index transport is the
canonical inclusion of old labels into the larger finite label type.
-/
structure CuntzStarTower where
  family : ∀ n, CStarCuntzFamily (Stage n) (Fin n)
  map : ∀ {m n : ℕ}, m ≤ n → Stage m →⋆ₐ[ℂ] Stage n
  map_id : ∀ n, map (le_refl n) = StarAlgHom.id ℂ (Stage n)
  map_comp :
    ∀ {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k),
      (map hnk).comp (map hmn) = map (le_trans hmn hnk)
  map_generator :
    ∀ {m n : ℕ} (hmn : m ≤ n) (i : Fin m),
      map hmn ((family m).S i) = (family n).S (Fin.castLE hmn i)

namespace CuntzStarTower

variable (T : CuntzStarTower Stage)

/-- The supplied tower is a native Mathlib continuous star-inductive system. -/
def toContinuousStarInductiveSystem :
    ContinuousStarInductiveSystem (I := ℕ) Stage where
  map := T.map
  map_id := T.map_id
  map_comp := T.map_comp

@[simp] theorem toContinuousStarInductiveSystem_map
    {m n : ℕ} (hmn : m ≤ n) (a : Stage m) :
    (T.toContinuousStarInductiveSystem.map hmn) a = T.map hmn a :=
  rfl

@[simp] theorem map_projector
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    T.map hmn ((T.family m).S i * star ((T.family m).S i)) =
      (T.family n).S (Fin.castLE hmn i) *
        star ((T.family n).S (Fin.castLE hmn i)) := by
  rw [map_mul, T.map_generator hmn i, map_star, T.map_generator hmn i]

@[simp] theorem map_generator_star
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    T.map hmn (star ((T.family m).S i)) =
      star ((T.family n).S (Fin.castLE hmn i)) := by
  rw [map_star, T.map_generator hmn i]

theorem transition_generator_projector_compatibility
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    (T.toContinuousStarInductiveSystem.map hmn)
        ((T.family m).S i * star ((T.family m).S i)) =
      (T.family n).S (Fin.castLE hmn i) *
        star ((T.family n).S (Fin.castLE hmn i)) := by
  exact CuntzStarTower.map_projector (Stage := Stage) T hmn i

end CuntzStarTower

end InfoGeometry.Canonical.CuntzStarInductiveSystem
