import InfoGeometry.Spectral.Algebra.ExactCouple
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The homology page of an exact couple

The page is indexed by the source arrow of the incoming differential.  Thus
`DerivedE C pq` is homology in bidegree `shiftK pq`.  This avoids transports:
the boundary map is definitionally `differential pq`.
-/

namespace InfoGeometry.Spectral.Algebra

universe u

namespace ExactCouple

variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ pq : Z2, AddCommGroup (D pq)] [∀ pq : Z2, AddCommGroup (E pq)]
variable [∀ pq : Z2, Module R (D pq)] [∀ pq : Z2, Module R (E pq)]

/-- Reindexing a zero differential along equality of bidegrees preserves zero. -/
theorem differential_cast_eq_zero
    (C : ExactCouple R D E) {pq pq' : Z2}
    (h : pq = pq') (x : E pq)
    (hx : C.differential pq x = 0) :
    C.differential pq' (LinearEquiv.cast (R := R) (M := E) h x) = 0 := by
  cases h
  exact hx

/-- Cycles at the target of the differential originating at `pq`. -/
def targetCycles (C : ExactCouple R D E) (pq : Z2) :
    Submodule R (E (shiftK pq)) :=
  LinearMap.ker (C.differential (shiftK pq))

/-- Boundaries entering the target of the differential originating at `pq`. -/
def targetBoundaries (C : ExactCouple R D E) (pq : Z2) :
    Submodule R (E (shiftK pq)) :=
  LinearMap.range (C.differential pq)

/-- Square-zero implies every incoming boundary is a cycle at the target. -/
theorem targetBoundaries_le_targetCycles
    (C : ExactCouple R D E) (pq : Z2) :
    C.targetBoundaries pq ≤ C.targetCycles pq := by
  change
    LinearMap.range (C.differential pq) ≤
      LinearMap.ker (C.differential (shiftK pq))
  rw [LinearMap.range_le_ker_iff]
  exact C.differential_comp_differential pq

/-- Incoming boundaries regarded as a submodule of the target cycle module. -/
def targetBoundariesInCycles (C : ExactCouple R D E) (pq : Z2) :
    Submodule R (C.targetCycles pq) :=
  (C.targetBoundaries pq).comap (C.targetCycles pq).subtype

/-- Homology in bidegree `shiftK pq`: cycles modulo incoming boundaries. -/
abbrev DerivedE (C : ExactCouple R D E) (pq : Z2) :=
  C.targetCycles pq ⧸ C.targetBoundariesInCycles pq

/-- The class in the derived page represented by an explicit target cycle. -/
def targetCycleClass
    (C : ExactCouple R D E) (pq : Z2)
    (x : E (shiftK pq))
    (hx : C.differential (shiftK pq) x = 0) :
    C.DerivedE pq :=
  Submodule.Quotient.mk ⟨x, hx⟩

/-- Every incoming differential represents zero on the derived page. -/
@[simp]
theorem targetCycleClass_differential_eq_zero
    (C : ExactCouple R D E) (pq : Z2) (x : E pq) :
    C.targetCycleClass pq (C.differential pq x)
        (by
          have h :=
            LinearMap.congr_fun
              (C.differential_comp_differential pq) x
          simpa [LinearMap.comp_apply] using h) =
      0 := by
  apply (Submodule.Quotient.mk_eq_zero _).2
  change C.differential pq x ∈ C.targetBoundaries pq
  exact ⟨x, rfl⟩

/-- Every element of the derived page has a representative target cycle. -/
theorem derivedE_mk_surjective
    (C : ExactCouple R D E) (pq : Z2) :
    Function.Surjective
      (fun x : C.targetCycles pq =>
        (Submodule.Quotient.mk x : C.DerivedE pq)) :=
  fun q => Quotient.mk_surjective q

end ExactCouple

end InfoGeometry.Spectral.Algebra
