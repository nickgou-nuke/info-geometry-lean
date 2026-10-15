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

namespace ExactCoupleMap

variable {R : Type u} [Ring R]
variable {D E D' E' : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, AddCommGroup (D' pq)] [∀ pq, AddCommGroup (E' pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]
variable [∀ pq, Module R (D' pq)] [∀ pq, Module R (E' pq)]
variable {C : ExactCouple R D E} {C' : ExactCouple R D' E'}

/-- The component map on cycles of the derived page. -/
def targetCyclesMap (f : ExactCoupleMap R C C') (pq : Z2) :
    C.targetCycles pq →ₗ[R] C'.targetCycles pq where
  toFun x := by
    refine ⟨f.eMap (shiftK pq) x.1, ?_⟩
    have hx : C.differential (shiftK pq) x.1 = 0 := x.2
    have h := f.map_differential (shiftK pq) x.1
    rw [hx, map_zero] at h
    exact h.symm
  map_add' x y := by
    apply Subtype.ext
    exact map_add (f.eMap (shiftK pq)) x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact map_smul (f.eMap (shiftK pq)) r x.1

/-- The derived-page map induced by an exact-couple diagram map. -/
noncomputable def derivedEMap (f : ExactCoupleMap R C C') (pq : Z2) :
    C.DerivedE pq →ₗ[R] C'.DerivedE pq :=
  (Submodule.mapQ
    (C.targetBoundariesInCycles pq)
    (C'.targetBoundariesInCycles pq)
    (f.targetCyclesMap pq)
    (by
      intro x hx
      change (C.targetCycles pq).subtype x ∈ C.targetBoundaries pq at hx
      rcases hx with ⟨y, hy⟩
      change f.eMap (shiftK pq) x.1 ∈ C'.targetBoundaries pq
      refine ⟨f.eMap pq y, ?_⟩
      rw [← f.map_differential pq y, hy]
      rfl))

@[simp]
theorem derivedEMap_targetCycleClass
    (f : ExactCoupleMap R C C') (pq : Z2)
    (x : E (shiftK pq)) (hx : C.differential (shiftK pq) x = 0) :
    f.derivedEMap pq (C.targetCycleClass pq x hx) =
      C'.targetCycleClass pq (f.eMap (shiftK pq) x)
        (by
          have h := f.map_differential (shiftK pq) x
          rw [hx, map_zero] at h
          exact h.symm) := by
  simp [derivedEMap, targetCyclesMap, ExactCouple.targetCycleClass]

end ExactCoupleMap

end InfoGeometry.Spectral.Algebra
