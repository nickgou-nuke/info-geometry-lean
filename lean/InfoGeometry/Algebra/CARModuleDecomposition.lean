import InfoGeometry.Physics.SplitCliffordAlgebras
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# A one-mode CAR representation is a doubled annihilation kernel

The existing `SplitClifford.CARPair` is the input.  No new CAR predicate is
introduced.  The equivalence is explicit: `(x,y) ↦ cre x + y`, where both
coordinates belong to `ker ann`.  The first coordinate is the occupied one.
-/

namespace InfoGeometry.Algebra.CARModuleDecomposition

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (C : SplitClifford.CARPair (Module.End K V))

lemma ann_ann (v : V) : C.ann (C.ann v) = 0 :=
  LinearMap.congr_fun C.ann_sq v

lemma cre_cre (v : V) : C.cre (C.cre v) = 0 :=
  LinearMap.congr_fun C.cre_sq v

lemma resolve (v : V) : C.ann (C.cre v) + C.cre (C.ann v) = v :=
  LinearMap.congr_fun C.anti v

lemma ann_cre_kernel (v : C.ann.ker) : C.ann (C.cre (v : V)) = v := by
  have hv : C.ann (v : V) = 0 := v.property
  simpa only [hv, map_zero, add_zero] using resolve C (v : V)

/-- Explicit linear equivalence, not a dimension-only choice of carrier map. -/
def splitEquiv : (C.ann.ker × C.ann.ker) ≃ₗ[K] V where
  toFun z := C.cre z.1 + z.2
  invFun v := (⟨C.ann v, ann_ann C v⟩,
    ⟨v - C.cre (C.ann v), by
      change C.ann (v - C.cre (C.ann v)) = 0
      rw [map_sub, ann_cre_kernel C ⟨C.ann v, ann_ann C v⟩, sub_self]⟩)
  left_inv z := by
    rcases z with ⟨x,y⟩
    have hy : C.ann (y : V) = 0 := y.property
    have hxy : C.ann (C.cre (x : V) + y) = x := by
      rw [map_add, ann_cre_kernel, hy, add_zero]
    apply Prod.ext
    · apply Subtype.ext
      exact hxy
    · apply Subtype.ext
      change C.cre (x : V) + y - C.cre (C.ann (C.cre (x : V) + y)) = y
      rw [hxy]
      abel
  right_inv v := by
    change C.cre (C.ann v) + (v - C.cre (C.ann v)) = v
    abel
  map_add' x y := by
    change C.cre ((x.1 : V) + y.1) + ((x.2 : V) + y.2) = _
    rw [map_add]
    abel
  map_smul' r z := by
    change C.cre (r • (z.1 : V)) + r • (z.2 : V) = r • (C.cre z.1 + z.2)
    rw [map_smul, smul_add]

@[simp] theorem splitEquiv_apply (x y : C.ann.ker) :
    splitEquiv C (x,y) = C.cre x + y := rfl

/-- Lower block action is the supplied annihilation, with no basis choice. -/
theorem ann_split (x y : C.ann.ker) :
    C.ann (splitEquiv C (x,y)) = splitEquiv C (0,x) := by
  have hy : C.ann (y : V) = 0 := y.property
  simp only [splitEquiv_apply, map_add, ann_cre_kernel, hy, map_zero, add_zero, zero_add]

/-- Upper block action is the supplied creation. -/
theorem cre_split (x y : C.ann.ker) :
    C.cre (splitEquiv C (x,y)) = splitEquiv C (y,0) := by
  simp only [splitEquiv_apply, map_add, cre_cre, zero_add, add_zero]

/-- Dimension is derived from the CAR equations, not assumed. -/
theorem finrank_twice_kernel [FiniteDimensional K V] :
    Module.finrank K V = Module.finrank K C.ann.ker + Module.finrank K C.ann.ker := by
  have h := (splitEquiv C).finrank_eq
  rw [Module.finrank_prod] at h
  exact h.symm

end InfoGeometry.Algebra.CARModuleDecomposition
