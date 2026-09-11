import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinBivectorLinear

/-!
# The canonical Pluecker wedge as a native alternating map

The existing `wedgeVec4` coordinate formula is bundled here as an actual
Mathlib alternating bilinear map.  Its codomain is the now-linear canonical
six-coordinate bivector carrier.  No decomposability converse or projective
quotient is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.FierzKleinFoundation

/-- The coordinate wedge as a bilinear map in its two vector arguments. -/
def wedgeVec4Multilinear :
    MultilinearMap ℝ (fun _ : Fin 2 => Vec4) Bivector4 :=
  MultilinearMap.mk
    (fun v => wedgeVec4 (v 0) (v 1))
    (by
      intro _ v i x y
      fin_cases i <;>
        apply bivector4CoordinateLinearEquiv.injective <;>
        rw [map_add] <;>
        funext j <;>
        fin_cases j <;>
        simp [wedgeVec4] <;>
        ring)
    (by
      intro _ v i r x
      fin_cases i <;>
        apply bivector4CoordinateLinearEquiv.injective <;>
        rw [map_smul] <;>
        funext j <;>
        fin_cases j <;>
        simp [wedgeVec4] <;>
        ring)

/-- The coordinate Pluecker wedge as a genuine alternating bilinear map. -/
def wedgeVec4Alternating : Vec4 [⋀^Fin 2]→ₗ[ℝ] Bivector4 :=
  AlternatingMap.mk wedgeVec4Multilinear (by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change wedgeVec4 (v 0) (v 1) = 0
      have h : v 0 = v 1 := by simpa using hij
      rw [h]
      apply bivector4CoordinateLinearEquiv.injective
      rw [map_zero]
      funext k
      fin_cases k <;> simp [wedgeVec4] <;> ring
    · change wedgeVec4 (v 0) (v 1) = 0
      have h : v 1 = v 0 := by simpa using hij
      rw [h]
      apply bivector4CoordinateLinearEquiv.injective
      rw [map_zero]
      funext k
      fin_cases k <;> simp [wedgeVec4] <;> ring
    · exact (hne rfl).elim)

@[simp] theorem wedgeVec4Alternating_apply (u v : Vec4) :
    wedgeVec4Alternating ![u, v] = wedgeVec4 u v :=
  rfl

/-- Repeated vectors vanish by the universal alternating-map law. -/
@[simp] theorem wedgeVec4Alternating_self (u : Vec4) :
    wedgeVec4Alternating ![u, u] = 0 := by
  exact wedgeVec4Alternating.map_eq_zero_of_eq ![u, u]
    (i := 0) (j := 1) rfl (by decide)

end InfoGeometry.Canonical.FierzKleinFoundation
