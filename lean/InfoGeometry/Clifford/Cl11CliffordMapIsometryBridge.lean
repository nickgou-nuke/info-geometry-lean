import InfoGeometry.Clifford.Cl11Matrix
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The canonical Cl(1,1) Clifford-map bridge

The affine/projective part of the repository is kept separate from the
Clifford fibre.  This owner records the native Mathlib lift of the linear
reflection `(x,y) ↦ (x,-y)`; translations are deliberately not included.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl11Matrix

open scoped Matrix

/-- Reflection of the negative Witt coordinate. -/
def splitReflection : Vec11 ≃ₗ[ℝ] Vec11 where
  toFun v := (v.1, -v.2)
  invFun v := (v.1, -v.2)
  left_inv v := by rcases v with ⟨x, y⟩; simp
  right_inv v := by rcases v with ⟨x, y⟩; simp
  map_add' u v := by
    rcases u with ⟨u₁, u₂⟩
    rcases v with ⟨v₁, v₂⟩
    simp
    ring
  map_smul' c v := by rcases v with ⟨x, y⟩; simp

@[simp] theorem q11_splitReflection (v : Vec11) :
    q11 (splitReflection v) = q11 v := by
  rcases v with ⟨x, y⟩
  simp [splitReflection, q11_apply]

/-- The reflection as a Mathlib quadratic isometry. -/
def splitReflectionIsometry : q11 →qᵢ q11 where
  __ := splitReflection.toLinearMap
  map_app' := q11_splitReflection

/-- The induced algebra homomorphism on the Clifford quotient. -/
noncomputable def splitReflectionCliffordMap :
    CliffordAlgebra q11 →ₐ[ℝ] CliffordAlgebra q11 :=
  CliffordAlgebra.map splitReflectionIsometry

@[simp] theorem splitReflectionCliffordMap_ι (v : Vec11) :
    splitReflectionCliffordMap (CliffordAlgebra.ι q11 v) =
      CliffordAlgebra.ι q11 (splitReflection v) := by
  rw [splitReflectionCliffordMap, CliffordAlgebra.map_apply_ι]
  rfl

@[simp] theorem splitReflectionCliffordMap_pos :
    splitReflectionCliffordMap (CliffordAlgebra.ι q11 (1, 0)) =
      CliffordAlgebra.ι q11 (1, 0) := by
  rw [splitReflectionCliffordMap_ι]
  simp [splitReflection]

@[simp] theorem splitReflectionCliffordMap_neg :
    splitReflectionCliffordMap (CliffordAlgebra.ι q11 (0, 1)) =
      CliffordAlgebra.ι q11 (0, -1) := by
  rw [splitReflectionCliffordMap_ι]
  rfl

end InfoGeometry.Clifford.Cl11Matrix
