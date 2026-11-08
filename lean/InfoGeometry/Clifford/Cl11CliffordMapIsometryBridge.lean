/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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

/-- The same quadratic symmetry packaged as an isometric equivalence, so it
can induce an automorphism rather than only an endomorphism. -/
def splitReflectionIsometryEquiv : q11.IsometryEquiv q11 where
  toLinearEquiv := splitReflection
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

/-- The linear glide reflection induces an algebra automorphism of the
Clifford fibre. The affine translation is not part of this fibre map. -/
noncomputable def splitReflectionCliffordAuto :
    CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11 :=
  CliffordAlgebra.equivOfIsometry splitReflectionIsometryEquiv

@[simp] theorem splitReflectionCliffordAuto_ι (v : Vec11) :
    splitReflectionCliffordAuto (CliffordAlgebra.ι q11 v) =
      CliffordAlgebra.ι q11 (splitReflection v) := by
  change CliffordAlgebra.map splitReflectionIsometryEquiv.toIsometry
      (CliffordAlgebra.ι q11 v) = _
  rw [CliffordAlgebra.map_apply_ι]
  rfl

/-- The fibre automorphism is involutive, matching the square of the linear
reflection (not the square of the affine glide). -/
theorem splitReflectionCliffordAuto_involutive :
    splitReflectionCliffordAuto.trans splitReflectionCliffordAuto =
      AlgEquiv.refl := by
  rw [splitReflectionCliffordAuto, CliffordAlgebra.equivOfIsometry_trans]
  have h : splitReflectionIsometryEquiv.trans splitReflectionIsometryEquiv =
      QuadraticMap.IsometryEquiv.refl q11 := by
    apply DFunLike.coe_injective
    funext v
    change splitReflection (splitReflection v) = v
    rcases v with ⟨x, y⟩
    simp [splitReflection]
  rw [h, CliffordAlgebra.equivOfIsometry_refl]

/-- Reflection of the positive coordinate in the split plane. This is the
distinct `(-x,y)` convention used by
`KleinBottleExteriorOrientationBridge.glideLinear`; the existing
`splitReflection` is `(x,-y)`. -/
def splitReflectionFirstCoordinate : Vec11 ≃ₗ[ℝ] Vec11 where
  toFun v := (-v.1, v.2)
  invFun v := (-v.1, v.2)
  left_inv v := by rcases v with ⟨x, y⟩; simp
  right_inv v := by rcases v with ⟨x, y⟩; simp
  map_add' u v := by
    rcases u with ⟨u₁, u₂⟩
    rcases v with ⟨v₁, v₂⟩
    apply Prod.ext
    · simp
      ring
    · rfl
  map_smul' c v := by rcases v with ⟨x, y⟩; ext <;> simp

@[simp] theorem q11_splitReflectionFirstCoordinate (v : Vec11) :
    q11 (splitReflectionFirstCoordinate v) = q11 v := by
  rcases v with ⟨x, y⟩
  simp [splitReflectionFirstCoordinate, q11_apply]

/-- The first-coordinate reflection as an isometric equivalence of the
canonical split quadratic form. -/
def splitReflectionFirstCoordinateIsometryEquiv : q11.IsometryEquiv q11 where
  toLinearEquiv := splitReflectionFirstCoordinate
  map_app' := q11_splitReflectionFirstCoordinate

/-- The first-coordinate reflection induces its native automorphism on the
`Cl(1,1)` Clifford algebra. -/
noncomputable def splitReflectionFirstCoordinateCliffordAuto :
    CliffordAlgebra q11 ≃ₐ[ℝ] CliffordAlgebra q11 :=
  CliffordAlgebra.equivOfIsometry splitReflectionFirstCoordinateIsometryEquiv

@[simp] theorem splitReflectionFirstCoordinateCliffordAuto_ι (v : Vec11) :
    splitReflectionFirstCoordinateCliffordAuto (CliffordAlgebra.ι q11 v) =
      CliffordAlgebra.ι q11 (splitReflectionFirstCoordinate v) := by
  change CliffordAlgebra.map
      splitReflectionFirstCoordinateIsometryEquiv.toIsometry
      (CliffordAlgebra.ι q11 v) = _
  rw [CliffordAlgebra.map_apply_ι]
  rfl

/-- The first-coordinate Clifford reflection squares to the identity. -/
theorem splitReflectionFirstCoordinateCliffordAuto_involutive :
    splitReflectionFirstCoordinateCliffordAuto.trans
        splitReflectionFirstCoordinateCliffordAuto = AlgEquiv.refl := by
  rw [splitReflectionFirstCoordinateCliffordAuto,
    CliffordAlgebra.equivOfIsometry_trans]
  have h :
      splitReflectionFirstCoordinateIsometryEquiv.trans
          splitReflectionFirstCoordinateIsometryEquiv =
        QuadraticMap.IsometryEquiv.refl q11 := by
    apply DFunLike.coe_injective
    funext v
    change splitReflectionFirstCoordinate
        (splitReflectionFirstCoordinate v) = v
    rcases v with ⟨x, y⟩
    simp [splitReflectionFirstCoordinate]
  rw [h, CliffordAlgebra.equivOfIsometry_refl]

end InfoGeometry.Clifford.Cl11Matrix
