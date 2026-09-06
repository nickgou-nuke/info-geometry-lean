import InfoGeometry.Canonical.FierzKleinFoundation

/-!
# Native linear structure on canonical Klein bivector coordinates

`Bivector4` is the repo's six Pluecker-coordinate carrier.  This file gives it
the real vector-space structure transported from `Fin 6 → ℝ`, then exposes the
transport itself as a genuine `LinearEquiv`.

No quadratic, projective, or decomposability claim is stored in the structure.
-/

noncomputable section

namespace InfoGeometry.Canonical.FierzKleinFoundation

@[ext] theorem Bivector4.ext {P Q : Bivector4}
    (h01 : P.p01 = Q.p01) (h02 : P.p02 = Q.p02)
    (h03 : P.p03 = Q.p03) (h12 : P.p12 = Q.p12)
    (h13 : P.p13 = Q.p13) (h23 : P.p23 = Q.p23) : P = Q := by
  cases P
  cases Q
  simp_all

/-- Ordered coordinate equivalence
`(p01,p02,p03,p12,p13,p23)`. -/
def bivector4Coordinates : Bivector4 ≃ (Fin 6 → ℝ) where
  toFun P := ![P.p01, P.p02, P.p03, P.p12, P.p13, P.p23]
  invFun c := ⟨c 0, c 1, c 2, c 3, c 4, c 5⟩
  left_inv P := by cases P; rfl
  right_inv c := by
    funext i
    fin_cases i <;> rfl

noncomputable instance : AddCommGroup Bivector4 :=
  bivector4Coordinates.addCommGroup

noncomputable instance : Module ℝ Bivector4 :=
  bivector4Coordinates.module ℝ

/-- The coordinate transport as an actual real-linear equivalence. -/
def bivector4CoordinateLinearEquiv : Bivector4 ≃ₗ[ℝ] (Fin 6 → ℝ) where
  toFun := bivector4Coordinates
  invFun := bivector4Coordinates.symm
  left_inv := bivector4Coordinates.left_inv
  right_inv := bivector4Coordinates.right_inv
  map_add' P Q := by
    change bivector4Coordinates
      (bivector4Coordinates.symm
        (bivector4Coordinates P + bivector4Coordinates Q)) = _
    exact bivector4Coordinates.apply_symm_apply _
  map_smul' r P := by
    change bivector4Coordinates
      (bivector4Coordinates.symm (r • bivector4Coordinates P)) = _
    exact bivector4Coordinates.apply_symm_apply _

@[simp] theorem bivector4CoordinateLinearEquiv_apply (P : Bivector4) :
    bivector4CoordinateLinearEquiv P =
      ![P.p01, P.p02, P.p03, P.p12, P.p13, P.p23] :=
  rfl

end InfoGeometry.Canonical.FierzKleinFoundation
