import InfoGeometry.Jordan.Core
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Jordan.SPD

/-!
# Core Jordan

Core façade for Jordan algebra structures and SPD matrices.
-/

namespace InfoGeometry.Core

abbrev JordanAlgebra := InfoGeometry.Jordan.JordanAlgebra
abbrev SPD := InfoGeometry.Jordan.SPD

section JordanAlgebra

open scoped InfoGeometryJordan

variable {V : Type _} [AddCommGroup V] [Module ℝ V] [JordanAlgebra V]

@[simp] lemma jordan_prod_comm (x y : V) : x ⊙ y = y ⊙ x :=
  InfoGeometry.Jordan.jordanProd_comm x y

@[simp] lemma jordan_prod_add_left (x y z : V) :
    (x + y) ⊙ z = x ⊙ z + y ⊙ z :=
  InfoGeometry.Jordan.jordanProd_add_left x y z

@[simp] lemma jordan_prod_add_right (x y z : V) :
    x ⊙ (y + z) = x ⊙ y + x ⊙ z :=
  InfoGeometry.Jordan.jordanProd_add_right x y z

@[simp] lemma jordan_prod_smul_left (a : ℝ) (x y : V) :
    (a • x) ⊙ y = a • (x ⊙ y) :=
  InfoGeometry.Jordan.jordanProd_smul_left a x y

@[simp] lemma jordan_prod_smul_right (a : ℝ) (x y : V) :
    x ⊙ (a • y) = a • (x ⊙ y) :=
  InfoGeometry.Jordan.jordanProd_smul_right a x y

lemma jordan_prod_identity (x y : V) :
    (x ⊙ x) ⊙ (x ⊙ y) = x ⊙ ((x ⊙ x) ⊙ y) :=
  InfoGeometry.Jordan.jordanProd_identity x y

end JordanAlgebra

section SPD

open InfoGeometry.Jordan

variable {n : ℕ} (A : SPD n)

@[simp] lemma spd_transpose_eq_self :
    Matrix.transpose A.mat = A.mat :=
  SPD.transpose_eq_self A

lemma spd_pos_def : A.mat.PosDef :=
  SPD.posDef A

/-- Backward-compatible alias. Prefer `spd_transpose_eq_self`. -/
lemma SPD_transpose_eq_self :
    Matrix.transpose A.mat = A.mat :=
  spd_transpose_eq_self A

/-- Backward-compatible alias. Prefer `spd_pos_def`. -/
lemma SPD_posDef : A.mat.PosDef :=
  spd_pos_def A

end SPD

end InfoGeometry.Core
