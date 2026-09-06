import InfoGeometry.Jordan.Core
import InfoGeometry.Jordan.SPD

/-!
# Core Jordan

Core façade for Jordan algebra structures and SPD matrices.
-/

namespace InfoGeometry.Core

abbrev JordanAlgebra := InfoGeometry.Jordan.JordanAlgebra
abbrev SPD := InfoGeometry.Jordan.SPD

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
