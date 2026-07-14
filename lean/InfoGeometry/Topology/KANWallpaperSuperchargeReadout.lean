import InfoGeometry.Topology.KANWallpaperIsomorphism
import InfoGeometry.Algebra.FiniteInductiveSUSY

/-!
# KAN wallpaper supercharge readout

This module gives the smallest honest bridge from the finite KAN-wallpaper
matrix model to the repository's existing super-anticommutator surface.

It does **not** prove physical supersymmetry, a Cuntz-algebra realization,
black-hole physics, or a crystallographic origin theorem for the full SUSY
program. It only proves that in the concrete `3 × 3` projective matrix model,
the self-anticommutator of the glide matrix reads back as twice the translation
matrix.

#### BUCKET 1: CLOSED FINITE THEOREMS

* `glide_self_anticomm_eq_double_translation`
* `glide_self_anticomm_eq_two_nsmul_translation`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

None.

#### BUCKET 3: OPEN CLOSURE DEBT

* no Cuntz-algebra realization;
* no supercharge representation theorem on a boundary algebra;
* no physical SUSY interpretation theorem;
* no event-horizon or holography theorem.
-/

noncomputable section

namespace KANWallpaperSuperchargeReadout

open InfoGeometry.Topology.KANWallpaper
open InfoGeometry.Algebra.FiniteInductiveSUSY

/--
In the finite projective matrix model, the glide matrix has self-anticommutator
`T_x + T_x`.
-/
theorem glide_self_anticomm_eq_double_translation :
    anticomm G G = T_x + T_x := by
  simp [anticomm, glide_squared_is_translation]

/--
Equivalent additive readout of the self-anticommutator as two copies of the
translation matrix.
-/
theorem glide_self_anticomm_eq_two_nsmul_translation :
    anticomm G G = 2 • T_x := by
  rw [glide_self_anticomm_eq_double_translation]
  simp [two_mul]

end KANWallpaperSuperchargeReadout

end noncomputable section
