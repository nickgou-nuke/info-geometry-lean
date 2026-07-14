import InfoGeometry.SuperMetriplectic.Axioms
import InfoGeometry.Canonical.MoorePenrose
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Meta.Architecture

/-!
# SuperMetriplectic Inverse Bridge

Small theorem-backed bridge from the conservative scalar inverse-shadow packets in
`SuperMetriplectic.Axioms` to the repo-owned inverse predicates in
`Canonical.MoorePenrose` and `Canonical.Drazin`.

This file does not manufacture operatorial inverse kernels from scalar data.
It only certifies that the scalar shadow structures are honest instances of the
same inverse laws on the one-dimensional body lane, and that the hidden block in
`ScalarSchurDrazinBlock` carries those certified scalar shadows.
-/

namespace InverseBridge

open InfoGeometry.Canonical

/--
A scalar Penrose witness is an honest Moore-Penrose inverse witness on `ℝ`.
-/
@[rep_depth transport]
theorem toIsMoorePenroseInverse
    (P : InfoGeometry.SuperMetriplectic.ScalarPenroseInverse) :
    MoorePenrose.IsMoorePenroseInverse P.a P.aPlus := by
  refine MoorePenrose.IsMoorePenroseInverse.mk ?_ ?_ ?_ ?_
  · exact P.aba
  · exact P.bab
  · simp
  · simp

/--
A scalar Drazin witness is an honest Drazin inverse witness on `ℝ`.
-/
@[rep_depth transport]
theorem toIsDrazinInverse
    (D : InfoGeometry.SuperMetriplectic.ScalarDrazinInverse) :
    Drazin.IsDrazinInverse D.a D.aD D.index := by
  exact Drazin.IsDrazinInverse.mk D.commute D.reflexive D.spectral

/--
The hidden scalar block of a `ScalarSchurDrazinBlock` carries a certified
Moore-Penrose shadow witness.
-/
@[rep_depth transport]
theorem hiddenBlock_hasMoorePenroseShadow
    (B : InfoGeometry.SuperMetriplectic.ScalarSchurDrazinBlock) :
    MoorePenrose.IsMoorePenroseInverse B.LΘΘ B.penrose.aPlus := by
  have hP := toIsMoorePenroseInverse B.penrose
  simpa [B.penrose_matches_hidden] using hP

/--
The hidden scalar block of a `ScalarSchurDrazinBlock` carries a certified Drazin
shadow witness.
-/
@[rep_depth transport]
theorem hiddenBlock_hasDrazinShadow
    (B : InfoGeometry.SuperMetriplectic.ScalarSchurDrazinBlock) :
    Drazin.IsDrazinInverse B.LΘΘ B.drazin.aD B.drazin.index := by
  have hD := toIsDrazinInverse B.drazin
  simpa [B.drazin_matches_hidden] using hD

end InverseBridge
