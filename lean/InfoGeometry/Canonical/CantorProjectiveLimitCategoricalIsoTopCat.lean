import InfoGeometry.Canonical.CantorProjectiveLimitTopCat
import InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

/-!
# Identifying the two native prefix-limit carriers

The repository contains both a concrete coherent-family carrier and the
categorical `TopCat` limit of the finite-prefix diagram.  They are related by
the same Cantor boundary; this owner records the resulting canonical
topological isomorphism and its projection law.
-/

noncomputable section

namespace InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimit.PrefixProjectiveLimit
open InfoGeometry.Canonical.CantorProjectiveLimitTopCat
open InfoGeometry.Canonical.UHFInductiveColimitBoundaryInverseLimit

def projectiveToCategoricalLimitTopCatIso :
    TopCat.of PrefixProjectiveLimit ≅
      TopCat.of (↑(limit prefixDiagram)) :=
  cantorProjectiveLimitTopCatIso.symm.trans prefixBoundaryLimitIso

theorem projectiveToCategoricalLimit_projection (n : ℕ) :
    projectiveToCategoricalLimitTopCatIso.hom ≫
        limit.π prefixDiagram (Opposite.op n) =
      projectiveProjectionTopCatHom n := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rw [TopCat.comp_app]
  change (limit.π prefixDiagram (Opposite.op n)).hom
      (prefixBoundaryLimitIso.hom (toCantor p)) = π n p
  apply funext
  intro i
  have hproj := prefixBoundaryLimitIso_hom_apply n (toCantor p) i
  have hword := congrFun (boundaryPrefix_toCantor_eq_word p n) i
  simpa [boundaryPrefix] using hproj.trans hword

theorem projectiveToCategoricalLimit_projection_apply
    (n : ℕ) (p : PrefixProjectiveLimit) (i : Fin n) :
    (limit.π prefixDiagram (Opposite.op n)).hom
        (projectiveToCategoricalLimitTopCatIso.hom p) i =
      p.word n i := by
  have h := congrArg (fun f => f p)
    (projectiveToCategoricalLimit_projection n)
  have hi := congrFun h i
  exact hi

end InfoGeometry.Canonical.CantorProjectiveLimitCategoricalIsoTopCat
