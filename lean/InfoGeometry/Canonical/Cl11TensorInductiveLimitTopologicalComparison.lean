import InfoGeometry.Canonical.Cl11TensorInductiveLimit
import InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison

/-!
# Tensor-inductive-limit property and topological comparison

This owner connects the concrete `TensorInductiveLimit` packaging of the
`Cl(1,1)` tower with the existing algebraic-to-`TopCat` comparison.  It does
not put a topology on the algebraic direct limit and does not assert a
topological universal property for the property.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalComparison

open InfoGeometry.Canonical.Cl11TensorInductiveLimit
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Clifford.Cl11TensorTowerLimit

@[simp] theorem tensorInductiveLimit_inj_eq_ofStage
    (n : ℕ)
    (A : InfoGeometry.Canonical.Cl11TensorInductiveLimit.Stage n) :
    cl11TensorInductiveLimit.inj n A = ofStage n A := rfl

theorem tensorInductiveLimit_comparison_stage
    (n : ℕ)
    (A : InfoGeometry.Canonical.Cl11TensorInductiveLimit.Stage n) :
    algebraicToTopological
        (cl11TensorInductiveLimit.inj n A) =
      topologicalInjection n A := by
  rw [tensorInductiveLimit_inj_eq_ofStage]
  exact algebraicToTopological_ofStage n A

theorem algebraicToTopological_unique
    (f : InfoGeometry.Canonical.Cl11TensorInductiveLimit.Limit →
      topologicalColimit)
    (hf : ∀ (n : ℕ)
      (A : InfoGeometry.Canonical.Cl11TensorInductiveLimit.Stage n),
      f (ofStage n A) = topologicalInjection n A) :
    f = algebraicToTopological := by
  funext x
  induction x using DirectLimit.induction with
  | _ n A =>
      change f (ofStage n A) = algebraicToTopological (ofStage n A)
      rw [hf n A, algebraicToTopological_ofStage]

end InfoGeometry.Canonical.Cl11TensorInductiveLimitTopologicalComparison
