import InfoGeometry.Krein.KreinSpace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A fixed Krein-skew flow preserves its quadratic form

The conservation law follows by differentiation using the existing Krein
adjoint. A differentiable orbit of such a generator cannot enter the null cone
from a non-null initial state. This asserts no existence of an orbit or
equivalence with the Navier--Stokes equation.
-/

noncomputable section

namespace InfoGeometry.Canonical.KreinFlowConservation

open InfoGeometry.Krein InfoGeometry.Krein.KreinSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [KreinSpace H]

theorem hasDerivAt_krein_square {x : ℝ → H} {A : H →L[ℝ] H} {t : ℝ}
    (hx : HasDerivAt x (A (x t)) t) (hA : IsKreinSkewAdjoint A) :
    HasDerivAt (fun r => kreinInner (x r) (x r)) 0 t := by
  have hJ := (jCLM (H := H)).hasFDerivAt.comp_hasDerivAt t hx
  have h := hJ.inner ℝ hx
  have hz := (isKreinSkewAdjoint_iff A).mp hA (x t) (x t)
  change kreinInner (A (x t)) (x t) + kreinInner (x t) (A (x t)) = 0 at hz
  convert h using 1
  simpa only [Function.comp_def, kreinInner_def, jCLM_apply, add_comm] using hz.symm

/-- Time dependence of the generator is allowed; the Krein metric is fixed. -/
theorem krein_square_conserved {x : ℝ → H} {A : ℝ → H →L[ℝ] H}
    (hx : ∀ t, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t, IsKreinSkewAdjoint (A t)) (t s : ℝ) :
    kreinInner (x t) (x t) = kreinInner (x s) (x s) := by
  have hd := fun r => hasDerivAt_krein_square (hx r) (hA r)
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t s

/-- A preserved nonzero quadratic value cannot become zero at a later time. -/
theorem nonnull_preserved {x : ℝ → H} {A : ℝ → H →L[ℝ] H}
    (hx : ∀ t, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t, IsKreinSkewAdjoint (A t)) {s : ℝ}
    (hs : kreinInner (x s) (x s) ≠ 0) (t : ℝ) :
    kreinInner (x t) (x t) ≠ 0 := by
  rwa [krein_square_conserved hx hA t s]

end InfoGeometry.Canonical.KreinFlowConservation
