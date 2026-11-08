import InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Pullback interface for para-Kähler two-forms

This owner introduces no map between existing geometric carriers.  It records
the exact theorem available once such a linear map is supplied.
-/

namespace InfoGeometry.Canonical.ParaKahlerPullbackBridge

open InfoGeometry.Canonical.ParaKahlerMaurerCartanQGT

def pullbackParaBerryTwoForm
    {W V : Type*} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V] [Module ℝ V]
    (D : ParaKahlerDatum ℝ V) (f : W →ₗ[ℝ] V) (u v : W) : ℝ :=
  D.paraBerryTwoForm (f u) (f v)

theorem pullbackParaBerryTwoForm_skew
    {W V : Type*} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V] [Module ℝ V]
    (D : ParaKahlerDatum ℝ V) (f : W →ₗ[ℝ] V) (u v : W) :
    pullbackParaBerryTwoForm D f v u =
      -pullbackParaBerryTwoForm D f u v := by
  simpa [pullbackParaBerryTwoForm] using D.paraBerryTwoForm_skew (f u) (f v)

theorem pullbackParaQGT_conjugation
    {W V : Type*} [AddCommGroup W] [Module ℝ W]
    [AddCommGroup V] [Module ℝ V]
    (D : ParaKahlerDatum ℝ V) (f : W →ₗ[ℝ] V) (u v : W) :
    (paraQGT D (f v) (f u)).re = (paraQGT D (f u) (f v)).re ∧
    (paraQGT D (f v) (f u)).ep = -(paraQGT D (f u) (f v)).ep := by
  exact paraQGT_conjugation D (f u) (f v)

end InfoGeometry.Canonical.ParaKahlerPullbackBridge
