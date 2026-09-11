import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ZornMatrix

/-!
# Chiral readbacks of the native Zorn multiplication table

This owner adds only generic symmetric identities.  The native multiplication
remains owned by `InfoGeometry.Algebra.ZornMatrix`.
-/

namespace InfoGeometry.Canonical.ZornChiralMultiplicationReadback

noncomputable section

open InfoGeometry.Algebra
open InfoGeometry.Algebra.ZornMatrix

lemma cross_add_swap (v w : Vec3 ℝ) :
    Vec3.cross v w + Vec3.cross w v = ![0, 0, 0] := by
  funext k
  fin_cases k <;> simp [Vec3.cross] <;> ring

theorem U_anticommute (i j : Fin 3) :
    (U i : ZornMatrix ℝ) * U j + U j * U i = 0 := by
  simpa using (InfoGeometry.Algebra.ZornMatrix.U_anticommute (R := ℝ) i j)

theorem V_anticommute (i j : Fin 3) :
    (V i : ZornMatrix ℝ) * V j + V j * V i = 0 := by
  simpa using (InfoGeometry.Algebra.ZornMatrix.V_anticommute (R := ℝ) i j)

theorem U_V_CAR_readback (i j : Fin 3) :
    (U i : ZornMatrix ℝ) * V j + V j * U i =
      if i = j then I else 0 := by
  simpa using (InfoGeometry.Algebra.ZornMatrix.U_V_anticommutator (R := ℝ) i j)

end
end InfoGeometry.Canonical.ZornChiralMultiplicationReadback
