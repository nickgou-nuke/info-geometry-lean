import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Four-plane Hadamard coordinates for split octonions

The standard coordinates `(a,x₁,x₂,x₃,b,y₁,y₂,y₃)` are changed to
`(a₊,a₋,x₁₊,x₂₊,x₃₊,x₁₋,x₂₋,x₃₋)` by four independent Hadamard transforms.
This owner transports coordinates only; it does not redefine the native
Cayley--Dickson product.
-/

namespace InfoGeometry.Clifford.SplitOctonionChiralHadamard

noncomputable section

def stdToChiral (v : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![v 0 + v 4, v 0 - v 4,
    v 1 + v 5, v 2 + v 6, v 3 + v 7,
    v 1 - v 5, v 2 - v 6, v 3 - v 7]

def chiralToStd (w : Fin 8 → ℝ) : Fin 8 → ℝ :=
  ![(w 0 + w 1) / 2, (w 2 + w 5) / 2,
    (w 3 + w 6) / 2, (w 4 + w 7) / 2,
    (w 0 - w 1) / 2, (w 2 - w 5) / 2,
    (w 3 - w 6) / 2, (w 4 - w 7) / 2]

theorem stdToChiral_chiralToStd (w : Fin 8 → ℝ) :
    stdToChiral (chiralToStd w) = w := by
  funext i
  fin_cases i <;>
    simp [stdToChiral, chiralToStd] <;> ring

theorem chiralToStd_stdToChiral (v : Fin 8 → ℝ) :
    chiralToStd (stdToChiral v) = v := by
  funext i
  fin_cases i <;>
    simp [stdToChiral, chiralToStd] <;> ring

theorem stdToChiral_injective : Function.Injective stdToChiral := by
  intro v w h
  rw [← chiralToStd_stdToChiral v, ← chiralToStd_stdToChiral w, h]

theorem chiralToStd_injective : Function.Injective chiralToStd := by
  intro v w h
  rw [← stdToChiral_chiralToStd v, ← stdToChiral_chiralToStd w, h]

end
end InfoGeometry.Clifford.SplitOctonionChiralHadamard
