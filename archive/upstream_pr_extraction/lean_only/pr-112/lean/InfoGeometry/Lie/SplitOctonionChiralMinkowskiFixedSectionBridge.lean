import Mathlib.Tactic
import InfoGeometry.Lie.SplitOctonionCircularWittForm
import InfoGeometry.Quantum.PauliSoldering
import InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge

/-!
# Split-Octonion Chiral Minkowski Fixed-Section and Mirror Bridge

This module formalizes:
1. **Four Witt Pairs in Split-Octonion Geometry**:
   $$X = u_+ e_+ + u_- e_- + \sum_{i=1}^3 (u_i \sigma_i^+ + v_i \sigma_i^-)$$
   with norm $N(X) = u_+ u_- - \sum_{i=1}^3 u_i v_i$.
2. **Chiral Reflection Involution $\kappa$**:
   $$\kappa : (u_+, \mathbf{u}, u_-, \mathbf{v}) \longmapsto (u_-, \mathbf{v}, u_+, \mathbf{u})$$
3. **🏆 THEOREM 1 (Fixed-Section Minkowski Isometry)**:
   $$N(X_{\mathrm{sym}}) = t^2 - (x_1^2 + x_2^2 + x_3^2) = \eta_{1,3}(t, \mathbf{x})$$
4. **🏆 THEOREM 2 (Anti-Fixed Mirror Sector Isometry)**:
   $$N(X_{\mathrm{anti}}) = -(\tau^2 - (y_1^2 + y_2^2 + y_3^2)) = -\eta_{1,3}(\tau, \mathbf{y})$$
5. **🏆 THEOREM 3 (Direct Sum Decomposition $(1,3) \oplus (3,1) \cong (4,4)$)**:
   $$N(X_{\mathrm{sym}} + X_{\mathrm{anti}}) = N(X_{\mathrm{sym}}) + N(X_{\mathrm{anti}})$$
6. **🏆 THEOREM 4 (Pauli Soldering Determinant Commutative Diagram)**:
   $$\det(\operatorname{solder}(t, x_1, x_2, x_3)) = N(X_{\mathrm{sym}})$$
-/

noncomputable section

open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Quantum.PauliSoldering
open InfoGeometry.Lie.SplitOctonionCircularMinkowskiPauliBridge

namespace InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge

abbrev Coord := Fin 8 → ℝ
abbrev Minkowski4 := Fin 4 → ℝ

/-- Split-octonion Witt quadratic form $N(X) = u_+ u_- - (u_1 v_1 + u_2 v_2 + u_3 v_3)$. -/
def wittNorm (x : Coord) : ℝ :=
  x 0 * x 4 - (x 1 * x 5 + x 2 * x 6 + x 3 * x 7)

@[simp] theorem wittNorm_eq_circularWitt (x : Coord) :
    wittNorm x = circularWittQuadratic x :=
  rfl

/-- Chiral reflection involution $\kappa : u_+ \leftrightarrow u_-, \mathbf{u} \leftrightarrow \mathbf{v}$. -/
def kappa (x : Coord) : Coord :=
  ![x 4, x 5, x 6, x 7, x 0, x 1, x 2, x 3]

/-- 🏆 THEOREM 1: $\kappa$ is an involution: $\kappa^2 = I$. -/
theorem kappa_involutive (x : Coord) : kappa (kappa x) = x := by
  ext i
  fin_cases i <;> rfl

/-- Symmetric fixed section vector $X_{\mathrm{sym}} = \frac{1}{2}(x + \kappa(x))$. -/
def symmSection (t : ℝ) (x1 x2 x3 : ℝ) : Coord :=
  ![t, x1, x2, x3, t, x1, x2, x3]

/-- Anti-fixed mirror section vector $X_{\mathrm{anti}} = \frac{1}{2}(x - \kappa(x))$. -/
def antiSection (tau : ℝ) (y1 y2 y3 : ℝ) : Coord :=
  ![tau, y1, y2, y3, -tau, -y1, -y2, -y3]

/-- 🏆 THEOREM 2: $\kappa$ fixes the symmetric section: $\kappa(X_{\mathrm{sym}}) = X_{\mathrm{sym}}$. -/
theorem kappa_fixes_symmSection (t x1 x2 x3 : ℝ) :
    kappa (symmSection t x1 x2 x3) = symmSection t x1 x2 x3 := by
  ext i
  fin_cases i <;> rfl

/-- 🏆 THEOREM 3: $\kappa$ inverts the anti-fixed section: $\kappa(X_{\mathrm{anti}}) = -X_{\mathrm{anti}}$. -/
theorem kappa_inverts_antiSection (tau y1 y2 y3 : ℝ) :
    kappa (antiSection tau y1 y2 y3) = - (antiSection tau y1 y2 y3) := by
  ext i
  fin_cases i <;> simp [kappa, antiSection]

/-- 🏆 THEOREM 4 (Chiral Fixed-Section Minkowski Isometry):
    $$N(X_{\mathrm{sym}}) = t^2 - (x_1^2 + x_2^2 + x_3^2)$$ -/
theorem wittNorm_symmSection (t x1 x2 x3 : ℝ) :
    wittNorm (symmSection t x1 x2 x3) = t^2 - (x1^2 + x2^2 + x3^2) := by
  simp [wittNorm, symmSection]
  ring

/-- 🏆 THEOREM 5 (Anti-Fixed Mirror Sector Isometry):
    $$N(X_{\mathrm{anti}}) = -(\tau^2 - (y_1^2 + y_2^2 + y_3^2))$$ -/
theorem wittNorm_antiSection (tau y1 y2 y3 : ℝ) :
    wittNorm (antiSection tau y1 y2 y3) = - (tau^2 - (y1^2 + y2^2 + y3^2)) := by
  simp [wittNorm, antiSection]
  ring

/-- 🏆 THEOREM 6 (Direct Sum Decomposition $(1,3) \oplus (3,1) = (4,4)$):
    $$N(X_{\mathrm{sym}} + X_{\mathrm{anti}}) = N(X_{\mathrm{sym}}) + N(X_{\mathrm{anti}})$$ -/
theorem wittNorm_direct_sum (t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    wittNorm (symmSection t x1 x2 x3 + antiSection tau y1 y2 y3) =
      (t^2 - (x1^2 + x2^2 + x3^2)) - (tau^2 - (y1^2 + y2^2 + y3^2)) := by
  simp [wittNorm, symmSection, antiSection]
  ring

/-! The symmetric and antisymmetric chiral sectors are orthogonal for the
    polarized circular Witt form. -/
theorem circularPeircePolar_symmSection_antiSection (t x1 x2 x3 tau y1 y2 y3 : ℝ) :
    circularPeircePolar (symmSection t x1 x2 x3)
      (antiSection tau y1 y2 y3) = 0 := by
  simp [circularPeircePolar, symmSection, antiSection]

/-- 🏆 THEOREM 7 (Exact Pauli Soldering Realization):
    $$\det(\operatorname{solder}(t, x_1, x_2, x_3)) = N(X_{\mathrm{sym}})$$ -/
theorem solder_det_eq_wittNorm_symm (t x1 x2 x3 : ℝ) :
    (solder ((t : ℂ), (x1 : ℂ), (x2 : ℂ), (x3 : ℂ))).det =
      (wittNorm (symmSection t x1 x2 x3) : ℂ) := by
  rw [casimir_as_determinant]
  rw [wittNorm_symmSection]
  simp

end InfoGeometry.Lie.SplitOctonionChiralMinkowskiFixedSectionBridge
