import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi

/-!
# Dirac-Kähler Multiplication Rules (Native Mathlib Formulation)

This file replaces the legacy explicit 32x32 matrix representations and external CAS
calls with the true categorical representation using Mathlib's universal `CliffordAlgebra`.

We define the Cl(5,5) Clifford algebra over ℝ and instantiate the Dirac-Kähler
generators directly from the standard quadratic form.
-/

namespace InfoGeometry.Canonical

open Matrix

noncomputable section

/- **1. The Cl(5,5) Metric Matrix η_AB** -/
def cl55Matrix : Matrix (Fin 10) (Fin 10) ℝ :=
  diagonal (fun i => if i.val < 5 then (1 : ℝ) else (-1 : ℝ))

/- **2. The Quadratic Form for Cl(5,5)** -/
def cl55Metric : QuadraticForm ℝ (Fin 10 → ℝ) :=
  cl55Matrix.toQuadraticMap'

/- **3. The Mathlib Native Clifford Algebra Type** -/
abbrev Cl55 := CliffordAlgebra cl55Metric

/- **4. The 10 Generators Γᴬ** -/
def Gamma (A : Fin 10) : Cl55 :=
  CliffordAlgebra.ι cl55Metric (Pi.single A 1)

/- **5. The True Clifford Relations (derived structurally without CAS)** -/
theorem clifford_relations (A B : Fin 10) :
    Gamma A * Gamma B + Gamma B * Gamma A =
      algebraMap ℝ Cl55 (2 * cl55Matrix A B) := by
  dsimp [Gamma]
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  have hpolar :
      QuadraticMap.polar (⇑cl55Metric) (Pi.single A 1) (Pi.single B 1) =
        2 * cl55Matrix A B := by
    dsimp [cl55Metric, Matrix.toQuadraticMap']
    rw [LinearMap.BilinMap.polar_toQuadraticMap]
    simp [cl55Metric, cl55Matrix, Matrix.toQuadraticMap',
      Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec, Pi.single_apply]
    fin_cases A <;> fin_cases B <;>
      norm_num [Matrix.toLinearMap₂'_apply, dotProduct, Matrix.mulVec,
        Pi.single_apply]
  rw [hpolar]

/- **6. Chirality Operator Γⁱ¹⋯Γ¹⁰ = Γ¹ ⋯ Γ¹⁰** -/
def ChiralityOperator : Cl55 :=
  (List.finRange 10).map Gamma |>.prod

/- **7. Dirac-Kähler symbol: the algebraic part of `D = Γᴬ ∂ᴬ`. -/
abbrev DiracKahlerOperator := Fin 10 → Cl55

namespace DiracKahlerOperator

/-- Compatibility accessor for the native Clifford coefficient family. -/
abbrev coefficients (D : DiracKahlerOperator) : Fin 10 → Cl55 := D

end DiracKahlerOperator

def diracKahlerSymbol (D : DiracKahlerOperator) : Cl55 :=
  ∑ A : Fin 10, Gamma A * D.coefficients A

theorem diracKahlerSymbol_zero :
    diracKahlerSymbol (fun _ => 0) = 0 := by
  simp [diracKahlerSymbol]

theorem diracKahlerSymbol_add (D E : DiracKahlerOperator) :
    diracKahlerSymbol (D + E) =
      diracKahlerSymbol D + diracKahlerSymbol E := by
  simp [diracKahlerSymbol, Finset.sum_add_distrib, mul_add]

theorem diracKahlerSymbol_smul (r : ℝ) (D : DiracKahlerOperator) :
    diracKahlerSymbol (r • D) = r • diracKahlerSymbol D := by
  simp [diracKahlerSymbol, Finset.smul_sum, mul_smul_comm]

/- **8. Algebraic Dirac-Kähler square.**

This is only the square of the finite Clifford symbol.  A Lichnerowicz
identity needs a differential operator, a connection, and curvature data; it
is therefore not asserted by this algebra-only owner.
-/
def DiracKahlerSquare (D : DiracKahlerOperator) : Cl55 :=
  diracKahlerSymbol D * diracKahlerSymbol D

end
end InfoGeometry.Canonical
