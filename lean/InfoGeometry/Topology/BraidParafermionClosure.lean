import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.AharonovBohmVortices
import InfoGeometry.Topology.ParafermionBraiding

/-!
# Braid parafermion finite closure

\[
\mathrm{blockEmbed2x2}(AB)=\mathrm{blockEmbed2x2}(A)\,\mathrm{blockEmbed2x2}(B),
\qquad
\sigma_1\sigma_2\sigma_1=\sigma_2\sigma_1\sigma_2,
\qquad
3z_3=0,
\quad z_3\neq 0.
\]

\[
\mathrm{finite\_braid\_parafermion\_closure}(t)
:
\big(\sigma_1\sigma_2\sigma_1=\sigma_2\sigma_1\sigma_2\big)
\wedge (3z_3=0)\wedge (z_3\neq 0).
\]

\[
\mathrm{finite\_braid\_vortex\_closure}(t,v)
:
\big(\sigma_1\sigma_2\sigma_1=\sigma_2\sigma_1\sigma_2\big)
\wedge (v^3=1).
\]
-/

noncomputable section

namespace InfoGeometry.Topology.BraidParafermionClosure

open Matrix
open InfoGeometry.Topology.Parafermion

/-- `M_{2\times2}\hookrightarrow M_{3\times3}`. -/
abbrev Mat2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

/-- `M_{3\times3}`. -/
abbrev Mat3C := InfoGeometry.Algebra.FiniteSpin.Mat3C

/-- `M_{2\times2}\to M_{3\times3}`. -/
def blockEmbed2x2 (A : Mat2C) : Mat3C :=
  ![![A 0 0, A 0 1, 0],
    ![A 1 0, A 1 1, 0],
    ![0,     0,     1]]

/-- `\mathrm{blockEmbed2x2}(AB)=\mathrm{blockEmbed2x2}(A)\,\mathrm{blockEmbed2x2}(B)`. -/
theorem blockEmbed2x2_mul (A B : Mat2C) :
    blockEmbed2x2 (A * B) = blockEmbed2x2 A * blockEmbed2x2 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockEmbed2x2, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

/-- `z_3:=1\in\mathbb Z/3\mathbb Z`. -/
def z3Unit : ZMod 3 := 1

/-- `3z_3=0`. -/
theorem z3Unit_three_windings :
    z3Unit + z3Unit + z3Unit = 0 := by
  decide

/-- `z_3\neq 0`. -/
theorem z3Unit_nonzero :
    z3Unit ≠ 0 := by
  decide

/-- `(\mathrm{Artin})\wedge(3z_3=0)\wedge(z_3\neq 0)`. -/
theorem finite_braid_parafermion_closure (t : ℂ) :
    sigma_1 t * sigma_2 t * sigma_1 t = sigma_2 t * sigma_1 t * sigma_2 t ∧
      z3Unit + z3Unit + z3Unit = 0 ∧
        z3Unit ≠ 0 := by
  exact ⟨su3_parafermion_braiding t, z3Unit_three_windings, z3Unit_nonzero⟩

/-- `(\mathrm{Artin})\wedge(v^3=1)`. -/
theorem finite_braid_vortex_closure (t : ℂ) (v : AharonovBohmVortex) :
    sigma_1 t * sigma_2 t * sigma_1 t = sigma_2 t * sigma_1 t * sigma_2 t ∧
      vortexOperator v * vortexOperator v * vortexOperator v = 1 := by
  exact ⟨su3_parafermion_braiding t, vortexOperator_cube_eq_one v⟩

end InfoGeometry.Topology.BraidParafermionClosure

end noncomputable section
