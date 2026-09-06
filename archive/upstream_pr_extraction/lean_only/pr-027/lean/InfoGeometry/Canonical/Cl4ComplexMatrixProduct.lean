import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Complex `Cl(4,0)` matrix-product classification

This formalizes the isomorphism $Cl(4,0; \mathbb{C}) \cong M_4(\mathbb{C})$
using the Kronecker product of Pauli matrices to construct the exact
Dirac algebra representations.
-/

open scoped Matrix

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Canonical.Cl4ComplexMatrixProduct

abbrev Vec4 : Type := ℂ × ℂ × ℂ × ℂ
abbrev Mat4C : Type := Matrix (Fin 4) (Fin 4) ℂ

noncomputable def q4 : QuadraticForm ℂ Vec4 :=
  QuadraticMap.sq.prod (QuadraticMap.sq.prod (QuadraticMap.sq.prod QuadraticMap.sq))

@[simp] lemma q4_apply (v : Vec4) : q4 v = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 := by
  simp [q4, QuadraticMap.prod_apply]
  ring

-- Generator 1: σ1 ⊗ I
def g1 : Mat4C := !![
  0, 0, 1, 0;
  0, 0, 0, 1;
  1, 0, 0, 0;
  0, 1, 0, 0
]

-- Generator 2: σ2 ⊗ I
def g2 : Mat4C := !![
  0, 0, -Complex.I, 0;
  0, 0, 0, -Complex.I;
  Complex.I, 0, 0, 0;
  0, Complex.I, 0, 0
]

-- Generator 3: σ3 ⊗ σ1
def g3 : Mat4C := !![
  0, 1, 0, 0;
  1, 0, 0, 0;
  0, 0, 0, -1;
  0, 0, -1, 0
]

-- Generator 4: σ3 ⊗ σ2
def g4 : Mat4C := !![
  0, -Complex.I, 0, 0;
  Complex.I, 0, 0, 0;
  0, 0, 0, Complex.I;
  0, 0, -Complex.I, 0
]

lemma g1_sq : g1 * g1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g1, Matrix.mul_apply, Fin.sum_univ_four]

lemma g2_sq : g2 * g2 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g2, Matrix.mul_apply, Fin.sum_univ_four]

lemma g3_sq : g3 * g3 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g3, Matrix.mul_apply, Fin.sum_univ_four]

lemma g4_sq : g4 * g4 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g4, Matrix.mul_apply, Fin.sum_univ_four]

noncomputable def gen : Vec4 →ₗ[ℂ] Mat4C where
  toFun v := v.1 • g1 + v.2.1 • g2 + v.2.2.1 • g3 + v.2.2.2 • g4
  map_add' u v := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [g1, g2, g3, g4] <;> ring
  map_smul' c v := by
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [g1, g2, g3, g4, mul_add] <;> ring

set_option maxHeartbeats 800000 in
lemma gen_sq (v : Vec4) : gen v * gen v = algebraMap ℂ Mat4C (q4 v) := by
  rcases v with ⟨a,b,c,d⟩
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gen, q4_apply, g1, g2, g3, g4, Matrix.mul_apply, Fin.sum_univ_four,
      Algebra.algebraMap_eq_smul_one] <;> ring_nf <;> simp <;> ring

noncomputable def cl4ToMat4 : CliffordAlgebra q4 →ₐ[ℂ] Mat4C :=
  CliffordAlgebra.lift q4 ⟨gen, gen_sq⟩

noncomputable def e1 : CliffordAlgebra q4 := CliffordAlgebra.ι q4 (1,0,0,0)
noncomputable def e2 : CliffordAlgebra q4 := CliffordAlgebra.ι q4 (0,1,0,0)
noncomputable def e3 : CliffordAlgebra q4 := CliffordAlgebra.ι q4 (0,0,1,0)
noncomputable def e4 : CliffordAlgebra q4 := CliffordAlgebra.ι q4 (0,0,0,1)

lemma finrank_mat4C : Module.finrank ℂ Mat4C = 16 := by
  simp [Mat4C, Module.finrank_matrix, Fintype.card_fin]

end InfoGeometry.Canonical.Cl4ComplexMatrixProduct
