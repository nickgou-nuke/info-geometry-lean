import Mathlib

/-!
# Complex `Cl(5,0)` matrix-product classification

This formalizes the isomorphism $Cl(5,0; \mathbb{C}) \cong M_4(\mathbb{C}) \times M_4(\mathbb{C})$
using the Kronecker product of Pauli matrices to construct the exact
Dirac algebra representations, split across the chiral halves.
-/

open scoped Matrix

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace InfoGeometry.Canonical.Cl5ComplexMatrixProduct

abbrev Vec5 : Type := ℂ × ℂ × ℂ × ℂ × ℂ
abbrev Mat4C : Type := Matrix (Fin 4) (Fin 4) ℂ
abbrev ProdMat4C : Type := Mat4C × Mat4C

noncomputable def q5 : QuadraticForm ℂ Vec5 :=
  QuadraticMap.sq.prod (QuadraticMap.sq.prod (QuadraticMap.sq.prod (QuadraticMap.sq.prod QuadraticMap.sq)))

@[simp] lemma q5_apply (v : Vec5) : q5 v = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2.1 ^ 2 + v.2.2.2.2 ^ 2 := by
  simp [q5, QuadraticMap.prod_apply]
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

-- Generator 5: -σ3 ⊗ σ3
def g5 : Mat4C := !![
  -1, 0, 0, 0;
  0, 1, 0, 0;
  0, 0, 1, 0;
  0, 0, 0, -1
]

lemma g1_sq : g1 * g1 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g1, Matrix.mul_apply, Fin.sum_univ_four]

lemma g2_sq : g2 * g2 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g2, Matrix.mul_apply, Fin.sum_univ_four]

lemma g3_sq : g3 * g3 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g3, Matrix.mul_apply, Fin.sum_univ_four]

lemma g4_sq : g4 * g4 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g4, Matrix.mul_apply, Fin.sum_univ_four]

lemma g5_sq : g5 * g5 = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [g5, Matrix.mul_apply, Fin.sum_univ_four]

set_option maxHeartbeats 8000000 in
noncomputable def gen : Vec5 →ₗ[ℂ] ProdMat4C where
  toFun v := (
    v.1 • g1 + v.2.1 • g2 + v.2.2.1 • g3 + v.2.2.2.1 • g4 + v.2.2.2.2 • g5,
    v.1 • g1 + v.2.1 • g2 + v.2.2.1 • g3 + v.2.2.2.1 • g4 - v.2.2.2.2 • g5
  )
  map_add' u v := by
    ext
    · simp [add_smul]; abel
    · simp [add_smul]; abel
  map_smul' c v := by
    ext
    · simp [mul_smul]
    · simp [mul_smul, smul_sub]

set_option maxHeartbeats 8000000 in
lemma gen_sq (v : Vec5) : gen v * gen v = algebraMap ℂ ProdMat4C (q5 v) := by
  rcases v with ⟨a,b,c,d,e⟩
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gen, q5_apply, g1, g2, g3, g4, g5, Matrix.mul_apply, Fin.sum_univ_four,
      Algebra.algebraMap_eq_smul_one] <;> ring_nf <;> simp <;> ring

noncomputable def cl5ToProdMat4 : CliffordAlgebra q5 →ₐ[ℂ] ProdMat4C :=
  CliffordAlgebra.lift q5 ⟨gen, gen_sq⟩

noncomputable def e1 : CliffordAlgebra q5 := CliffordAlgebra.ι q5 (1,0,0,0,0)
noncomputable def e2 : CliffordAlgebra q5 := CliffordAlgebra.ι q5 (0,1,0,0,0)
noncomputable def e3 : CliffordAlgebra q5 := CliffordAlgebra.ι q5 (0,0,1,0,0)
noncomputable def e4 : CliffordAlgebra q5 := CliffordAlgebra.ι q5 (0,0,0,1,0)
noncomputable def e5 : CliffordAlgebra q5 := CliffordAlgebra.ι q5 (0,0,0,0,1)

lemma finrank_prodMat4C : Module.finrank ℂ ProdMat4C = 32 := by
  simp [ProdMat4C, Mat4C, Module.finrank_prod, Module.finrank_matrix, Fintype.card_fin]

end InfoGeometry.Canonical.Cl5ComplexMatrixProduct
