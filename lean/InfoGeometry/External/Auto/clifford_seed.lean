import Mathlib.Tactic
open CliffordAlgebra
open QuadraticForm
open QuadraticMap
open Matrix

/-!
# Cl(1,1) ≅ M₂(ℝ) — using mathlib's CliffordAlgebra

The quadratic form Q on ℝ² with signature (1,1): Q(x,y) = x² - y².
Proved using the universal property of the Clifford algebra.
-/

noncomputable section

/-- Signature (1,1) quadratic form on ℝ²: Q(x,y) = x² - y² -/
def Q : QuadraticForm ℝ (ℝ × ℝ) :=
  (QuadraticMap.sq.comp (LinearMap.fst ℝ ℝ ℝ : (ℝ × ℝ) →ₗ[ℝ] ℝ)) -
  (QuadraticMap.sq.comp (LinearMap.snd ℝ ℝ ℝ : (ℝ × ℝ) →ₗ[ℝ] ℝ))

@[simp] lemma Q_apply (x y : ℝ) : Q (x, y) = x*x - y*y := rfl

/-- The matrix generators for Cl(1,1) -/
def σx : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def σy : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

lemma σx_sq : σx * σx = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σx, Matrix.mul_apply, Fin.sum_univ_two]

lemma σy_sq : σy * σy = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σy, Matrix.mul_apply, Fin.sum_univ_two]

/-- The linear map ℝ² → M₂(ℝ) sending e₁↦σx, e₂↦σy -/
def f_lin : (ℝ × ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun := λ ⟨x, y⟩ => x • σx + y • σy
  map_add' := λ ⟨x₁,y₁⟩ ⟨x₂,y₂⟩ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [σx, σy, Matrix.add_apply] <;> ring
  map_smul' := λ r ⟨x,y⟩ => by
    ext i j; fin_cases i <;> fin_cases j <;> simp [σx, σy, Matrix.smul_apply] <;> ring

/-- f satisfies the Clifford condition: f(v)² = algebraMap(Q(v)) -/
lemma f_clifford_cond (v : ℝ × ℝ) : f_lin v * f_lin v = algebraMap ℝ _ (Q v) := by
  rcases v with ⟨x, y⟩
  have h_anti : σx * σy = -(σy * σx) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [σx, σy, Matrix.mul_apply, Fin.sum_univ_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [f_lin, Q_apply, σx, σy, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Algebra.algebraMap_eq_smul_one] <;> ring

/-- The algebra homomorphism Cl(1,1) → M₂(ℝ) from the universal property -/
def cl11_to_M2 : CliffordAlgebra Q →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  CliffordAlgebra.lift Q ⟨f_lin, f_clifford_cond⟩

@[simp] lemma cl11_to_M2_ι (v : ℝ × ℝ) : cl11_to_M2 (ι Q v) = f_lin v :=
  CliffordAlgebra.lift_ι_apply _ _ v

lemma cl11_to_M2_e1 : cl11_to_M2 (ι Q (1, 0)) = σx := by simp [f_lin]
lemma cl11_to_M2_e2 : cl11_to_M2 (ι Q (0, 1)) = σy := by simp [f_lin]

/-- Any 2×2 real matrix is in the span of {I, σx, σy, σx·σy}. -/
theorem M2_basis_decompose (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M = ((M 0 0 + M 1 1)/2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        ((M 0 1 + M 1 0)/2 : ℝ) • σx +
        ((M 0 1 - M 1 0)/2 : ℝ) • σy +
        ((M 1 1 - M 0 0)/2 : ℝ) • (σx * σy) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [σx, σy, Matrix.smul_apply, Matrix.add_apply] <;> ring

#check cl11_to_M2
#check cl11_to_M2_e1
#check cl11_to_M2_e2
#check f_clifford_cond
#check M2_basis_decompose
