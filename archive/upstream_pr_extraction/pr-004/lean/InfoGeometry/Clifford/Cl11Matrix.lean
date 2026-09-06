import InfoGeometry.Clifford.SplitQ11

import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading  -- for finrank formula
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic

open scoped Matrix

/-!
# `Cl(1,1)` Matrix Model

Concrete `2 × 2` real-matrix model for `Cl(1,1)`, with explicit generators,
Clifford lift, and a constructive surjectivity witness.  Closes the final
`AlgEquiv` via `finrank`.
-/

namespace InfoGeometry.Clifford.Cl11Matrix

/-- Carrier for split-signature `(1,1)` vectors. -/
abbrev Vec11 : Type := ℝ × ℝ

/-- Real `2 × 2` matrices. -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ

/-- Split quadratic form `(1,1)` on `Vec11`. -/
noncomputable abbrev q11 : QuadraticForm ℝ Vec11 := InfoGeometry.Clifford.splitQ11

/-- Generator squaring to `+1`. -/
def Eplus : Mat2 := !![(1 : ℝ), 0; 0, (-1 : ℝ)]

/-- Generator squaring to `-1`. -/
def Eminus : Mat2 := !![(0 : ℝ), 1; (-1 : ℝ), 0]

/-- Pseudoscalar generator `J₁ = E₊ E₋`. -/
def J1 : Mat2 := Eplus * Eminus

lemma J1_transpose : (J1 : Mat2)ᵀ = J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J1, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

lemma Eplus_sq : Eplus * Eplus = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, Matrix.mul_apply, Fin.sum_univ_two]

lemma Eminus_sq : Eminus * Eminus = (-1 : ℝ) • (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eminus, Matrix.mul_apply, Fin.sum_univ_two]

lemma J1_sq : J1 * J1 = (1 : Mat2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J1, Eplus, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Generator map `(a,b) ↦ a E₊ + b E₋`. -/
noncomputable def gen : Vec11 →ₗ[ℝ] Mat2 where
  toFun v := v.1 • Eplus + v.2 • Eminus
  map_add' := by
    intro u v
    simp [add_smul, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a v
    simp [smul_add, smul_smul, mul_assoc]

@[simp] lemma gen_apply_pair (a b : ℝ) :
    gen (a, b) = a • Eplus + b • Eminus := rfl

/-- Clifford relation needed for `CliffordAlgebra.lift`. -/
lemma gen_sq (v : Vec11) :
    gen v * gen v = (q11 v) • (1 : Mat2) := by
  rcases v with ⟨a, b⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gen, q11, InfoGeometry.Clifford.splitQ11_apply, Eplus, Eminus,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Algebra morphism `Cl(1,1) → Mat₂(ℝ)` induced by `gen`. -/
noncomputable def cl11ToMat : CliffordAlgebra q11 →ₐ[ℝ] Mat2 :=
  CliffordAlgebra.lift q11 gen (by
    intro v
    -- `algebraMap r = r • 1` for matrices
    simpa [Algebra.algebraMap_eq_smul_one] using gen_sq v)

@[simp] lemma cl11ToMat_ι_one_zero :
    cl11ToMat (CliffordAlgebra.ι q11 (1, 0)) = Eplus := by
  simp [cl11ToMat, gen, Eplus, Eminus]

@[simp] lemma cl11ToMat_ι_zero_one :
    cl11ToMat (CliffordAlgebra.ι q11 (0, 1)) = Eminus := by
  simp [cl11ToMat, gen, Eplus, Eminus]

/-- Pseudoscalar element in `Cl(1,1)`. -/
noncomputable def J1_cl : CliffordAlgebra q11 :=
  (CliffordAlgebra.ι q11 (1, 0)) * (CliffordAlgebra.ι q11 (0, 1))

@[simp] lemma cl11ToMat_J1 : cl11ToMat J1_cl = J1 := by
  simp [J1_cl, J1]

/-- Matrix coefficient for identity component. -/
noncomputable def alpha (M : Mat2) : ℝ := (M 0 0 + M 1 1) / 2
/-- Matrix coefficient for `Eplus` component. -/
noncomputable def beta (M : Mat2) : ℝ := (M 0 0 - M 1 1) / 2
/-- Matrix coefficient for `J1` component. -/
noncomputable def delta (M : Mat2) : ℝ := (M 0 1 + M 1 0) / 2
/-- Matrix coefficient for `Eminus` component. -/
noncomputable def gamma (M : Mat2) : ℝ := (M 0 1 - M 1 0) / 2

lemma mat2_decompose (M : Mat2) :
    M = (alpha M) • (1 : Mat2)
      + (beta M) • Eplus
      + (gamma M) • Eminus
      + (delta M) • J1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alpha, beta, gamma, delta, Eplus, Eminus, J1] <;> ring

/-- Constructive preimage for surjectivity. -/
noncomputable def preimage (M : Mat2) : CliffordAlgebra q11 :=
  (alpha M) • (1 : CliffordAlgebra q11)
    + (beta M) • (CliffordAlgebra.ι q11 (1, 0))
    + (gamma M) • (CliffordAlgebra.ι q11 (0, 1))
    + (delta M) • J1_cl

lemma cl11ToMat_preimage (M : Mat2) :
    cl11ToMat (preimage M)
      = (alpha M) • (1 : Mat2)
        + (beta M) • Eplus
        + (gamma M) • Eminus
        + (delta M) • J1 := by
  -- `simp` uses the `[simp]` lemmas for images of generators + J1_cl
  simp [preimage, map_add, map_smul]

lemma cl11ToMat_surjective : Function.Surjective cl11ToMat := by
  intro M
  refine ⟨preimage M, ?_⟩
  calc
    cl11ToMat (preimage M)
        = (alpha M) • (1 : Mat2)
          + (beta M) • Eplus
          + (gamma M) • Eminus
          + (delta M) • J1 := cl11ToMat_preimage M
    _ = M := (mat2_decompose M).symm

/-- `finrank ℝ Mat2 = 4`. -/
lemma finrank_mat2 : finrank ℝ Mat2 = 4 := by
  classical
  simp [Mat2, finrank_matrix]

/-- `finrank ℝ Vec11 = 2`. -/
lemma finrank_vec11 : finrank ℝ Vec11 = 2 := by
  classical
  simp [Vec11, finrank_prod]

/-- `finrank ℝ (CliffordAlgebra q11) = 4` via the standard formula `2^(finrank Vec11)`. -/
lemma finrank_cl11 : finrank ℝ (CliffordAlgebra q11) = 4 := by
  classical
  -- lemma name is stable in current Mathlib: `CliffordAlgebra.finrank`
  have : finrank ℝ (CliffordAlgebra q11) = 2 ^ finrank ℝ Vec11 := by
    simpa using (CliffordAlgebra.finrank (Q := q11) (R := ℝ) (V := Vec11))
  -- 2^(2) = 4
  simpa [finrank_vec11] using this

/-- Surjective + equal finrank ⇒ injective. -/
lemma cl11ToMat_injective : Function.Injective cl11ToMat := by
  classical
  let f : (CliffordAlgebra q11) →ₗ[ℝ] Mat2 := cl11ToMat.toLinearMap
  have hs : Function.Surjective f := by
    intro M
    rcases cl11ToMat_surjective (q11 := q11) M with ⟨x, hx⟩
    exact ⟨x, hx⟩
  have hdim : finrank ℝ (CliffordAlgebra q11) = finrank ℝ Mat2 := by
    simp [finrank_cl11, finrank_mat2]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hs

/-- Final algebra equivalence `Cl(1,1) ≃ₐ[ℝ] M₂(ℝ)`. -/
noncomputable def cl11EquivMat : CliffordAlgebra q11 ≃ₐ[ℝ] Mat2 :=
  AlgEquiv.ofBijective cl11ToMat ⟨cl11ToMat_injective, cl11ToMat_surjective⟩

end InfoGeometry.Clifford.Cl11Matrix
