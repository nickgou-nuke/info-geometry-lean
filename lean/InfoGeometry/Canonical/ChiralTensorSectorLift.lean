import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.TwoSheetThreeColorWeyl

/-!
# Tensor-product realization of the diagonal chiral sector

This owner embeds a three-component family of sheet operators into the
`M₂(ℂ) ⊗ M₃(ℂ)` carrier.  It is a sector embedding, not an assertion that the
three-component Zorn cross product is the multiplication of all of `M₆(ℂ)`.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralTensorSectorLift

abbrev SheetOperator := InfoGeometry.Algebra.FiniteSpin.Mat2C
abbrev TensorOperator := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

def chiralTensorLift (U : Fin 3 → SheetOperator) : TensorOperator :=
  fun (s, i) (t, j) => if i = j then U i s t else 0

def colorDiagonalProjector (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = k ∧ j = k then 1 else 0

def chiralTensorLiftKron (U : Fin 3 → SheetOperator) : TensorOperator :=
  ∑ k : Fin 3, Matrix.kronecker (U k) (colorDiagonalProjector k)

@[simp] theorem chiralTensorLift_apply (U : Fin 3 → SheetOperator)
    (s t : Fin 2) (i j : Fin 3) :
    chiralTensorLift U (s, i) (t, j) = if i = j then U i s t else 0 := by
  rfl

theorem chiralTensorLift_eq_kronecker_sum (U : Fin 3 → SheetOperator) :
    chiralTensorLift U = chiralTensorLiftKron U := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  by_cases hij : i = j
  · subst j
    fin_cases i <;>
      simp [chiralTensorLift, chiralTensorLiftKron, colorDiagonalProjector,
        Matrix.kronecker, Fin.sum_univ_three]
  · fin_cases i <;> fin_cases j <;>
      simp_all [chiralTensorLift, chiralTensorLiftKron,
        colorDiagonalProjector, Matrix.kronecker, Fin.sum_univ_three]

theorem chiralTensorLift_add (U V : Fin 3 → SheetOperator) :
    chiralTensorLift (U + V) = chiralTensorLift U + chiralTensorLift V := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  by_cases h : i = j <;> simp [chiralTensorLift_apply, h]

theorem chiralTensorLift_zero :
    chiralTensorLift (0 : Fin 3 → SheetOperator) = 0 := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  simp [chiralTensorLift_apply]

theorem chiralTensorLift_smul (c : ℂ) (U : Fin 3 → SheetOperator) :
    chiralTensorLift (c • U) = c • chiralTensorLift U := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  by_cases h : i = j <;> simp [chiralTensorLift_apply, h, smul_eq_mul]

theorem chiralTensorLift_injective : Function.Injective chiralTensorLift := by
  intro U V hUV
  funext k
  ext s t
  have hentry := congrArg (fun M : TensorOperator => M (s, k) (t, k)) hUV
  simpa [chiralTensorLift_apply] using hentry

theorem chiralTensorLift_mul (U V : Fin 3 → SheetOperator) :
    chiralTensorLift U * chiralTensorLift V =
      chiralTensorLift (fun k => U k * V k) := by
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [chiralTensorLift, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three]

theorem chiralTensorLift_commutator (U V : Fin 3 → SheetOperator) :
    chiralTensorLift U * chiralTensorLift V -
        chiralTensorLift V * chiralTensorLift U =
      chiralTensorLift (fun k => U k * V k - V k * U k) := by
  rw [chiralTensorLift_mul, chiralTensorLift_mul]
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  by_cases h : i = j <;> simp [chiralTensorLift_apply, h]

theorem chiralTensorLift_anticommutator (U V : Fin 3 → SheetOperator) :
    chiralTensorLift U * chiralTensorLift V +
        chiralTensorLift V * chiralTensorLift U =
      chiralTensorLift (fun k => U k * V k + V k * U k) := by
  rw [chiralTensorLift_mul, chiralTensorLift_mul]
  ext s t
  rcases s with ⟨s, i⟩
  rcases t with ⟨t, j⟩
  by_cases h : i = j <;> simp [chiralTensorLift_apply, h]

end InfoGeometry.Canonical.ChiralTensorSectorLift
