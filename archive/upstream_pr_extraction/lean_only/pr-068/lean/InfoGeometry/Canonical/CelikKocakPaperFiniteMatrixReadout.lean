import InfoGeometry.Canonical.CelikKocakPaperAllDepthClosure

/-!
# Finite matrix readout of the Çelik--Koçak paper generators

The endpoint basis turns the finite operator representation into matrices.
This file deliberately keeps the two generator families indexed by `Fin n`;
it does not claim the full tensor-product matrix isomorphism.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open FunctionSpace

abbrev EndpointMatrix (n : ℕ) :=
  Matrix (((Fin n) → Bool)) (((Fin n) → Bool)) ℂ

abbrev EndpointOperator (n : ℕ) :=
  (((Fin n) → Bool) → ℂ) →ₗ[ℂ] (((Fin n) → Bool) → ℂ)

noncomputable def endpointMatrixAlgEquiv (n : ℕ) :
    EndpointMatrix n ≃ₐ[ℂ] EndpointOperator n :=
  Matrix.toLinAlgEquiv (endpointBasis (n := n))

@[simp] theorem endpointMatrixAlgEquiv_apply
    {n : ℕ} (A : EndpointMatrix n) :
    endpointMatrixAlgEquiv n A = Matrix.toLin' A := by
  rfl

theorem endpointMatrixAlgEquiv_injective (n : ℕ) :
    Function.Injective (endpointMatrixAlgEquiv n) :=
  (endpointMatrixAlgEquiv n).injective

theorem endpointMatrixAlgEquiv_surjective (n : ℕ) :
    Function.Surjective (endpointMatrixAlgEquiv n) :=
  (endpointMatrixAlgEquiv n).surjective

noncomputable def paperOddMatrix {n : ℕ} (j : Fin n) : EndpointMatrix n :=
  LinearMap.toMatrix (endpointBasis (n := n)) (endpointBasis (n := n))
    (paperOddGenerator (n := n) j.val j.isLt)

noncomputable def paperEvenMatrix {n : ℕ} (j : Fin n) : EndpointMatrix n :=
  LinearMap.toMatrix (endpointBasis (n := n)) (endpointBasis (n := n))
    (paperEvenGenerator (n := n) j.val j.isLt)

@[simp] theorem paperOddMatrix_sq {n : ℕ} (j : Fin n) :
    paperOddMatrix j * paperOddMatrix j = 1 := by
  simp only [paperOddMatrix]
  rw [← LinearMap.toMatrix_mul]
  rw [paperOddGenerator_sq]
  simp [paperOddMatrix, LinearMap.toMatrix_one]

@[simp] theorem paperEvenMatrix_sq {n : ℕ} (j : Fin n) :
    paperEvenMatrix j * paperEvenMatrix j = 1 := by
  simp only [paperEvenMatrix]
  rw [← LinearMap.toMatrix_mul]
  rw [paperEvenGenerator_sq]
  simp [paperEvenMatrix, LinearMap.toMatrix_one]

theorem paperOddMatrix_anticomm_paperEvenMatrix {n : ℕ} (j : Fin n) :
    paperOddMatrix j * paperEvenMatrix j =
      -(paperEvenMatrix j * paperOddMatrix j) := by
  simp only [paperOddMatrix, paperEvenMatrix]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  rw [paperOddGenerator_anticomm_paperEvenGenerator]
  simp [paperOddMatrix, paperEvenMatrix]

theorem paperOddMatrix_anticomm_of_lt {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i < j) :
    paperOddMatrix (⟨i, hi⟩ : Fin n) * paperOddMatrix ⟨j, hj⟩ +
        paperOddMatrix (⟨j, hj⟩ : Fin n) * paperOddMatrix ⟨i, hi⟩ = 0 := by
  simp only [paperOddMatrix]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  rw [← map_add]
  exact congrArg
    (LinearMap.toMatrix (endpointBasis (n := n)) (endpointBasis (n := n)))
    (paperOddGenerator_anticommute_of_lt hi hj hij)

theorem paperEvenMatrix_anticomm_of_lt {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i < j) :
    paperEvenMatrix (⟨i, hi⟩ : Fin n) * paperEvenMatrix ⟨j, hj⟩ +
        paperEvenMatrix (⟨j, hj⟩ : Fin n) * paperEvenMatrix ⟨i, hi⟩ = 0 := by
  simp only [paperEvenMatrix]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  rw [← map_add]
  exact congrArg
    (LinearMap.toMatrix (endpointBasis (n := n)) (endpointBasis (n := n)))
    (paperEvenGenerator_anticommute_of_lt hi hj hij)

theorem paperOddMatrix_anticomm_paperEvenMatrix_of_lt {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i < j) :
    paperOddMatrix (⟨i, hi⟩ : Fin n) * paperEvenMatrix ⟨j, hj⟩ +
        paperEvenMatrix (⟨j, hj⟩ : Fin n) * paperOddMatrix ⟨i, hi⟩ = 0 := by
  simp only [paperOddMatrix, paperEvenMatrix]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  rw [← map_add]
  exact congrArg
    (LinearMap.toMatrix (endpointBasis (n := n)) (endpointBasis (n := n)))
    (paperOdd_even_anticommute_of_lt hi hj hij)

theorem paperEvenMatrix_anticomm_paperOddMatrix_of_lt {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i < j) :
    paperEvenMatrix (⟨i, hi⟩ : Fin n) * paperOddMatrix ⟨j, hj⟩ +
        paperOddMatrix (⟨j, hj⟩ : Fin n) * paperEvenMatrix ⟨i, hi⟩ = 0 := by
  simp only [paperOddMatrix, paperEvenMatrix]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  rw [← map_add]
  exact congrArg
    (LinearMap.toMatrix (endpointBasis (n := n)) (endpointBasis (n := n)))
    (paperEven_odd_anticommute_of_lt hi hj hij)

end InfoGeometry.Canonical.CelikKocakPaperFormalism
