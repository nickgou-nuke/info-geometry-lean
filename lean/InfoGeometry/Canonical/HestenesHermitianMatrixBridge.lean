import InfoGeometry.Canonical.HestenesHermitianAdjoint
import InfoGeometry.Canonical.FiniteHestenesTomitaBridge

/-! # Native Hestenes Hermitian/Krein matrix bridge

The Hermitian Clifford anti-involution `γ₀ reverse(.) γ₀` is identified on the
whole even algebra with conjugate transpose under the independently proved
real algebra equivalence `Cl⁺(1,3) ≃ₐ[ℝ] M₂(ℂ)`.  Twisting by the fundamental
bivector then gives the existing matrix Krein adjoint.
-/

noncomputable section
namespace HestenesHermitianMatrixBridge

open HestenesCl14
open HestenesPauliSheetBridge
open HestenesEvenPauliEquiv
open HestenesKreinFramework
open HestenesKreinMatrixBridge
open HestenesHermitianAdjoint
open FiniteHestenesTomitaBridge

abbrev Sheet := HestenesPauliSheetBridge.Sheet

@[simp] theorem paravector_conjTranspose (v : V14) :
    Matrix.conjTranspose (paravector v) = paravector v := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector, Matrix.conjTranspose_apply]
  all_goals ring

@[simp] theorem paravectorConj_conjTranspose (v : V14) :
    Matrix.conjTranspose (paravectorConj v) = paravectorConj v := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravectorConj, Matrix.conjTranspose_apply]
  all_goals ring

private theorem hestenesAdjoint_pair (u v : V14) :
    clPlusToPauli
        (hestenesAdjoint ((CliffordAlgebra.even.ι Q14).bilin u v)) =
      Matrix.conjTranspose
        (clPlusToPauli ((CliffordAlgebra.even.ι Q14).bilin u v)) := by
  have hp :
      hestenesAdjoint ((CliffordAlgebra.even.ι Q14).bilin u v) =
        ((CliffordAlgebra.even.ι Q14).bilin (basisVec 0) v) *
          ((CliffordAlgebra.even.ι Q14).bilin u (basisVec 0)) := by
    apply Subtype.ext
    change gamma 0 * CliffordAlgebra.reverse
        (CliffordAlgebra.ι Q14 u * CliffordAlgebra.ι Q14 v) * gamma 0 =
      (gamma 0 * CliffordAlgebra.ι Q14 v) *
        (CliffordAlgebra.ι Q14 u * gamma 0)
    rw [CliffordAlgebra.reverse.map_mul]
    simp only [CliffordAlgebra.reverse_ι, mul_assoc]
  have hmap := congrArg clPlusToPauli hp
  rw [map_mul, clPlusToPauli_on_pair, clPlusToPauli_on_pair] at hmap
  calc
    clPlusToPauli (hestenesAdjoint
        ((CliffordAlgebra.even.ι Q14).bilin u v)) =
        paravector (basisVec 0) * paravectorConj v *
          (paravector u * paravectorConj (basisVec 0)) := hmap
    _ = Matrix.conjTranspose (clPlusToPauli
        ((CliffordAlgebra.even.ι Q14).bilin u v)) := by
      rw [clPlusToPauli_on_pair, Matrix.conjTranspose_mul,
        paravector_conjTranspose, paravectorConj_conjTranspose]
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [paravector, paravectorConj, basisVec,
          Matrix.mul_apply, Fin.sum_univ_two]

/-- Whole-algebra compatibility of the native Hestenes Hermitian adjoint with
matrix conjugate transpose. -/
theorem clPlusToPauli_hestenesAdjoint (x : ClPlus14) :
    clPlusToPauli (hestenesAdjoint x) =
      Matrix.conjTranspose (clPlusToPauli x) := by
  rcases x with ⟨x, hx⟩
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      have hr : hestenesAdjoint
          (⟨algebraMap ℝ Cl14 r, SetLike.algebraMap_mem_graded _ _⟩ : ClPlus14) =
          algebraMap ℝ ClPlus14 r := by
        apply Subtype.ext
        simp [hestenesAdjoint, reverseEven,
          ← Algebra.commutes r (gamma 0)]
        rw [mul_assoc, gamma_zero_sq, mul_one]
      have hs :
          (⟨algebraMap ℝ Cl14 r, SetLike.algebraMap_mem_graded _ _⟩ : ClPlus14) =
            algebraMap ℝ ClPlus14 r := by
        apply Subtype.ext
        rfl
      rw [hr, hs, clPlusToPauli.commutes]
      rw [Matrix.algebraMap_eq_diagonal]
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Matrix.conjTranspose_apply]
  | add x y hx hy ihx ihy =>
      change clPlusToPauli
          (hestenesAdjoint (⟨x, hx⟩ + ⟨y, hy⟩)) =
        Matrix.conjTranspose
          (clPlusToPauli (⟨x, hx⟩ + ⟨y, hy⟩))
      rw [hestenesAdjoint_add, map_add, map_add,
        Matrix.conjTranspose_add, ihx, ihy]
  | ι_mul_ι_mul u v x hx ihx =>
      let p : ClPlus14 := (CliffordAlgebra.even.ι Q14).bilin u v
      let z : ClPlus14 := ⟨x, hx⟩
      change clPlusToPauli (hestenesAdjoint (p * z)) =
        Matrix.conjTranspose (clPlusToPauli (p * z))
      rw [hestenesAdjoint_mul, map_mul, map_mul,
        Matrix.conjTranspose_mul, ihx, hestenesAdjoint_pair]

/-- The already constructed AlgEquiv transports the Hestenes adjoint exactly
to conjugate transpose. -/
theorem clPlusPauliAlgEquiv_hestenesAdjoint (x : ClPlus14) :
    clPlusPauliAlgEquiv (hestenesAdjoint x) =
      Matrix.conjTranspose (clPlusPauliAlgEquiv x) :=
  clPlusToPauli_hestenesAdjoint x

/-- The intrinsic Hermitian Hestenes operation is exactly the finite
standard-form Tomita pullback already constructed from matrix adjunction. -/
theorem hestenesAdjoint_eq_cliffordTomita (x : ClPlus14) :
    hestenesAdjoint x = cliffordTomita x := by
  apply clPlusPauliAlgEquiv.injective
  rw [clPlusPauliAlgEquiv_hestenesAdjoint, map_cliffordTomita]
  rfl

/-- Full native Krein bridge. -/
theorem clPlusToPauli_hestenesKreinAdjoint (x : ClPlus14) :
    clPlusToPauli (hestenesKreinAdjoint x) =
      kreinAdjoint (clPlusToPauli x) := by
  rw [hestenesKreinAdjoint, map_mul, map_mul,
    clPlusToPauli_sigma0, clPlusToPauli_hestenesAdjoint]
  rfl

@[simp] theorem hestenesKreinAdjoint_add (x y : ClPlus14) :
    hestenesKreinAdjoint (x + y) =
      hestenesKreinAdjoint x + hestenesKreinAdjoint y := by
  apply clPlusToPauli_injective
  simp [clPlusToPauli_hestenesKreinAdjoint]

@[simp] theorem hestenesKreinAdjoint_real_smul (r : ℝ) (x : ClPlus14) :
    hestenesKreinAdjoint (r • x) = r • hestenesKreinAdjoint x := by
  apply clPlusToPauli_injective
  rw [clPlusToPauli_hestenesKreinAdjoint]
  simp only [map_smul]
  change kreinAdjoint ((r : ℂ) • clPlusToPauli x) =
    (r : ℂ) • clPlusToPauli (hestenesKreinAdjoint x)
  rw [clPlusToPauli_hestenesKreinAdjoint]
  simpa using kreinAdjoint_smul (r : ℂ) (clPlusToPauli x)

@[simp] theorem hestenesKreinAdjoint_mul (x y : ClPlus14) :
    hestenesKreinAdjoint (x * y) =
      hestenesKreinAdjoint y * hestenesKreinAdjoint x := by
  apply clPlusToPauli_injective
  rw [map_mul, clPlusToPauli_hestenesKreinAdjoint,
    clPlusToPauli_hestenesKreinAdjoint,
    clPlusToPauli_hestenesKreinAdjoint]
  simp only [map_mul]
  change kreinAdjoint (clPlusToPauli x * clPlusToPauli y) =
    kreinAdjoint (clPlusToPauli y) * kreinAdjoint (clPlusToPauli x)
  unfold kreinAdjoint
  rw [Matrix.conjTranspose_mul]
  calc
    fundamentalSymmetry *
        (Matrix.conjTranspose (clPlusToPauli y) *
          Matrix.conjTranspose (clPlusToPauli x)) * fundamentalSymmetry =
        fundamentalSymmetry * Matrix.conjTranspose (clPlusToPauli y) *
          Matrix.conjTranspose (clPlusToPauli x) * fundamentalSymmetry := by
            simp only [Matrix.mul_assoc]
    _ = fundamentalSymmetry * Matrix.conjTranspose (clPlusToPauli y) *
          (fundamentalSymmetry * fundamentalSymmetry) *
          Matrix.conjTranspose (clPlusToPauli x) * fundamentalSymmetry := by
            rw [fundamentalSymmetry_sq]
            simp
    _ = (fundamentalSymmetry * Matrix.conjTranspose (clPlusToPauli y) *
          fundamentalSymmetry) *
        (fundamentalSymmetry * Matrix.conjTranspose (clPlusToPauli x) *
          fundamentalSymmetry) := by
            simp only [Matrix.mul_assoc]

@[simp] theorem hestenesKreinAdjoint_involutive (x : ClPlus14) :
    hestenesKreinAdjoint (hestenesKreinAdjoint x) = x := by
  apply clPlusToPauli_injective
  simp [clPlusToPauli_hestenesKreinAdjoint]

theorem hestenes_hermitian_krein_matrix_packet :
    (∀ x : ClPlus14,
      clPlusToPauli (hestenesAdjoint x) =
        Matrix.conjTranspose (clPlusToPauli x)) ∧
      (∀ x : ClPlus14,
        clPlusToPauli (hestenesKreinAdjoint x) =
          kreinAdjoint (clPlusToPauli x)) ∧
      (∀ x : ClPlus14, hestenesAdjoint x = cliffordTomita x) ∧
      (∀ x : ClPlus14,
        hestenesKreinAdjoint (hestenesKreinAdjoint x) = x) := by
  exact ⟨clPlusToPauli_hestenesAdjoint,
    clPlusToPauli_hestenesKreinAdjoint,
    hestenesAdjoint_eq_cliffordTomita,
    hestenesKreinAdjoint_involutive⟩

end HestenesHermitianMatrixBridge
end noncomputable section
