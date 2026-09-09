import InfoGeometry.Canonical.HestenesPauliSheetBridgeFinite
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # The real algebra equivalence `Cl⁺(1,3) ≃ M₂(ℂ)` -/

noncomputable section
namespace HestenesEvenPauliEquiv

open scoped DirectSum

open HestenesCl14
open HestenesPauliSheetBridge
open TwoSheetThreeColorWeyl

def sigmaPowersetCardFin4Equiv :
    (Σ n : ℕ, Set.powersetCard (Fin 4) n) ≃ Finset (Fin 4) where
  toFun x := x.2.1
  invFun s := ⟨s.card, ⟨s, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨n, s, hs⟩
    subst n
    rfl
  right_inv _ := rfl

def exteriorAlgebraV14Basis :
    Module.Basis (Finset (Fin 4)) ℝ (ExteriorAlgebra ℝ V14) := by
  let homogeneousBasis :
      Module.Basis (Σ n : ℕ, Set.powersetCard (Fin 4) n) ℝ
        (⨁ n : ℕ, ExteriorAlgebra.exteriorPower ℝ n V14) :=
    DFinsupp.basis (fun n => (Pi.basisFun ℝ (Fin 4)).exteriorPower n)
  let transported := homogeneousBasis.map
    (DirectSum.decomposeLinearEquiv
      (fun n : ℕ => ExteriorAlgebra.exteriorPower ℝ n V14)).symm
  exact transported.reindex sigmaPowersetCardFin4Equiv

def cliffordAlgebra14Basis : Module.Basis (Finset (Fin 4)) ℝ Cl14 :=
  exteriorAlgebraV14Basis.map (CliffordAlgebra.equivExterior Q14).symm

theorem cliffordAlgebra14_finrank : Module.finrank ℝ Cl14 = 16 := by
  rw [Module.finrank_eq_card_basis cliffordAlgebra14Basis]
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

noncomputable instance : FiniteDimensional ℝ Cl14 :=
  cliffordAlgebra14Basis.finiteDimensional_of_finite

/-- Right multiplication by the time-like generator exchanges the even and
odd Clifford summands. -/
def evenOddLinearEquiv :
    CliffordAlgebra.evenOdd Q14 0 ≃ₗ[ℝ] CliffordAlgebra.evenOdd Q14 1 where
  toFun x := ⟨x.1 * gamma 0, by
    simpa using SetLike.mul_mem_graded x.2 gamma_zero_mem_odd⟩
  invFun x := ⟨x.1 * gamma 0, by
    simpa using SetLike.mul_mem_graded x.2 gamma_zero_mem_odd⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_add' x y := by
    apply Subtype.ext
    simp [add_mul]
  map_smul' c x := by
    apply Subtype.ext
    simp

theorem clPlus14_finrank : Module.finrank ℝ ClPlus14 = 8 := by
  change Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 0) = 8
  have hsum : Module.finrank ℝ Cl14 =
      Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 0) +
        Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 1) := by
    rw [← Module.finrank_prod]
    exact LinearEquiv.finrank_eq
      (Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl Q14)).symm
  have heq : Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 0) =
      Module.finrank ℝ (CliffordAlgebra.evenOdd Q14 1) :=
    LinearEquiv.finrank_eq evenOddLinearEquiv
  rw [cliffordAlgebra14_finrank, ← heq] at hsum
  omega

theorem sheet_finrank : Module.finrank ℝ Sheet = 8 := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  norm_num

def pauli0 : Sheet := 1
def pauli1 : Sheet := !![0, 1; 1, 0]
def pauli2 : Sheet := !![0, -Complex.I; Complex.I, 0]
def pauli3 : Sheet := !![1, 0; 0, -1]

@[simp] theorem clPlusToPauli_sigma0 : clPlusToPauli (sigmaEven 0) = pauli1 := by
  rw [sigmaEven, clPlusToPauli_on_pair]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector, paravectorConj, basisVec, pauli1,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem clPlusToPauli_sigma1 : clPlusToPauli (sigmaEven 1) = pauli2 := by
  rw [sigmaEven, clPlusToPauli_on_pair]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector, paravectorConj, basisVec, pauli2,
      Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem clPlusToPauli_sigma2 : clPlusToPauli (sigmaEven 2) = pauli3 := by
  rw [sigmaEven, clPlusToPauli_on_pair]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector, paravectorConj, basisVec, pauli3,
      Matrix.mul_apply, Fin.sum_univ_two]

def volumeEven : ClPlus14 := sigmaEven 0 * sigmaEven 1 * sigmaEven 2

@[simp] theorem clPlusToPauli_volumeEven :
    clPlusToPauli volumeEven = Complex.I • (1 : Sheet) := by
  simp [volumeEven]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli1, pauli2, pauli3, Matrix.mul_apply, Fin.sum_univ_two]

def pauliCoeff0 (A : Sheet) : ℂ := (A 0 0 + A 1 1) / 2
def pauliCoeff1 (A : Sheet) : ℂ := (A 0 1 + A 1 0) / 2
def pauliCoeff2 (A : Sheet) : ℂ := (Complex.I / 2) * (A 0 1 - A 1 0)
def pauliCoeff3 (A : Sheet) : ℂ := (A 0 0 - A 1 1) / 2

def liftComplexCoeff (z : ℂ) (x : ClPlus14) : ClPlus14 :=
  z.re • x + z.im • (volumeEven * x)

def pauliPreimage (A : Sheet) : ClPlus14 :=
  liftComplexCoeff (pauliCoeff0 A) 1 +
    liftComplexCoeff (pauliCoeff1 A) (sigmaEven 0) +
    liftComplexCoeff (pauliCoeff2 A) (sigmaEven 1) +
    liftComplexCoeff (pauliCoeff3 A) (sigmaEven 2)

theorem clPlusToPauli_liftComplexCoeff (z : ℂ) (x : ClPlus14) :
    clPlusToPauli (liftComplexCoeff z x) = z • clPlusToPauli x := by
  rw [liftComplexCoeff, map_add, map_smul, map_smul, map_mul,
    clPlusToPauli_volumeEven]
  ext i j
  simp [Complex.ext_iff]
  <;> ring

theorem clPlusToPauli_pauliPreimage (A : Sheet) :
    clPlusToPauli (pauliPreimage A) = A := by
  rw [pauliPreimage, map_add, map_add, map_add]
  simp only [clPlusToPauli_liftComplexCoeff, map_one,
    clPlusToPauli_sigma0, clPlusToPauli_sigma1, clPlusToPauli_sigma2]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliCoeff0, pauliCoeff1, pauliCoeff2, pauliCoeff3,
      pauli1, pauli2, pauli3]
  all_goals ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

theorem clPlusToPauli_surjective : Function.Surjective clPlusToPauli :=
  fun A => ⟨pauliPreimage A, clPlusToPauli_pauliPreimage A⟩

theorem clPlusToPauli_injective : Function.Injective clPlusToPauli := by
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := clPlusToPauli.toLinearMap)
    (by rw [clPlus14_finrank, sheet_finrank])).2
      (by simpa using clPlusToPauli_surjective)

/-- The independently defined native even Clifford algebra is exactly the
real Pauli matrix algebra. -/
noncomputable def clPlusPauliAlgEquiv : ClPlus14 ≃ₐ[ℝ] Sheet :=
  AlgEquiv.ofBijective clPlusToPauli
    ⟨clPlusToPauli_injective, clPlusToPauli_surjective⟩

end HestenesEvenPauliEquiv
end noncomputable section
