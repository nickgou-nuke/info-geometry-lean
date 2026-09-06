import proofs.HestenesClPlus14
import proofs.TwoSheetThreeColorWeyl

/-!
# Constructive paravector bridge from real Cl⁺(1,3) to M₂(ℂ)

The explicit paravector matrices make the real quadratic identity transparent
and feed Mathlib's universal property of the even Clifford algebra.
-/

noncomputable section
namespace HestenesPauliSheetBridge

open HestenesCl14
open TwoSheetThreeColorWeyl

abbrev Sheet := M2C

def paravector (v : V14) : Sheet :=
  !![v 0 + v 3, v 1 - Complex.I * v 2;
     v 1 + Complex.I * v 2, v 0 - v 3]

def paravectorConj (v : V14) : Sheet :=
  !![v 0 - v 3, -(v 1 - Complex.I * v 2);
     -(v 1 + Complex.I * v 2), v 0 + v 3]

private theorem q14_explicit (v : V14) :
    Q14 v = v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 := by
  rw [Q14_apply]
  simp [qCoeff, Fin.sum_univ_succ]
  ring

@[simp] theorem paravector_add (u v : V14) :
    paravector (u + v) = paravector u + paravector v := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector] <;> ring

@[simp] theorem paravector_smul (c : ℝ) (v : V14) :
    paravector (c • v) = c • paravector v := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravector] <;> ring

@[simp] theorem paravectorConj_add (u v : V14) :
    paravectorConj (u + v) = paravectorConj u + paravectorConj v := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravectorConj] <;> ring

@[simp] theorem paravectorConj_smul (c : ℝ) (v : V14) :
    paravectorConj (c • v) = c • paravectorConj v := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravectorConj] <;> ring

@[simp] theorem paravectorConj_mul_paravector (v : V14) :
    paravectorConj v * paravector v =
      (Q14 v) • (1 : Sheet) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
  rw [q14_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravectorConj, paravector, Matrix.mul_apply, Fin.sum_univ_two,
      ] <;> ring_nf <;> try rw [hI] <;> ring

@[simp] theorem paravector_mul_paravectorConj (v : V14) :
    paravector v * paravectorConj v =
      (Q14 v) • (1 : Sheet) := by
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by norm_num
  rw [q14_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [paravectorConj, paravector, Matrix.mul_apply, Fin.sum_univ_two,
      ] <;> ring_nf <;> try rw [hI] <;> ring

noncomputable def evenHom : CliffordAlgebra.EvenHom Q14 Sheet where
  bilin := LinearMap.mk₂ ℝ
    (fun u v => paravector u * paravectorConj v)
    (by intro u v w; change paravector (u + v) * paravectorConj w = _
        rw [paravector_add, add_mul])
    (by intro c v w; change paravector (c • v) * paravectorConj w = _
        rw [paravector_smul, smul_mul_assoc])
    (by intro u v w; change paravector u * paravectorConj (v + w) = _
        rw [paravectorConj_add, mul_add])
    (by intro c v w; change paravector v * paravectorConj (c • w) = _
        rw [paravectorConj_smul, mul_smul_comm])
  contract v := by
    simp only [LinearMap.mk₂_apply]
    simpa only [Algebra.smul_def, mul_one] using
      paravector_mul_paravectorConj v
  contract_mid u v w := by
    simp only [LinearMap.mk₂_apply]
    calc
      (paravector u * paravectorConj v) *
          (paravector v * paravectorConj w) =
          paravector u * (paravectorConj v * paravector v) *
            paravectorConj w := by simp only [mul_assoc]
      _ = (Q14 v) • (paravector u * paravectorConj w) := by
        rw [paravectorConj_mul_paravector]
        rw [mul_smul_comm, smul_mul_assoc]
        simp

def clPlusToPauli : HestenesCl14.ClPlus14 →ₐ[ℝ] Sheet :=
  (CliffordAlgebra.even.lift Q14 evenHom)

@[simp] theorem clPlusToPauli_on_pair (u v : V14) :
    clPlusToPauli ((CliffordAlgebra.even.ι Q14).bilin u v) =
      paravector u * paravectorConj v := by
  exact CliffordAlgebra.even.lift_ι Q14 evenHom u v

def evenPair (i j : Fin 4) : HestenesCl14.ClPlus14 :=
  (CliffordAlgebra.even.ι Q14).bilin (basisVec i) (basisVec j)

def pauliTwo : Sheet := !![0, -Complex.I; Complex.I, 0]

@[simp] theorem clPlusToPauli_evenPair (i j : Fin 4) :
    clPlusToPauli (evenPair i j) =
      paravector (basisVec i) * paravectorConj (basisVec j) := by
  exact CliffordAlgebra.even.lift_ι Q14 evenHom (basisVec i) (basisVec j)

@[simp] theorem clPlusToPauli_evenPair_00 :
    clPlusToPauli (evenPair 0 0) = (1 : Sheet) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [evenPair, clPlusToPauli_on_pair, paravector, paravectorConj,
      basisVec, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem clPlusToPauli_evenPair_30 :
    clPlusToPauli (evenPair 3 0) = sheetGamma := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [evenPair, clPlusToPauli_on_pair, paravector, paravectorConj,
      basisVec, sheetGamma, sheetPlus, sheetMinus, Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp] theorem clPlusToPauli_evenPair_10 :
    clPlusToPauli (evenPair 1 0) = sheetFlip := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [evenPair, clPlusToPauli_on_pair, paravector, paravectorConj,
      basisVec, sheetFlip, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem clPlusToPauli_evenPair_20 :
    clPlusToPauli (evenPair 2 0) = pauliTwo := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [evenPair, clPlusToPauli_on_pair, paravector, paravectorConj,
      basisVec, pauliTwo, Matrix.mul_apply, Fin.sum_univ_two]

end HestenesPauliSheetBridge
end noncomputable section
