import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Canonical.CliffordParityBridge

namespace InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q]

/-- We specify the spacetime basis generators. -/
class HasSpacetimeBasis (Q : QuadraticForm R M) [HasVolumeElement R M Q] where
  gamma : Fin 4 → M
  omega_eq : Omega (R := R) (M := M) (Q := Q) = 
    ι Q (gamma 0) * ι Q (gamma 1) * ι Q (gamma 2) * ι Q (gamma 3)
  -- The generators are orthogonal.
  orthogonal : ∀ i j, i ≠ j → QuadraticMap.polar Q (gamma i) (gamma j) = 0

variable [HasSpacetimeBasis Q]

def gamma (i : Fin 4) : M := HasSpacetimeBasis.gamma Q i

/-- The six basis bivectors. -/
def basisBivector (i : Fin 6) : CliffordAlgebra Q :=
  match i with
  | 0 => ι Q (gamma Q 0) * ι Q (gamma Q 1)
  | 1 => ι Q (gamma Q 0) * ι Q (gamma Q 2)
  | 2 => ι Q (gamma Q 0) * ι Q (gamma Q 3)
  | 3 => ι Q (gamma Q 2) * ι Q (gamma Q 3)
  | 4 => ι Q (gamma Q 3) * ι Q (gamma Q 1)
  | 5 => ι Q (gamma Q 1) * ι Q (gamma Q 2)

/-- The exact grade-2 bivector sector for 1,3 spacetime. -/
def Bivector13 : Submodule R (CliffordAlgebra Q) :=
  Submodule.span R (Set.range (basisBivector Q))

omit [HasVolumeElement R M Q] [HasSpacetimeBasis Q] in
lemma ι_mul_ι_swap_of_orthogonal {x y : M} (h : QuadraticMap.polar Q x y = 0) :
    ι Q y * ι Q x = - (ι Q x * ι Q y) := by
  have h1 : ι Q x * ι Q y + ι Q y * ι Q x = 0 := by
    calc ι Q x * ι Q y + ι Q y * ι Q x 
      _ = algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q x y) := ι_mul_ι_add_swap x y
      _ = algebraMap R (CliffordAlgebra Q) 0 := by rw [h]
      _ = 0 := map_zero _
  exact eq_neg_of_add_eq_zero_right h1

lemma reverse_basisBivector (i : Fin 6) : 
    reverse (basisBivector Q i) = - basisBivector Q i := by
  revert i
  intro i
  fin_cases i
  all_goals {
    dsimp [basisBivector]
    rw [reverse.map_mul, reverse_ι, reverse_ι]
    apply ι_mul_ι_swap_of_orthogonal Q
    apply HasSpacetimeBasis.orthogonal
    decide
  }

theorem reverse_bivector (B : CliffordAlgebra Q) (h : B ∈ Bivector13 Q) :
    reverse B = -B := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h
  · intro B hB
    rcases hB with ⟨i, hi⟩
    rw [← hi]
    apply reverse_basisBivector
  · simp
  · intro x y hx hy hrev_x hrev_y
    rw [map_add, hrev_x, hrev_y, neg_add]
  · intro a x hx hrev_x
    rw [map_smul, hrev_x, smul_neg]

omit [HasSpacetimeBasis Q] in
lemma ι_mul_ι_mul_omega_comm (x y : M) : 
    (ι Q x * ι Q y) * Omega (Q := Q) = Omega (Q := Q) * (ι Q x * ι Q y) := by
  have h1 := HasVolumeElement.omega_odd (R := R) (M := M) (Q := Q) y
  have h2 := HasVolumeElement.omega_odd (R := R) (M := M) (Q := Q) x
  -- ι(y)*Omega = -Omega*ι(y) => (ι(y)*Omega) = -(Omega*ι(y)) -> actually omega_odd gives:
  -- Omega * ι = - ι * Omega
  -- => ι * Omega = - (Omega * ι)
  have h1_swap : ι Q y * Omega (Q := Q) = - (Omega (Q := Q) * ι Q y) := by
    rw [h1, neg_neg]
  have h2_swap : ι Q x * Omega (Q := Q) = - (Omega (Q := Q) * ι Q x) := by
    rw [h2, neg_neg]
  calc (ι Q x * ι Q y) * Omega (Q := Q)
    _ = ι Q x * (ι Q y * Omega (Q := Q)) := by rw [mul_assoc]
    _ = ι Q x * (- (Omega (Q := Q) * ι Q y)) := by rw [h1_swap]
    _ = - (ι Q x * (Omega (Q := Q) * ι Q y)) := by rw [mul_neg]
    _ = - ((ι Q x * Omega (Q := Q)) * ι Q y) := by rw [mul_assoc]
    _ = - ((- (Omega (Q := Q) * ι Q x)) * ι Q y) := by rw [h2_swap]
    _ = (Omega (Q := Q) * ι Q x) * ι Q y := by rw [neg_mul, neg_neg]
    _ = Omega (Q := Q) * (ι Q x * ι Q y) := by rw [mul_assoc]

lemma omega_comm_basisBivector (i : Fin 6) : 
    basisBivector Q i * Omega (Q := Q) = Omega (Q := Q) * basisBivector Q i := by
  revert i
  intro i
  fin_cases i
  all_goals {
    dsimp [basisBivector]
    apply ι_mul_ι_mul_omega_comm
  }

theorem omega_comm_bivector (B : CliffordAlgebra Q) (h : B ∈ Bivector13 Q) :
    B * Omega (Q := Q) = Omega (Q := Q) * B := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h
  · intro B hB
    rcases hB with ⟨i, hi⟩
    rw [← hi]
    apply omega_comm_basisBivector
  · simp
  · intro x y hx hy hcomm_x hcomm_y
    rw [add_mul, hcomm_x, hcomm_y, mul_add]
  · intro a x hx hcomm_x
    rw [Algebra.smul_mul_assoc, hcomm_x, Algebra.mul_smul_comm]

omit [HasVolumeElement R M Q] [HasSpacetimeBasis Q] in
lemma algebraMap_comm_left (c : R) (x : CliffordAlgebra Q) :
  x * algebraMap R _ c = algebraMap R _ c * x := (Algebra.commutes c x).symm


theorem basisBivector_mul_omega (i : Fin 6) : 
    basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  have h10 : ι Q (gamma Q 1) * ι Q (gamma Q 0) = - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 0 1 (by decide))
  have h20 : ι Q (gamma Q 2) * ι Q (gamma Q 0) = - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 0 2 (by decide))
  have h30 : ι Q (gamma Q 3) * ι Q (gamma Q 0) = - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 0 3 (by decide))
  have h21 : ι Q (gamma Q 2) * ι Q (gamma Q 1) = - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 1 2 (by decide))
  have h31 : ι Q (gamma Q 3) * ι Q (gamma Q 1) = - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 1 3 (by decide))
  have h32 : ι Q (gamma Q 3) * ι Q (gamma Q 2) = - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 2 3 (by decide))
  have h12 : ι Q (gamma Q 1) * ι Q (gamma Q 2) = - (ι Q (gamma Q 2) * ι Q (gamma Q 1)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 2 1 (by decide))
  have h13 : ι Q (gamma Q 1) * ι Q (gamma Q 3) = - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) 3 1 (by decide))
  have sq0 := ι_sq_scalar Q (gamma Q 0)
  have sq1 := ι_sq_scalar Q (gamma Q 1)
  have sq2 := ι_sq_scalar Q (gamma Q 2)
  have sq3 := ι_sq_scalar Q (gamma Q 3)
  fin_cases i
  · -- 0: 01
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 1)) * basisBivector Q 3) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h10]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [sq1]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 1)) * basisBivector Q 3) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))
  · -- 1: 02
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * basisBivector Q 4) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h20]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h21]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [sq0]
        _ = algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3) := by rw [sq2]
        _ = algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2))) * ι Q (gamma Q 3) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 0)))]
        _ = algebraMap R _ (Q (gamma Q 0)) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) := by rw [← Algebra.commutes (Q (gamma Q 2))]
        _ = algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by simp only [← mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * (ι Q (gamma Q 1) * ι Q (gamma Q 3)) := by rw [← RingHom.map_mul]
        _ = algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * - (ι Q (gamma Q 3) * ι Q (gamma Q 1)) := by rw [h13]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 1))) := by simp only [mul_neg, ← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 2)) * basisBivector Q 4) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨4, rfl⟩))
  · -- 2: 03
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 3)) * basisBivector Q 5) := by
      calc (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h30]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h31]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - ((ι Q (gamma Q 0) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 3)) := rfl
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) * ι Q (gamma Q 3)) := by rw [sq0]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * (ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (ι Q (gamma Q 1) * (algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 2)))) := by rw [Algebra.commutes (Q (gamma Q 3)) (ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ((ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 3))) * ι Q (gamma Q 2))) := by rw [← mul_assoc (ι Q (gamma Q 1)) (algebraMap R _ (Q (gamma Q 3))) (ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * ((algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 1)) * ι Q (gamma Q 2))) := by rw [Algebra.commutes (Q (gamma Q 3)) (ι Q (gamma Q 1))]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 0)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by rw [← mul_assoc (algebraMap R _ (Q (gamma Q 0))) (algebraMap R _ (Q (gamma Q 3))) (ι Q (gamma Q 1) * ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 3)) * (ι Q (gamma Q 1) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 0) * Q (gamma Q 3)) * basisBivector Q 5) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨5, rfl⟩))
  · -- 3: 23
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * basisBivector Q 0) := by
      calc (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 2) * - (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h30]
        _ = - ((ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h20]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 2) * - (ι Q (gamma Q 1) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h31]
        _ = - (ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h21]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [mul_neg, neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by rw [sq2]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * (algebraMap R _ (Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1))) := by rw [algebraMap_comm_left]
        _ = - (algebraMap R _ (Q (gamma Q 2) * Q (gamma Q 3)) * basisBivector Q 0) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
  · -- 4: 31
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * basisBivector Q 1) := by
      calc (ι Q (gamma Q 3) * ι Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 3) * - (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h10]
        _ = - ((ι Q (gamma Q 3) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 3)) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h30]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [sq1]
        _ = ι Q (gamma Q 0) * (ι Q (gamma Q 3) * algebraMap R _ (Q (gamma Q 1))) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 3)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [← Algebra.commutes]
        _ = ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 3) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [← Algebra.commutes]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * (ι Q (gamma Q 3) * ι Q (gamma Q 2)) * ι Q (gamma Q 3) := by simp only [mul_assoc]
        _ = algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * - (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3) := by rw [h32]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * (ι Q (gamma Q 3) * ι Q (gamma Q 3))) := by simp only [← mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0) * ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))) := by rw [sq3]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * algebraMap R _ (Q (gamma Q 3))) := by rw [mul_assoc (algebraMap R _ (Q (gamma Q 1)))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * (ι Q (gamma Q 2) * algebraMap R _ (Q (gamma Q 3))))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 2)))) := by rw [Algebra.commutes (Q (gamma Q 3)) (ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 3))) * ι Q (gamma Q 2))) := by rw [← mul_assoc (ι Q (gamma Q 0)) (algebraMap R _ (Q (gamma Q 3))) (ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((algebraMap R _ (Q (gamma Q 3)) * ι Q (gamma Q 0)) * ι Q (gamma Q 2))) := by rw [Algebra.commutes (Q (gamma Q 3)) (ι Q (gamma Q 0))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [← mul_assoc (algebraMap R _ (Q (gamma Q 1))) (algebraMap R _ (Q (gamma Q 3))) (ι Q (gamma Q 0) * ι Q (gamma Q 2))]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 3)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * (ι Q (gamma Q 0) * ι Q (gamma Q 2))) := by rw [mul_comm (Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 3) * Q (gamma Q 1)) * basisBivector Q 1) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · -- 5: 12
    dsimp [basisBivector]
    rw [HasSpacetimeBasis.omega_eq (Q := Q)]
    have H : (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * basisBivector Q 2) := by
      calc (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3))
        _ = ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 0)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [← mul_assoc]
        _ = ι Q (gamma Q 1) * - (ι Q (gamma Q 0) * ι Q (gamma Q 2)) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h20]
        _ = - ((ι Q (gamma Q 1) * ι Q (gamma Q 0)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (- (ι Q (gamma Q 0) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [h10]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by simp only [neg_mul, neg_neg, ← mul_assoc]
        _ = ι Q (gamma Q 0) * ι Q (gamma Q 1) * - (ι Q (gamma Q 1) * ι Q (gamma Q 2)) * ι Q (gamma Q 2) * ι Q (gamma Q 3) := by rw [h21]
        _ = - (ι Q (gamma Q 0) * ι Q (gamma Q 1) * ι Q (gamma Q 1) * ι Q (gamma Q 2) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by simp only [mul_neg, neg_mul, ← mul_assoc]
        _ = - (ι Q (gamma Q 0) * (ι Q (gamma Q 1) * ι Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [mul_assoc (ι Q (gamma Q 0))]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 2) * ι Q (gamma Q 2) * ι Q (gamma Q 3)) := by rw [sq1]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 2) * ι Q (gamma Q 2)) * ι Q (gamma Q 3)) := by rw [mul_assoc (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)))]
        _ = - (ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3)) := by rw [sq2]
        _ = - (ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - ((ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 1))) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3))) := by rw [← mul_assoc (ι Q (gamma Q 0)) (algebraMap R _ (Q (gamma Q 1))) (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3))]
        _ = - ((algebraMap R _ (Q (gamma Q 1)) * ι Q (gamma Q 0)) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3))) := by rw [Algebra.commutes (Q (gamma Q 1)) (ι Q (gamma Q 0))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (ι Q (gamma Q 0) * (algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((ι Q (gamma Q 0) * algebraMap R _ (Q (gamma Q 2))) * ι Q (gamma Q 3))) := by rw [← mul_assoc (ι Q (gamma Q 0)) (algebraMap R _ (Q (gamma Q 2))) (ι Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * ((algebraMap R _ (Q (gamma Q 2)) * ι Q (gamma Q 0)) * ι Q (gamma Q 3))) := by rw [Algebra.commutes (Q (gamma Q 2)) (ι Q (gamma Q 0))]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * (algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3)))) := by simp only [mul_assoc]
        _ = - (algebraMap R _ (Q (gamma Q 1)) * algebraMap R _ (Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by rw [← mul_assoc (algebraMap R _ (Q (gamma Q 1))) (algebraMap R _ (Q (gamma Q 2))) (ι Q (gamma Q 0) * ι Q (gamma Q 3))]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * (ι Q (gamma Q 0) * ι Q (gamma Q 3))) := by rw [← RingHom.map_mul]
        _ = - (algebraMap R _ (Q (gamma Q 1) * Q (gamma Q 2)) * basisBivector Q 2) := rfl
    erw [H]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))

theorem hodge_preserves_bivector (B : CliffordAlgebra Q) (h : B ∈ Bivector13 Q) :
    B * Omega (Q := Q) ∈ Bivector13 Q := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ h
  · intro B hB
    rcases hB with ⟨i, hi⟩
    rw [← hi]
    apply basisBivector_mul_omega
  · rw [zero_mul]; apply Submodule.zero_mem
  · intro x y hx hy hx_omega hy_omega
    rw [add_mul]
    apply Submodule.add_mem _ hx_omega hy_omega
  · intro a x hx hx_omega
    rw [Algebra.smul_mul_assoc]
    apply Submodule.smul_mem _ a hx_omega

theorem hodge_sq_bivector (B : CliffordAlgebra Q) (_h : B ∈ Bivector13 Q) :
    (B * Omega (Q := Q)) * Omega (Q := Q) = - B := by
  rw [mul_assoc, omega_sq (Q := Q), mul_neg, mul_one]

def hodgeBivector : Bivector13 Q →ₗ[R] Bivector13 Q where
  toFun B := ⟨(B : CliffordAlgebra Q) * Omega (Q := Q), hodge_preserves_bivector Q (B : CliffordAlgebra Q) B.property⟩
  map_add' x y := by ext; simp [add_mul]
  map_smul' c x := by ext; simp [Algebra.smul_mul_assoc]

end InfoGeometry.Canonical.HestenesBivectorCarrier
