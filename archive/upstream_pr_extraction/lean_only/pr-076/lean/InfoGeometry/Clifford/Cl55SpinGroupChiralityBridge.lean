import InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
import Mathlib.Data.Matrix.Basic

/-!
# Chirality preservation for the native `Spin(5,5)` action

The evenness of a native spin-group element implies commutation with the
Witt volume element. Transporting this identity through the established
spinor algebra equivalence gives the corresponding matrix chirality
commutation and chiral subspace preservation theorems.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl55SpinGroupChiralityBridge

open CliffordAlgebra
open Matrix
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55SpinBivectorChiralityBridge
open InfoGeometry.Clifford.Cl55SpinorChirality
open InfoGeometry.Clifford.SpinorRep

/-- 🏆 THEOREM 1: Every even Clifford element commutes with the Witt volume element -/
theorem even_commutes_wittVolume {x : Cl55}
    (hx : x ∈ CliffordAlgebra.evenOdd Q55 0) :
    x * cl55WittVolume = cl55WittVolume * x := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      rw [Algebra.commutes]
  | add x y hx hy ihx ihy =>
      simp only [add_mul, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
      have hm₁ := cl55WittVolume_anticommutes m₁
      have hm₂ := cl55WittVolume_anticommutes m₂
      have hprod :
          (ι55 m₁ * ι55 m₂) * cl55WittVolume =
            cl55WittVolume * (ι55 m₁ * ι55 m₂) := by
        calc
          (ι55 m₁ * ι55 m₂) * cl55WittVolume =
              ι55 m₁ * (ι55 m₂ * cl55WittVolume) := by
                rw [mul_assoc]
          _ = ι55 m₁ * (-(cl55WittVolume * ι55 m₂)) := by
                rw [hm₂]
          _ = -((ι55 m₁ * cl55WittVolume) * ι55 m₂) := by
                noncomm_ring
          _ = -((-(cl55WittVolume * ι55 m₁)) * ι55 m₂) := by
                rw [hm₁]
          _ = cl55WittVolume * (ι55 m₁ * ι55 m₂) := by
                noncomm_ring
      calc
        (ι55 m₁ * ι55 m₂ * x) * cl55WittVolume =
            ι55 m₁ * ι55 m₂ * (x * cl55WittVolume) := by
              rw [mul_assoc]
        _ = ι55 m₁ * ι55 m₂ * (cl55WittVolume * x) := by rw [ih]
        _ = cl55WittVolume * (ι55 m₁ * ι55 m₂ * x) := by
              rw [← mul_assoc, hprod]
              rw [mul_assoc]

/-- 🏆 THEOREM 2: Every Spin(5,5) element commutes with the Witt volume element -/
theorem spinGroup_commutes_wittVolume (g : Spin55) :
    (g : Cl55) * cl55WittVolume = cl55WittVolume * (g : Cl55) :=
  even_commutes_wittVolume (spinGroup.mem_even g.prop)

/-- 🏆 THEOREM 3: Spin(5,5) matrix representation commutes with matrix chirality Γ₅₅ -/
theorem spinGroup_matrix_commutes_chirality55 (g : Spin55) :
    cl55SpinorAlgEquiv (g : Cl55) * chirality55 =
      chirality55 * cl55SpinorAlgEquiv (g : Cl55) := by
  rw [← spinorWittVolume_eq_chirality55]
  unfold spinorWittVolume
  rw [← map_mul, ← map_mul]
  rw [spinGroup_commutes_wittVolume g]

/-- 🏆 THEOREM 4: Spin(5,5) matrix representation commutes with chiral positive projector P₊ -/
theorem spinGroup_matrix_commutes_chiralPlusProjector (g : Spin55) :
    cl55SpinorAlgEquiv (g : Cl55) * chiralPlusProjector =
      chiralPlusProjector * cl55SpinorAlgEquiv (g : Cl55) := by
  dsimp [chiralPlusProjector]
  have h := spinGroup_matrix_commutes_chirality55 g
  simp [mul_add, add_mul, h]

/-- 🏆 THEOREM 5: Spin(5,5) matrix representation commutes with chiral negative projector P₋ -/
theorem spinGroup_matrix_commutes_chiralMinusProjector (g : Spin55) :
    cl55SpinorAlgEquiv (g : Cl55) * chiralMinusProjector =
      chiralMinusProjector * cl55SpinorAlgEquiv (g : Cl55) := by
  dsimp [chiralMinusProjector]
  have h := spinGroup_matrix_commutes_chirality55 g
  simp [mul_sub, sub_mul, h]

/-- 🏆 THEOREM 6: Spin(5,5) matrix action preserves the chiral positive subspace S₊ -/
theorem spinGroup_matrix_preserves_chiralPlus_vector (g : Spin55) (v : Fin (2^5) → ℝ)
    (hv : Matrix.mulVec chiralPlusProjector v = v) :
    Matrix.mulVec chiralPlusProjector (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v) =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v := by
  calc Matrix.mulVec chiralPlusProjector (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v)
    _ = Matrix.mulVec (chiralPlusProjector * cl55SpinorAlgEquiv (g : Cl55)) v := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55) * chiralPlusProjector) v := by rw [← spinGroup_matrix_commutes_chiralPlusProjector]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (Matrix.mulVec chiralPlusProjector v) := by rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v := by rw [hv]

/-- 🏆 THEOREM 7: Spin(5,5) matrix action preserves the chiral negative subspace S₋ -/
theorem spinGroup_matrix_preserves_chiralMinus_vector (g : Spin55) (v : Fin (2^5) → ℝ)
    (hv : Matrix.mulVec chiralMinusProjector v = v) :
    Matrix.mulVec chiralMinusProjector (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v) =
      Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v := by
  calc Matrix.mulVec chiralMinusProjector (Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v)
    _ = Matrix.mulVec (chiralMinusProjector * cl55SpinorAlgEquiv (g : Cl55)) v := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55) * chiralMinusProjector) v := by rw [← spinGroup_matrix_commutes_chiralMinusProjector]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) (Matrix.mulVec chiralMinusProjector v) := by rw [← Matrix.mulVec_mulVec]
    _ = Matrix.mulVec (cl55SpinorAlgEquiv (g : Cl55)) v := by rw [hv]

end InfoGeometry.Clifford.Cl55SpinGroupChiralityBridge
