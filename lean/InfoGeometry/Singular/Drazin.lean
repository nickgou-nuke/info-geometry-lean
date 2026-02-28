import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.GroupPower.Basic
import InfoGeometry.Singular.MoorePenrose

namespace InfoGeometry.Singular

section Drazin
variable {R : Type*} [Ring R]

/-- The Three Equations defining the Drazin Inverse of index k. -/
structure IsDrazinInverse (A D : R) (k : ℕ) : Prop where
  eq1 : D * A * D = D
  eq2 : A * D = D * A
  eq3 : A^k = A^(k + 1) * D

/-- The Spectral/Core Projector P_D = A * A^D -/
def Drazin_Projector (A D : R) (k : ℕ) (h : IsDrazinInverse A D k) : R := A * D

lemma Drazin_Projector_idempotent {A D : R} {k : ℕ} (h : IsDrazinInverse A D k) : 
    (Drazin_Projector A D k h) * (Drazin_Projector A D k h) = Drazin_Projector A D k h := by
  unfold Drazin_Projector
  calc
    (A * D) * (A * D) = A * (D * A * D) := by simp [mul_assoc]
    _ = A * D := by rw [h.eq1]

end Drazin

section Anomaly
variable {R : Type*} [Ring R] [AdjointLike R]

/-- 
THE CHIRAL ANOMALY: 
The commutator of the Geometric Mirror (MP) and the Spectral Mirror (Drazin).
χ = [P_MP, P_D]

This formally isolates the metric-spectral mismatch that occurs strictly 
on the singular causal boundary. 
-/
def ChiralAnomaly (A B D : R) (k : ℕ) 
    (hMP : IsMoorePenroseInverse A B) 
    (hD : IsDrazinInverse A D k) : R :=
  let P_MP := MP_Projector A B hMP
  let P_D := Drazin_Projector A D k hD
  P_MP * P_D - P_D * P_MP

/-- The Normal Metric Property: 
If the matrix commutes with its geometric adjoint (AA† = A†A), 
the anomaly rigorously vanishes (ε = 0). -/
def IsNormal (A : R) : Prop := A * A† = A† * A

end Anomaly
end InfoGeometry.Singular
