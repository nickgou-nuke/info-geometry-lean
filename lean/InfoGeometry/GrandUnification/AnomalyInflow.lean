import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

namespace InfoGeometry.TopologicalFieldTheory

open LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- The Graded Supertrace over the twin-sheeted state space. -/
noncomputable def supertrace (Γ X : Module.End R M) : R :=
  LinearMap.trace R M (Γ * X)

/-- 
Theorem: The Determinant Spinning Instability.
-/
theorem spinning_instability_anomaly 
    (Γ A B : Module.End R M)
    (hA : Γ * A = - (A * Γ))
    (hB : Γ * B = - (B * Γ)) :
    supertrace Γ (A * B - B * A) = (2 : R) * supertrace Γ (A * B) := by
  have h_reverse_transport : 
      LinearMap.trace R M ((Γ * B) * A) = - LinearMap.trace R M (Γ * (A * B)) := by
    have step1 : LinearMap.trace R M ((Γ * B) * A) = LinearMap.trace R M (A * (Γ * B)) := 
      LinearMap.trace_mul_comm R (Γ * B) A
    rw [step1]
    have step2 : A * (Γ * B) = (A * Γ) * B := by rw [← mul_assoc]
    rw [step2]
    have step3 : A * Γ = - (Γ * A) := by
      calc A * Γ
        _ = - (- (A * Γ)) := by rw [neg_neg]
        _ = - (Γ * A) := by rw [← hA]
    rw [step3]
    have step4 : (- (Γ * A)) * B = - ((Γ * A) * B) := by rw [neg_mul]
    rw [step4]
    have step5 : LinearMap.trace R M (- ((Γ * A) * B)) = - LinearMap.trace R M ((Γ * A) * B) := 
      LinearMap.map_neg (LinearMap.trace R M) ((Γ * A) * B)
    rw [step5]
    have step6 : (Γ * A) * B = Γ * (A * B) := by rw [mul_assoc]
    rw [step6]

  have main1 : supertrace Γ (A * B - B * A) = LinearMap.trace R M (Γ * (A * B - B * A)) := rfl
  rw [main1]
  have main2 : Γ * (A * B - B * A) = Γ * (A * B) - Γ * (B * A) := by rw [mul_sub]
  rw [main2]
  have main3 : LinearMap.trace R M (Γ * (A * B) - Γ * (B * A)) = LinearMap.trace R M (Γ * (A * B)) - LinearMap.trace R M (Γ * (B * A)) := 
    LinearMap.map_sub (LinearMap.trace R M) (Γ * (A * B)) (Γ * (B * A))
  rw [main3]
  have main4 : Γ * (B * A) = (Γ * B) * A := by rw [mul_assoc]
  rw [main4]
  rw [h_reverse_transport]
  have main5 : LinearMap.trace R M (Γ * (A * B)) - (- LinearMap.trace R M (Γ * (A * B))) = LinearMap.trace R M (Γ * (A * B)) + LinearMap.trace R M (Γ * (A * B)) := by rw [sub_neg_eq_add]
  rw [main5]
  have main6 : LinearMap.trace R M (Γ * (A * B)) + LinearMap.trace R M (Γ * (A * B)) = (2 : R) * LinearMap.trace R M (Γ * (A * B)) := by
    have two_def : (2 : R) = 1 + 1 := by norm_num
    rw [two_def, add_mul, one_mul]
  rw [main6]
  rfl

structure AnomalyInflowTQFTPacket (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  ChiralGrading : Module.End R M
  CartanFormA : Module.End R M
  CartanFormB : Module.End R M
  BulkTopologicalIndex : R
  cartanA_odd : ChiralGrading * CartanFormA = - (CartanFormA * ChiralGrading)
  cartanB_odd : ChiralGrading * CartanFormB = - (CartanFormB * ChiralGrading)
  anomaly_inflow_cancellation : 
    BulkTopologicalIndex = supertrace ChiralGrading (CartanFormA * CartanFormB - CartanFormB * CartanFormA)

def AnomalyInflowTQFTTarget (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  Nonempty (AnomalyInflowTQFTPacket R M)

theorem constructAnomalyInflowTQFTTarget
    (P : AnomalyInflowTQFTPacket R M) :
    AnomalyInflowTQFTTarget R M := 
  ⟨P⟩

end InfoGeometry.TopologicalFieldTheory
