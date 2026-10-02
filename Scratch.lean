import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

namespace InfoGeometry.TopologicalFieldTheory

open LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

theorem check_me
    (Γ A B : Module.End R M)
    (hA : Γ * A = - (A * Γ))
    (hB : Γ * B = - (B * Γ)) :
      LinearMap.trace R M ((Γ * B) * A) = - LinearMap.trace R M (Γ * (A * B)) := by
    rw [LinearMap.trace_mul_comm (Γ * B) A]
    rw [← mul_assoc, hB, mul_neg, map_neg, ← mul_assoc, LinearMap.trace_mul_comm Γ B]

end InfoGeometry.TopologicalFieldTheory
