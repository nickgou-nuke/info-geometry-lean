import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Group.Invertible.Defs

noncomputable section

namespace InfoGeometry.Clifford

open CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- 
The geometric inverse of a vector in the Clifford algebra.
v⁻¹ = v / Q(v)
-/
def geometricInverse (v : M) [Invertible (Q v)] : CliffordAlgebra Q :=
  (Invertible.invOf (Q v) : R) • ι Q v

/-- 
Property: v * v⁻¹ = 1.
-/
theorem ι_mul_geometricInverse (v : M) [Invertible (Q v)] :
    ι Q v * geometricInverse Q v = 1 := by
  dsimp [geometricInverse]
  calc
    ι Q v * ((Invertible.invOf (Q v) : R) • ι Q v)
        = (Invertible.invOf (Q v) : R) • (ι Q v * ι Q v) := by
                simp
    _ = (Invertible.invOf (Q v) : R) • algebraMap R (CliffordAlgebra Q) (Q v) := by
            simp [CliffordAlgebra.ι_sq_scalar]
    _ = 1 := by
            rw [Algebra.smul_def, ← map_mul]
            exact congrArg (algebraMap R (CliffordAlgebra Q)) (invOf_mul_self (a := Q v))
/-- 
Property: v⁻¹ * v = 1.
-/
theorem geometricInverse_mul_ι (v : M) [Invertible (Q v)] :
    geometricInverse Q v * ι Q v = 1 := by
  dsimp [geometricInverse]
  calc
    _ = (Invertible.invOf (Q v) : R) • (ι Q v * ι Q v) := by
            simp
    _ = (Invertible.invOf (Q v) : R) • algebraMap R (CliffordAlgebra Q) (Q v) := by
            simp [CliffordAlgebra.ι_sq_scalar]
    _ = 1 := by
            rw [Algebra.smul_def, ← map_mul]
            exact congrArg (algebraMap R (CliffordAlgebra Q)) (invOf_mul_self (a := Q v))

/--
Radial scaling: the geometric inverse of a vector scales the norm as r ↦ 1/r.
(Specifically, Q(v⁻¹) = 1/Q(v)).
-/
theorem quad_geometricInverse (v : M) [Invertible (Q v)] :
    ∃ (v_inv : CliffordAlgebra Q), v_inv = geometricInverse Q v ∧ (v_inv * v_inv = algebraMap R _ (Invertible.invOf (Q v))) := by
  use geometricInverse Q v
  refine ⟨rfl, ?_⟩
  dsimp [geometricInverse]
  calc
    ((Invertible.invOf (Q v) : R) • ι Q v) * ((Invertible.invOf (Q v) : R) • ι Q v)
        = ((Invertible.invOf (Q v) : R) * (Invertible.invOf (Q v) : R)) • (ι Q v * ι Q v) := by
            rw [smul_mul_smul]
    _ = ((Invertible.invOf (Q v) : R) * (Invertible.invOf (Q v) : R)) • algebraMap R (CliffordAlgebra Q) (Q v) := by
            simp [CliffordAlgebra.ι_sq_scalar]
    _ = algebraMap R (CliffordAlgebra Q) (Invertible.invOf (Q v)) := by
            rw [Algebra.smul_def, ← map_mul]
            have hmul :
                (Invertible.invOf (Q v) : R) * (Invertible.invOf (Q v) : R) * (Q v)
                  = (Invertible.invOf (Q v) : R) := by
              calc
                (Invertible.invOf (Q v) : R) * (Invertible.invOf (Q v) : R) * (Q v)
                    = (Invertible.invOf (Q v) : R) * ((Invertible.invOf (Q v) : R) * (Q v)) := by
                        ac_rfl
                _ = (Invertible.invOf (Q v) : R) * 1 := by rw [invOf_mul_self]
                _ = (Invertible.invOf (Q v) : R) := by simp
            exact congrArg (algebraMap R (CliffordAlgebra Q)) hmul


end InfoGeometry.Clifford
