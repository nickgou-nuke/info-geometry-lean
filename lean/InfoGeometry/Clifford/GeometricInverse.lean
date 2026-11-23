/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Group.Invertible.Defs

noncomputable section

namespace InfoGeometry.Clifford

open CliffordAlgebra

/-- Non-commutativity ground witness (`2 × 2` spin algebra over `ℂ`). -/
theorem geometricInverse_exists_noncomm_pair :
    ∃ a b : Matrix (Fin 2) (Fin 2) ℂ, a * b ≠ b * a :=
  ⟨_root_.InfoGeometry.Algebra.FiniteSpin.J_plus,
   _root_.InfoGeometry.Algebra.FiniteSpin.J_minus,
   _root_.InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne⟩

/-- In any non-commutative division ring `[DivisionRing D]`, if an element `v : D` satisfies
`v * v = q` with `q ≠ 0`, then `v * (v * q⁻¹) = 1` and `(q⁻¹ * v) * v = 1`. -/
theorem divisionRing_geometric_inverse
    {D : Type*} [DivisionRing D] (v q : D)
    (hv : v * v = q) (hq : q ≠ 0) :
    v * (v * q⁻¹) = 1 ∧ (q⁻¹ * v) * v = 1 := by
  constructor
  · rw [← mul_assoc, hv, mul_inv_cancel₀ hq]
  · rw [mul_assoc, hv, inv_mul_cancel₀ hq]

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

/-!
## Versor products

The general Shirokov characteristic-polynomial construction is distinct from the
special inverse of a versor.  The following finite-list result stays in Mathlib's
native `CliffordAlgebra`: it assumes each vector factor has nonzero quadratic
value, and constructs the inverse by reversing the factor order.  It does not
claim that every blade or rotor is invertible, nor does it formalize the general
multivector determinant recurrence.
-/

section VersorProduct

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Ordered geometric product of a finite list of vector generators. -/
def versorProduct : List M → CliffordAlgebra Q
  | [] => 1
  | v :: vs => CliffordAlgebra.ι Q v * versorProduct vs

/-- Candidate inverse of a vector generator with nonzero quadratic value. -/
def nonNullVectorInverse (v : M) : CliffordAlgebra Q :=
  (Q v)⁻¹ • CliffordAlgebra.ι Q v

theorem ι_mul_nonNullVectorInverse (v : M) (hv : Q v ≠ 0) :
    CliffordAlgebra.ι Q v * nonNullVectorInverse Q v = 1 := by
  dsimp [nonNullVectorInverse]
  calc
    CliffordAlgebra.ι Q v * ((Q v)⁻¹ • CliffordAlgebra.ι Q v)
        = (Q v)⁻¹ • (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) := by simp
    _ = (Q v)⁻¹ • algebraMap R (CliffordAlgebra Q) (Q v) := by
          rw [CliffordAlgebra.ι_sq_scalar]
    _ = 1 := by
          rw [Algebra.smul_def, ← map_mul]
          exact congrArg (algebraMap R (CliffordAlgebra Q)) (inv_mul_cancel₀ hv)

theorem nonNullVectorInverse_mul_ι (v : M) (hv : Q v ≠ 0) :
    nonNullVectorInverse Q v * CliffordAlgebra.ι Q v = 1 := by
  dsimp [nonNullVectorInverse]
  calc
    ((Q v)⁻¹ • CliffordAlgebra.ι Q v) * CliffordAlgebra.ι Q v
        = (Q v)⁻¹ • (CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v) := by simp
    _ = (Q v)⁻¹ • algebraMap R (CliffordAlgebra Q) (Q v) := by
          rw [CliffordAlgebra.ι_sq_scalar]
    _ = 1 := by
          rw [Algebra.smul_def, ← map_mul]
          exact congrArg (algebraMap R (CliffordAlgebra Q)) (inv_mul_cancel₀ hv)

/-- Reverse-ordered product of the inverses of the vector factors. -/
def versorProductInverse : List M → CliffordAlgebra Q
  | [] => 1
  | v :: vs => versorProductInverse vs * nonNullVectorInverse Q v

/-- A finite product of non-null Clifford vectors is two-sided invertible;
the inverse reverses the factor order. -/
theorem versorProduct_two_sided_inverse (vs : List M)
    (hvs : ∀ v ∈ vs, Q v ≠ 0) :
    versorProduct Q vs * versorProductInverse Q vs = 1 ∧
      versorProductInverse Q vs * versorProduct Q vs = 1 := by
  induction vs with
  | nil => simp [versorProduct, versorProductInverse]
  | cons v vs ih =>
      have hv : Q v ≠ 0 := hvs v (List.mem_cons_self)
      have htail : ∀ w ∈ vs, Q w ≠ 0 := fun w hw => hvs w (List.mem_cons_of_mem v hw)
      obtain ⟨ih₁, ih₂⟩ := ih htail
      constructor
      · simp only [versorProduct, versorProductInverse]
        calc
          (CliffordAlgebra.ι Q v * versorProduct Q vs) *
              (versorProductInverse Q vs * nonNullVectorInverse Q v)
              = CliffordAlgebra.ι Q v *
                  (versorProduct Q vs * versorProductInverse Q vs) *
                    nonNullVectorInverse Q v := by noncomm_ring
          _ = 1 := by rw [ih₁, mul_one, ι_mul_nonNullVectorInverse Q v hv]
      · simp only [versorProduct, versorProductInverse]
        calc
          (versorProductInverse Q vs * nonNullVectorInverse Q v) *
              (CliffordAlgebra.ι Q v * versorProduct Q vs)
              = versorProductInverse Q vs *
                  (nonNullVectorInverse Q v * CliffordAlgebra.ι Q v) *
                    versorProduct Q vs := by noncomm_ring
          _ = 1 := by rw [nonNullVectorInverse_mul_ι Q v hv, mul_one, ih₂]

end VersorProduct

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
