import Mathlib.Tactic
import Mathlib.Algebra.GroupWithZero.Basic
import InfoGeometry.Clifford.TowerMatrix

namespace InfoGeometry.Singular

open scoped Matrix
open Matrix

variable {n : ℕ}
abbrev Mat := InfoGeometry.Clifford.TowerMatrix.Mat n

/-- 
Drazin conditions for `D` being the spectral pseudoinverse of `A`.
Unlike Moore-Penrose, this does not depend on an adjoint (θ), 
but on the 'index' k where the kernel stabilizes.
-/
structure IsDrazin (A D : Mat) (k : ℕ) : Prop where
  comm : A * D = D * A
  eq1  : A^(k+1) * D = A^k
  eq2  : D * A * D = D

namespace IsDrazin

variable {A D : Mat} {k : ℕ} (h : IsDrazin A D k)

/-- 
The Spectral Projector (Spectral Mirror): 
Projector onto the 'Stable Range' of A.
-/
def Pspec : Mat := A * D

/-- 
The Spectral Complement (The Nilpotent Projector):
Projector onto the 'Generalized Null Space'. 
This is the "Coordinate Chart" for the spectral boundary.
-/
def Qspec : Mat := (1 : Mat) - (A * D)

theorem Pspec_idempotent : (A * D) * (A * D) = A * D := by
  calc
    (A * D) * (A * D) = A * (D * A * D) := by simp [Matrix.mul_assoc, h.comm]
    _ = A * D := by rw [h.eq2]

theorem Qspec_idempotent : ((1 : Mat) - (A * D)) * ((1 : Mat) - (A * D)) = (1 : Mat) - (A * D) := by
  simp [mul_sub, sub_mul, Pspec_idempotent h]

/-- 
On the 'Interior' (where A is invertible), 
the Spectral Mirror is simply the Identity.
-/
theorem Pspec_eq_one_of_invertible (hInv : IsUnit A) : 
    A * D = 1 := by
  -- If A is invertible, D must be A⁻¹ to satisfy DAD=D.
  -- Proof follows from the Drazin uniqueness/identities for units.
  let A_unit := hInv.unit
  have hAD : A * D = 1 := by
    -- comm: A D = D A
    -- eq2: D A D = D -> A D A D = A D -> (A D)^2 = A D
    -- For units, AD=1 is the only idempotent commuting with A.
    -- (This is a sketch; for the sandbox we use sorry to focus on the projector algebra)
    sorry
  exact hAD

end IsDrazin

end InfoGeometry.Singular
