import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Canonical.PrimitiveCuntzIsometry

noncomputable section

namespace InfoGeometry.Holography.TomitaTakesaki

open InfoGeometry.Canonical.PrimitiveCuntzIsometry

variable {A : Type*} [NormedRing A] [StarRing A] [CompleteSpace A]

/-- 
The Tomita-Takesaki Holographic System over a Star-Algebra.
Provides the Modular Conjugation (J) which maps boundary operators 
to their commutant (the bulk reflection).

In the Cuntz exactness framework, J is exactly the Higgs mass operator
J = S_L S_R^* + S_R S_L^* from Epoch 2!
-/
structure TomitaTakesakiSystem where
  S_L : A
  S_R : A
  
  -- The Modular Conjugation J
  J : A
  
  -- The fundamental definition of J as the chiral crossing (Higgs mass term)
  h_J_def : J = S_L * star S_R + S_R * star S_L
  
  -- Orthogonality and Identity of the Cuntz tree
  h_SL_SR_ortho : star S_L * S_R = 0
  h_SR_SL_ortho : star S_R * S_L = 0
  h_SL_iso : star S_L * S_L = 1
  h_SR_iso : star S_R * S_R = 1
  h_cuntz : S_L * star S_L + S_R * star S_R = 1

variable (tt : TomitaTakesakiSystem A)

/--
THEOREM: The Modular Conjugation maps Left to Right.
Applying J to the left boundary S_L maps it cleanly to the right bulk S_R.
-/
theorem Tomita_L_to_R : tt.J * tt.S_L = tt.S_R := by
  calc
    tt.J * tt.S_L = (tt.S_L * star tt.S_R + tt.S_R * star tt.S_L) * tt.S_L := by rw [tt.h_J_def]
    _ = tt.S_L * (star tt.S_R * tt.S_L) + tt.S_R * (star tt.S_L * tt.S_L) := by
      simp only [add_mul, mul_assoc]
    _ = tt.S_L * 0 + tt.S_R * 1 := by rw [tt.h_SR_SL_ortho, tt.h_SL_iso]
    _ = tt.S_R := by simp

/--
THEOREM: The Modular Conjugation maps Left-star to Right-star.
-/
theorem Tomita_L_star : star tt.S_L * tt.J = star tt.S_R := by
  calc
    star tt.S_L * tt.J = star tt.S_L * (tt.S_L * star tt.S_R + tt.S_R * star tt.S_L) := by rw [tt.h_J_def]
    _ = (star tt.S_L * tt.S_L) * star tt.S_R + (star tt.S_L * tt.S_R) * star tt.S_L := by
      simp only [mul_add, ← mul_assoc]
    _ = 1 * star tt.S_R + 0 * star tt.S_L := by rw [tt.h_SL_iso, tt.h_SL_SR_ortho]
    _ = star tt.S_R := by simp

/--
THEOREM: Bulk Reconstruction via Modular Conjugation.
Any boundary information (the S_L sector) is unitarily isomorphic 
to the bulk information (the S_R sector) via the modular conjugation J.
Conjugating a pure boundary operator S_L X S_L^* with J yields 
the pure bulk operator S_R X S_R^* exactly, with no information loss!
-/
theorem bulk_reconstruction_from_boundary (X : A) : 
    tt.J * (tt.S_L * X * star tt.S_L) * tt.J = tt.S_R * X * star tt.S_R := by
  calc
    tt.J * (tt.S_L * X * star tt.S_L) * tt.J
      = (tt.J * tt.S_L) * X * (star tt.S_L * tt.J) := by
        simp only [mul_assoc]
    _ = tt.S_R * X * star tt.S_R := by
        rw [Tomita_L_to_R tt, Tomita_L_star tt]

end InfoGeometry.Holography.TomitaTakesaki
