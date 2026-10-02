import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
open ExteriorAlgebra
lemma ι_mul_ι_add_swap (x y : V) : ι R x * ι R y + ι R y * ι R x = 0 := by
  have h := ExteriorAlgebra.ι_sq_zero (x + y)
  have hx := ExteriorAlgebra.ι_sq_zero x
  have hy := ExteriorAlgebra.ι_sq_zero y
  rw [map_add] at h
  calc ι R x * ι R y + ι R y * ι R x
    _ = (ι R x + ι R y) * (ι R x + ι R y) - ι R x * ι R x - ι R y * ι R y := by noncomm_ring
    _ = 0 - 0 - 0 := by rw [←h, hx, hy]
    _ = 0 := by simp
