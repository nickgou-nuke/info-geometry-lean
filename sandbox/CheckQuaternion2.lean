import Mathlib
#check (inferInstance : Ring (Quaternion ℝ))
variable {R : Type*} [Ring R]
#check (inferInstance : Ring (Quaternion R))
