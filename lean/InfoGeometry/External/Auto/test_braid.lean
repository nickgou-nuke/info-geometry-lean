import Mathlib

variable {F : Type*} [Field F] (A : F)
variable {A_alg : Type*} [Ring A_alg] [Algebra F A_alg]
variable (ei ej : A_alg)

-- Let's test if noncomm_ring can expand and simplify with scalar multiplication.
-- Wait, noncomm_ring doesn't handle algebraMap well sometimes.
-- We can just define elements directly.
