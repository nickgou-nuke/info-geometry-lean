import Mathlib
import InfoGeometry.Quantum.RealMajorana

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local notation "EndH" => H →L[ℝ] H

-- Check if EndH has StarRing and if star is adjoint
example (A : EndH) : star A = ContinuousLinearMap.adjoint A := rfl

-- Check adjoint inner product laws
#check ContinuousLinearMap.adjoint_inner_left
#check ContinuousLinearMap.adjoint_inner_right

-- Check star composition
example (A B : EndH) : star (A * B) = star B * star A := star_mul A B

-- Check if comp and * are the same for EndH
example (A B : EndH) : A.comp B = A * B := rfl
