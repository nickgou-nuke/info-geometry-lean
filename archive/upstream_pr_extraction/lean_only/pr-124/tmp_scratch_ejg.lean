import InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov

namespace InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov

namespace EmpiricalRNDensityPacket

variable {K : Type*} {B : Type*}
variable [Field K] [Ring B] [Algebra K B]
variable (P : EmpiricalRNDensityPacket (K := K) (B := B))

theorem scratch_emp (a : B) :
    empiricalStateRecursive (K := K) (B := B) P.chars P.hchars a =
      P.referenceState (P.rnDensity.density * a) := by
  ext b
  rw [empiricalStateRecursive_toLinearMap]
  exact P.rnDensity.rn_law b

theorem scratch_dual (t : R) (n : ℕ) :
    (1 + t • dualEpsilon R) ^ n =
      1 + ((n : R) * t) • dualEpsilon R := by
  simpa using nilpotent_power_law (A := DualNumbers R) (dualEpsilon R)
    (dualEpsilon_sq_zero R) t n

end EmpiricalRNDensityPacket
end InfoGeometry.OperatorAlgebra.ErlangenJaynesGromov
