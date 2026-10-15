import InfoGeometry.QuantumContext.DrazinSpectralKernel

/-!
# Generic left annihilation by the index-one Drazin kernel projector

This is the arbitrary-associative-ring complement to
`QuantumContext.DrazinSpectralKernel.group_inverse_nilpotent_zero`.
The matrix graph-Hodge owner already proves both sides for its matrix carrier;
here we expose the missing generic left-sided consequence using the existing
Drazin and projector definitions.

No convergence or spectral-limit statement is made.  In particular, this
algebraic projector identity alone does not identify the projector with a
limit of powers of a Markov transition matrix.
-/

namespace InfoGeometry.Experimental.Sandbox.DrazinGroupKernelLeftAnnihilation

open InfoGeometry.QuantumContext.Drazin

variable {R : Type*} [Ring R]
variable {A D : R}

/-- The index-one Drazin complementary projector annihilates the operator on
the left as well as on the right. -/
theorem group_inverse_kernel_left_zero
    (hD : IsDrazinInverse A D 1) :
    kernelProj A D * A = 0 := by
  have hcomm : kernelProj A D * A = A * kernelProj A D := by
    dsimp [kernelProj, spectralProj]
    calc
      (1 - A * D) * A = 1 * A - (A * D) * A := by rw [sub_mul]
      _ = A - A * (D * A) := by rw [one_mul, mul_assoc]
      _ = A - A * (A * D) := by rw [hD.comm.symm]
      _ = A * (1 - A * D) := by rw [mul_sub, mul_one]
  rw [hcomm, group_inverse_nilpotent_zero hD]

end InfoGeometry.Experimental.Sandbox.DrazinGroupKernelLeftAnnihilation
