import InfoGeometry.Canonical.FibonacciParafermionAtoms

/-!
# InfoGeometry.Categorical.Z3Parafermion

Theorem-safe categorical wrapper for the `Z₃` parafermion projector algebra.

This file re-exports the theorem-owned algebraic fragment from
`InfoGeometry.Canonical.FibonacciParafermionAtoms` under the categorical
namespace requested by the snippet.
-/

set_option autoImplicit false

namespace InfoGeometry.Categorical.Z3Parafermion

open InfoGeometry.Canonical.FibonacciParafermionAtoms

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The `+1` chiral projector. -/
noncomputable def proj_up (O : A) : A :=
  InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up O

/-- The `-1` chiral projector. -/
noncomputable def proj_down (O : A) : A :=
  InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down O

/-- The vacancy projector. -/
noncomputable def proj_vacancy (O : A) : A :=
  InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy O

/-- The non-vacancy/Drazin projector. -/
noncomputable def drazin_projector (O : A) : A :=
  InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_projector O

/-- Exact power reduction for a `Z₃` parafermion witness. -/
theorem O_pow_4 {O : A} (h : O ^ 3 = O) : O ^ 4 = O ^ 2 := by
  simpa using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.Z3Parafermion.O_pow_4 (A := A) (O := O) h)

/-- `proj_up` is orthogonal to the vacancy projector under `O^3 = O`. -/
theorem proj_up_orthogonal_vacancy (O : A) (h : O ^ 3 = O) :
    proj_up O * proj_vacancy O = 0 := by
  simpa [proj_up, proj_vacancy] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up_orthogonal_vacancy
      (A := A) (O := O) h)

/-- `proj_down` is orthogonal to the vacancy projector under `O^3 = O`. -/
theorem proj_down_orthogonal_vacancy (O : A) (h : O ^ 3 = O) :
    proj_down O * proj_vacancy O = 0 := by
  simpa [proj_down, proj_vacancy] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down_orthogonal_vacancy
      (A := A) (O := O) h)

/-- `proj_up` and `proj_down` are orthogonal under `O^3 = O`. -/
theorem proj_up_orthogonal_down (O : A) (h : O ^ 3 = O) :
    proj_up O * proj_down O = 0 := by
  simpa [proj_up, proj_down] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up_orthogonal_down
      (A := A) (O := O) h)

/-- `proj_down` and `proj_up` are orthogonal under `O^3 = O`. -/
theorem proj_down_orthogonal_up (O : A) (h : O ^ 3 = O) :
    proj_down O * proj_up O = 0 := by
  simpa [proj_up, proj_down] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down_orthogonal_up
      (A := A) (O := O) h)

/-- The vacancy projector is orthogonal to `proj_up` under `O^3 = O`. -/
theorem proj_vacancy_orthogonal_up (O : A) (h : O ^ 3 = O) :
    proj_vacancy O * proj_up O = 0 := by
  simpa [proj_up, proj_vacancy] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy_orthogonal_up
      (A := A) (O := O) h)

/-- The vacancy projector is orthogonal to `proj_down` under `O^3 = O`. -/
theorem proj_vacancy_orthogonal_down (O : A) (h : O ^ 3 = O) :
    proj_vacancy O * proj_down O = 0 := by
  simpa [proj_down, proj_vacancy] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy_orthogonal_down
      (A := A) (O := O) h)

/-- The three projectors form a partition of unity. -/
theorem proj_completeness (O : A) :
    proj_up O + proj_down O + proj_vacancy O = 1 := by
  simpa [proj_up, proj_down, proj_vacancy] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_completeness
      (A := A) (O := O))

/-- The Drazin projector is the chiral sum. -/
theorem drazin_eq_chiral_sum (O : A) :
    drazin_projector O = proj_up O + proj_down O := by
  simpa [proj_up, proj_down, drazin_projector] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_eq_chiral_sum
      (A := A) (O := O))

/-- The scalar-smul chiral projectors reconstruct the operator. -/
theorem O_reconstruction (O : A) :
    proj_up O - proj_down O = O := by
  simpa [proj_up, proj_down] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.O_reconstruction (A := A) (O := O))

/-- The scalar-smul chiral projectors reconstruct the square. -/
theorem O_sq_reconstruction (O : A) :
    proj_up O + proj_down O = O ^ 2 := by
  simpa [proj_up, proj_down] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.O_sq_reconstruction (A := A) (O := O))

/-- The `+1` projector is idempotent under `O^3 = O`. -/
theorem proj_up_idempotent (O : A) (h : O ^ 3 = O) :
    proj_up O * proj_up O = proj_up O := by
  simpa [proj_up] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_up_idempotent
      (A := A) (O := O) h)

/-- The `-1` projector is idempotent under `O^3 = O`. -/
theorem proj_down_idempotent (O : A) (h : O ^ 3 = O) :
    proj_down O * proj_down O = proj_down O := by
  simpa [proj_down] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_down_idempotent
      (A := A) (O := O) h)

/-- The vacancy projector is idempotent under `O^3 = O`. -/
theorem proj_vacancy_idempotent (O : A) (h : O ^ 3 = O) :
    proj_vacancy O * proj_vacancy O = proj_vacancy O := by
  simpa [proj_vacancy] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.proj_vacancy_idempotent
      (A := A) (O := O) h)

/-- The Drazin projector is idempotent under `O^3 = O`. -/
theorem drazin_idempotent (O : A) (h : O ^ 3 = O) :
    drazin_projector O * drazin_projector O = drazin_projector O := by
  simpa [drazin_projector] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_idempotent
      (A := A) (O := O) h)

/-- The Drazin projector is orthogonal to the vacancy projector. -/
theorem drazin_orthogonal_vacancy (O : A) (h : O ^ 3 = O) :
    drazin_projector O * proj_vacancy O = 0 := by
  simpa [drazin_projector, proj_vacancy] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.drazin_orthogonal_vacancy
      (A := A) (O := O) h)

/-- The `+1` projector is an eigenprojector for left multiplication by `O`. -/
theorem O_mul_proj_up (O : A) (h : O ^ 3 = O) :
    O * proj_up O = proj_up O := by
  simpa [proj_up] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.O_mul_proj_up
      (A := A) (O := O) h)

/-- The `-1` projector is an eigenprojector for left multiplication by `O`. -/
theorem O_mul_proj_down (O : A) (h : O ^ 3 = O) :
    O * proj_down O = - proj_down O := by
  simpa [proj_down] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.O_mul_proj_down
      (A := A) (O := O) h)

/-- The vacancy projector is annihilated by left multiplication by `O`. -/
theorem O_mul_proj_vacancy (O : A) (h : O ^ 3 = O) :
    O * proj_vacancy O = 0 := by
  simpa [proj_vacancy] using
    (InfoGeometry.Canonical.FibonacciParafermionAtoms.O_mul_proj_vacancy
      (A := A) (O := O) h)

end InfoGeometry.Categorical.Z3Parafermion
