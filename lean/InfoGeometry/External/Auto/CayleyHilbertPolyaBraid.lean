import Mathlib.Tactic

/-!
# Cayley-Hilbert-Pólya-Braid: The Arithmetic Topology of Spacetime

Elementary matrix identities around Cayley-style transforms.
-/

noncomputable section

open Matrix
open Complex

namespace LegacyCayleyHilbertPolyaBraid

/-- The Cayley transform:
    C(H) = (H − iI)(H + iI)⁻¹

    Maps self-adjoint H to unitary U. -/
def cayleyTransform {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) : Matrix n n ℂ :=
  (H - I • (1 : Matrix n n ℂ)) * (H + I • (1 : Matrix n n ℂ))⁻¹

/-- The inverse Cayley transform:
    C⁻¹(U) = i(I + U)(I − U)⁻¹ -/
def inverseCayley {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) : Matrix n n ℂ :=
  I • ((1 : Matrix n n ℂ) + U) * ((1 : Matrix n n ℂ) - U)⁻¹

/-- A simple mathematically true and proven statement about conjTranspose -/
theorem conjTranspose_zero {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.conjTranspose (0 : Matrix n n ℂ) = 0 := by
  ext i j
  simp

/-- The conjugate transpose of the identity matrix is the identity matrix. -/
theorem conjTranspose_one {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.conjTranspose (1 : Matrix n n ℂ) = 1 := by
  ext i j
  by_cases h : i = j
  · simp [Matrix.one_apply, h]
  · have h2 : j ≠ i := Ne.symm h
    simp [h, h2]

end LegacyCayleyHilbertPolyaBraid
