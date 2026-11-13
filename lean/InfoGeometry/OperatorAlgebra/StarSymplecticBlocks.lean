/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.MatrixNoncommutativity
import InfoGeometry.Clifford.OperatorValuedJones
import InfoGeometry.OperatorAlgebra.StarFormPreservation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Star-form blocks over a noncommutative coefficient ring

The frame is the existing `InfoGeometry.Clifford` frame. Its exchange matrix
is `J_mat`, and the skew form used here is `-K_mat = !![0, -1; 1, 0]`.
The first section needs only a ring. The star section constructs the actual
subgroup-valued squeeze homomorphism and classifies the infinitesimal blocks.
No analytic dilation, exponential, or Mellin transform is used.
-/

namespace InfoGeometry.OperatorAlgebra.StarSymplecticBlocks

open InfoGeometry.Clifford
open InfoGeometry.OperatorAlgebra.StarFormPreservation

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A]

/-! ## Unit-valued braiding -/

/-- A two-state clock matrix with an arbitrary coefficient. -/
def clockMatrix (a : A) : Matrix (Fin 2) (Fin 2) A :=
  !![1, 0; 0, a]

/-- The reciprocal diagonal factor for one unit. This is not asserted to be
a homomorphism on a noncommutative unit group. -/
def reciprocalDiagonalUnit (u : Aˣ) : (Matrix (Fin 2) (Fin 2) A)ˣ where
  val := !![(u : A), 0; 0, (↑u⁻¹ : A)]
  inv := !![(↑u⁻¹ : A), 0; 0, (u : A)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem reciprocalDiagonalUnit_val (u : Aˣ) :
    (reciprocalDiagonalUnit u : Matrix (Fin 2) (Fin 2) A) =
      !![(u : A), 0; 0, (↑u⁻¹ : A)] :=
  rfl

@[simp]
theorem reciprocalDiagonalUnit_inv (u : Aˣ) :
    (reciprocalDiagonalUnit u)⁻¹ = reciprocalDiagonalUnit u⁻¹ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reciprocalDiagonalUnit]

/-- The ordered Weyl braid is valid for each unit, without commuting coefficients. -/
theorem nonabelian_weyl_braiding (u : Aˣ) :
    J_mat (B := A) * clockMatrix (u : A) =
      (reciprocalDiagonalUnit u : Matrix (Fin 2) (Fin 2) A) *
        clockMatrix (u : A) * J_mat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_mat, clockMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- Exchanging the two blocks inverts the reciprocal diagonal factor. -/
theorem reciprocalDiagonal_shift_inversion (u : Aˣ) :
    J_mat (B := A) *
        (reciprocalDiagonalUnit u : Matrix (Fin 2) (Fin 2) A) * J_mat =
      (reciprocalDiagonalUnit u⁻¹ : Matrix (Fin 2) (Fin 2) A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Twists by an internal coefficient -/

/-- The exchange frame element multiplied by an internal coefficient. -/
def symmetricTwist (j : A) : Matrix (Fin 2) (Fin 2) A :=
  j • J_mat

/-- The skew frame element multiplied by an internal coefficient. -/
def skewTwist (j : A) : Matrix (Fin 2) (Fin 2) A :=
  j • (-K_mat)

@[simp]
theorem symmetricTwist_eq (j : A) : symmetricTwist j = !![0, j; j, 0] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [symmetricTwist, J_mat]

@[simp]
theorem skewTwist_eq (j : A) : skewTwist j = !![0, -j; j, 0] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [skewTwist, K_mat]

/-- The square uses the actual ordered coefficient product `j * j`. -/
theorem symmetricTwist_sq (j : A) :
    symmetricTwist j * symmetricTwist j = Matrix.scalar (Fin 2) (j * j) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem skewTwist_sq (j : A) :
    skewTwist j * skewTwist j = -(Matrix.scalar (Fin 2) (j * j)) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem symmetricTwist_sq_of_sq_eq_neg_one {j : A} (hj : j * j = -1) :
    symmetricTwist j * symmetricTwist j = -1 := by
  rw [symmetricTwist_sq, hj, map_neg, map_one]

theorem skewTwist_sq_of_sq_eq_neg_one {j : A} (hj : j * j = -1) :
    skewTwist j * skewTwist j = 1 := by
  rw [skewTwist_sq, hj]
  simp

theorem grading_symmetricTwist_anticommute (j : A) :
    Gamma_mat (B := A) * symmetricTwist j + symmetricTwist j * Gamma_mat = 0 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Gamma_mat]

theorem grading_skewTwist_anticommute (j : A) :
    Gamma_mat (B := A) * skewTwist j + skewTwist j * Gamma_mat = 0 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Gamma_mat]

theorem symmetricTwist_skewTwist_anticommute (j : A) :
    symmetricTwist j * skewTwist j + skewTwist j * symmetricTwist j = 0 := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp

/-! ## Hamiltonian blocks for the specified star form -/

section Star

variable [StarRing A]

/-- The concrete form is skew-adjoint for the matrix conjugate-transpose star. -/
theorem star_skewForm :
    star (-(K_mat (B := A))) = -(-(K_mat (B := A))) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K_mat]

/-- The Hamiltonian block with unconstrained off-diagonal entries. -/
def hamiltonianBlock (a b c : A) : Matrix (Fin 2) (Fin 2) A :=
  !![a, b; c, -star a]

/-- All three independent conditions in the infinitesimal form equation.
The fourth matrix entry follows from involutivity of star. -/
theorem mem_infinitesimal_iff (X : Matrix (Fin 2) (Fin 2) A) :
    X ∈ infinitesimalLieSubalgebra (-K_mat) ↔
      star (X 0 1) = X 0 1 ∧ star (X 1 0) = X 1 0 ∧
        X 1 1 = -star (X 0 0) := by
  rw [mem_infinitesimalLieSubalgebra]
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 0) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 0 1) h
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) A => M 1 1) h
    have hc : star (X 1 0) - X 1 0 = 0 := by
      simpa [K_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        sub_eq_add_neg] using h00
    have hb : X 0 1 - star (X 0 1) = 0 := by
      simpa [K_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        sub_eq_add_neg, add_comm] using h11
    have hd : -star (X 0 0) - X 1 1 = 0 := by
      simpa [K_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        sub_eq_add_neg] using h01
    exact ⟨(sub_eq_zero.mp hb).symm, sub_eq_zero.mp hc, (sub_eq_zero.mp hd).symm⟩
  · rintro ⟨hb, hc, hd⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [K_mat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb, hc, hd]

@[simp]
theorem hamiltonianBlock_mem_iff (a b c : A) :
    hamiltonianBlock a b c ∈ infinitesimalLieSubalgebra (-K_mat) ↔
      star b = b ∧ star c = c := by
  rw [mem_infinitesimal_iff]
  simp [hamiltonianBlock]

/-- Every infinitesimal form-preserving matrix has exactly the Hamiltonian
block shape, with self-adjoint off-diagonal entries. -/
theorem mem_iff_exists_hamiltonianBlock (X : Matrix (Fin 2) (Fin 2) A) :
    X ∈ infinitesimalLieSubalgebra (-K_mat) ↔
      ∃ a b c : A, star b = b ∧ star c = c ∧ X = hamiltonianBlock a b c := by
  rw [mem_infinitesimal_iff]
  constructor
  · rintro ⟨hb, hc, hd⟩
    refine ⟨X 0 0, X 0 1, X 1 0, hb, hc, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hamiltonianBlock, hd]
  · rintro ⟨a, b, c, hb, hc, rfl⟩
    simp [hamiltonianBlock, hb, hc]

/-- The existing grading matrix satisfies the infinitesimal equation. -/
theorem grading_mem_infinitesimal :
    Gamma_mat (B := A) ∈ infinitesimalLieSubalgebra (-K_mat) := by
  rw [mem_infinitesimal_iff]
  simp [Gamma_mat]

/-! ## The squeeze as a native group homomorphism -/

/-- The diagonal squeeze is an actual unit; its inverse is displayed explicitly. -/
def squeezeUnit (u : Aˣ) : (Matrix (Fin 2) (Fin 2) A)ˣ where
  val := !![(u : A), 0; 0, star (↑u⁻¹ : A)]
  inv := !![(↑u⁻¹ : A), 0; 0, star (u : A)]
  val_inv := by
    have hstar : star (↑u⁻¹ : A) * star (u : A) = 1 := by
      simpa only [star_mul, star_one] using congrArg star (Units.mul_inv u)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hstar]
  inv_val := by
    have hstar : star (u : A) * star (↑u⁻¹ : A) = 1 := by
      simpa only [star_mul, star_one] using congrArg star (Units.inv_mul u)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hstar]

@[simp]
theorem squeezeUnit_val (u : Aˣ) :
    (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) =
      !![(u : A), 0; 0, star (↑u⁻¹ : A)] :=
  rfl

@[simp]
theorem squeezeUnit_inv_val (u : Aˣ) :
    (↑((squeezeUnit u)⁻¹) : Matrix (Fin 2) (Fin 2) A) =
      !![(↑u⁻¹ : A), 0; 0, star (u : A)] :=
  rfl

@[simp]
theorem squeezeUnit_one : squeezeUnit (1 : Aˣ) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Inversion and star both reverse order, so the squeeze preserves multiplication. -/
@[simp]
theorem squeezeUnit_mul (u v : Aˣ) : squeezeUnit (u * v) = squeezeUnit u * squeezeUnit v := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_inv_rev, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem squeezeUnit_inv (u : Aˣ) : (squeezeUnit u)⁻¹ = squeezeUnit u⁻¹ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem squeezeUnit_injective : Function.Injective (squeezeUnit (A := A)) := by
  intro u v h
  apply Units.ext
  have h00 := congrArg
    (fun w : (Matrix (Fin 2) (Fin 2) A)ˣ => (w : Matrix (Fin 2) (Fin 2) A) 0 0) h
  simpa using h00

/-- The constructed squeeze preserves the actual skew star form. -/
theorem squeeze_preserves (u : Aˣ) :
    star (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) * (-K_mat) *
        (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) = -K_mat := by
  have hstar : star (u : A) * star (↑u⁻¹ : A) = 1 := by
    simpa only [star_mul, star_one] using congrArg star (Units.inv_mul u)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K_mat, Matrix.mul_apply, Fin.sum_univ_two, hstar]

/-- The unit group embeds in the native group preserving the skew form. -/
def squeezeHom : Aˣ →* preservingSubgroup (-(K_mat (B := A))) where
  toFun u := ⟨squeezeUnit u, squeeze_preserves u⟩
  map_one' := by
    apply Subtype.ext
    exact squeezeUnit_one
  map_mul' u v := by
    apply Subtype.ext
    exact squeezeUnit_mul u v

@[simp]
theorem squeezeHom_coe (u : Aˣ) : (squeezeHom u : (Matrix (Fin 2) (Fin 2) A)ˣ) =
    squeezeUnit u :=
  rfl

theorem squeezeHom_injective : Function.Injective (squeezeHom (A := A)) := by
  intro u v h
  apply squeezeUnit_injective
  exact congrArg (fun w : preservingSubgroup (-(K_mat (B := A))) =>
    (w : (Matrix (Fin 2) (Fin 2) A)ˣ)) h

/-- Exchanging the two diagonal blocks produces the star of the inverse squeeze. -/
theorem shift_squeeze_eq_star_inverse (u : Aˣ) :
    J_mat (B := A) * (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) * J_mat =
      star (↑((squeezeUnit u)⁻¹) : Matrix (Fin 2) (Fin 2) A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J_mat, Matrix.mul_apply, Fin.sum_univ_two]

/-- The shifted squeeze is the biorthogonal partner for the ordinary star pairing. -/
theorem squeeze_mul_star_shift_squeeze (u : Aˣ) :
    (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) *
        star (J_mat * (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) * J_mat) = 1 := by
  rw [shift_squeeze_eq_star_inverse, star_star]
  exact Units.mul_inv (squeezeUnit u)

theorem star_shift_squeeze_mul_squeeze (u : Aˣ) :
    star (J_mat * (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) * J_mat) *
        (squeezeUnit u : Matrix (Fin 2) (Fin 2) A) = 1 := by
  rw [shift_squeeze_eq_star_inverse, star_star]
  exact Units.inv_mul (squeezeUnit u)

end Star

end InfoGeometry.OperatorAlgebra.StarSymplecticBlocks
