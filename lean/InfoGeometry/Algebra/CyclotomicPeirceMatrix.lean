import InfoGeometry.Canonical.CyclotomicProjectorReadout
import InfoGeometry.Core.PeirceDecomposition

/-!
# Finite Peirce matrices from the existing Fourier readout

The finite family is the repository-owned `FourierCyclotomicReadout`, not a
second axiom record. Fourier families must be constructed by an upstream
owner. The matrix image has corner-valued entries and identity `diag(P_i)`,
not the identity of the whole ambient matrix ring.

All multiplication below is associative operator composition. The theorem
does not turn a nonassociative Zorn product into matrix multiplication.
-/

noncomputable section

namespace InfoGeometry.Algebra.CyclotomicPeirceMatrix

open InfoGeometry.Canonical.CyclotomicProjector

variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
variable {U : A} {n : ℕ} (F : FourierCyclotomicReadout (K := K) U n)

/-- The exact corner matrix; rows are target spectral sectors. -/
def blocks (X : A) : Matrix (Fin n) (Fin n) A :=
  fun i j => F.projector i * X * F.projector j

@[simp] theorem blocks_apply (X : A) (i j : Fin n) :
    blocks F X i j = F.projector i * X * F.projector j := rfl

/-- Completeness of the original family reconstructs the operator. -/
theorem sum_blocks (X : A) : (∑ i, ∑ j, blocks F X i j) = X := by
  calc
    (∑ i, ∑ j, blocks F X i j) =
        (∑ i, F.projector i) * X * (∑ j, F.projector j) := by
      simp only [blocks, Finset.sum_mul, Finset.mul_sum]
    _ = X := by simp only [F.complete, one_mul, mul_one]

/-- Fixed-corner support is a theorem, not arbitrary matrix data. -/
theorem blocks_supported (X : A) (i j : Fin n) :
    F.projector i * blocks F X i j * F.projector j = blocks F X i j := by
  unfold blocks
  calc
    F.projector i * (F.projector i * X * F.projector j) * F.projector j =
        (F.projector i * F.projector i) * X * (F.projector j * F.projector j) := by
      simp only [mul_assoc]
    _ = F.projector i * X * F.projector j := by rw [F.idempotent, F.idempotent]

theorem matching_block_product (X Y : A) (i j k : Fin n) :
    blocks F X i j * blocks F Y j k =
      F.projector i * X * F.projector j * Y * F.projector k := by
  unfold blocks
  calc
    (F.projector i * X * F.projector j) *
        (F.projector j * Y * F.projector k) =
        F.projector i * X * (F.projector j * F.projector j) * Y * F.projector k := by
      simp only [mul_assoc]
    _ = _ := by rw [F.idempotent]

/-- A mismatched intermediate spectral sector gives zero composition. -/
theorem mismatched_block_product (X Y : A) (i j k l : Fin n) (hjk : j ≠ k) :
    blocks F X i j * blocks F Y k l = 0 := by
  unfold blocks
  calc
    (F.projector i * X * F.projector j) *
        (F.projector k * Y * F.projector l) =
        F.projector i * X * (F.projector j * F.projector k) * Y * F.projector l := by
      simp only [mul_assoc]
    _ = 0 := by rw [F.orthogonal j k hjk]; simp

/-- A single off-diagonal corner squares to zero. A sum of corners need not. -/
theorem off_diagonal_block_square_zero (X : A) (i j : Fin n) (hij : i ≠ j) :
    blocks F X i j * blocks F X i j = 0 :=
  mismatched_block_product F X X i j i j hij.symm

/-- Genuine matrix multiplication of the corner-valued image. -/
theorem blocks_mul (X Y : A) : blocks F (X * Y) = blocks F X * blocks F Y := by
  ext i k
  change F.projector i * (X * Y) * F.projector k =
    ∑ j, blocks F X i j * blocks F Y j k
  calc
    F.projector i * (X * Y) * F.projector k =
        F.projector i * X * (∑ j, F.projector j) * Y * F.projector k := by
      rw [F.complete]
      simp only [mul_one, mul_assoc]
    _ = ∑ j, F.projector i * X * F.projector j * Y * F.projector k := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (matching_block_product F X Y i j k).symm

/-- Native linear embedding into the ambient matrix module. -/
def blocksLinear : A →ₗ[K] Matrix (Fin n) (Fin n) A where
  toFun := blocks F
  map_add' X Y := by
    ext i j
    simp [blocks, mul_add, add_mul]
  map_smul' c X := by
    ext i j
    simp [blocks, mul_smul_comm, smul_mul_assoc]

theorem blocks_injective : Function.Injective (blocks F) := by
  intro X Y h
  calc
    X = ∑ i, ∑ j, blocks F X i j := (sum_blocks F X).symm
    _ = ∑ i, ∑ j, blocks F Y i j := by rw [h]
    _ = Y := sum_blocks F Y

/-- The identity of the image is the diagonal of the spectral idempotents. -/
theorem blocks_one : blocks F 1 = Matrix.diagonal F.projector := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [blocks, F.idempotent]
  · simp [blocks, Matrix.diagonal, hij, F.orthogonal i j hij]

theorem image_identity_left (X : A) : blocks F 1 * blocks F X = blocks F X := by
  rw [← blocks_mul, one_mul]

theorem image_identity_right (X : A) : blocks F X * blocks F 1 = blocks F X := by
  rw [← blocks_mul, mul_one]

/-- There is generally no unital homomorphism into the FULL ambient matrix
ring with this formula. The corner image has its own identity. -/
theorem ambient_unit_obstruction (i : Fin n) (hi : F.projector i ≠ 1) :
    blocks F 1 ≠ (1 : Matrix (Fin n) (Fin n) A) := by
  intro h
  have hii := congrArg (fun M : Matrix (Fin n) (Fin n) A => M i i) h
  rw [blocks_one] at hii
  exact hi (by simpa using hii)

/-- The eigenvalue of the target projector acts on every block in that row. -/
theorem generator_left_block (X : A) (i j : Fin n) :
    U * blocks F X i j = algebraMap K A (F.ζ ^ i.val) * blocks F X i j := by
  unfold blocks
  calc
    U * (F.projector i * X * F.projector j) =
        (U * F.projector i) * X * F.projector j := by simp only [mul_assoc]
    _ = algebraMap K A (F.ζ ^ i.val) * (F.projector i * X * F.projector j) := by
      rw [F.eigen]
      simp only [mul_assoc]

end InfoGeometry.Algebra.CyclotomicPeirceMatrix
