import Mathlib
import InfoGeometry.NCG.BlockSupermatrixGradedTrace
import InfoGeometry.NCG.BerezinianExponentialSupertrace

/-!
# Finite Noncommutative Operator Blocks for the Graded Supertrace

This bridge exposes the repository's finite block-supermatrix carrier with its
custom block multiplication, proves the graded
superbracket supertrace identity there, exposes the finite block-diagonal
matrix-exponential Berezinian theorem, and supplies an explicit noncommuting
pair. The base coefficient ring is commutative as required by the matrix trace
theorem; the block carrier has a noncommuting pair. The imported carrier has
not been packaged here with a lawful associative-ring instance. These results
do not assert an equivalence with the scalar carrier or a representation on
the Sato spinor tower.
-/

namespace InfoGeometry.SuperGrassmannian.RealSuperGrassmannianOperatorBlocks

open InfoGeometry.NCG.BlockSupermatrixGradedTrace

/-! The generic theorem is exposed at the Section 46 bridge boundary. -/

/-- Block multiplication is associative on the finite block carrier. This is a
law for the custom multiplication; it does not register a ring or algebra
instance on `SuperMatrix`. -/
theorem operator_block_mul_assoc
    {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R]
    (X Y Z : InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix
      (m := m) (n := n) (R := R)) :
    (X * Y) * Z = X * (Y * Z) := by
  ext <;>
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc] <;>
    abel

theorem operator_block_superbracket_supertrace_zero
    {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R]
    (p q : InfoGeometry.NCG.BlockSupermatrixGradedTrace.Parity)
    (X Y : InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix
      (m := m) (n := n) (R := R))
    (hX : InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.IsHomogeneous p X)
    (hY : InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.IsHomogeneous q Y) :
    InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.supertrace
      (InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.superbracket p q X Y) = 0 :=
  InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.supertrace_superbracket_eq_zero
    p q X Y hX hY

/-! A concrete `2 × 2` matrix-block instance witnesses noncommutativity. -/

abbrev RationalOperatorBlock :=
  InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix
    (m := Fin 2) (n := Fin 2) (R := ℚ)

def matrixUnit01 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 0, 0]
def matrixUnit10 : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

def operatorX : RationalOperatorBlock := ⟨matrixUnit01, 0, 0, 0⟩
def operatorY : RationalOperatorBlock := ⟨matrixUnit10, 0, 0, 0⟩

theorem operatorX_even :
    InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.IsHomogeneous .even operatorX := by
  simp [InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.IsHomogeneous,
    operatorX]

theorem operatorY_even :
    InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.IsHomogeneous .even operatorY := by
  simp [InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.IsHomogeneous,
    operatorY]

/-- These operator blocks do not commute: their diagonal blocks are `E₀₁` and `E₁₀`. -/
theorem concrete_operator_blocks_noncommute : operatorX * operatorY ≠ operatorY * operatorX := by
  intro h
  have hA := congrArg (fun Z : RationalOperatorBlock => Z.A) h
  norm_num [operatorX, operatorY, matrixUnit01, matrixUnit10,
    InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.mul,
    Matrix.mul_apply, Fin.sum_univ_two] at hA

/-- Graded superbracket cancellation holds for the witnessed block carrier. -/
theorem concrete_operator_superbracket_trace_zero :
    InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.supertrace
      (InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.superbracket
        .even .even operatorX operatorY) = 0 :=
  operator_block_superbracket_supertrace_zero .even .even operatorX operatorY
    operatorX_even operatorY_even

theorem concrete_operator_supertrace_cyclic :
    InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.supertrace
      (operatorX * operatorY) =
    InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.supertrace
      (operatorY * operatorX) := by
  simpa [InfoGeometry.NCG.BlockSupermatrixGradedTrace.Parity.sign] using
    InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.supertrace_mul_graded_comm
      .even .even operatorX operatorY operatorX_even operatorY_even

/-- The repository's finite matrix-operator Berezinian law for a block matrix
whose diagonal blocks are the separate matrix exponentials `exp A` and `exp D`.
This theorem does not identify that block matrix with the exponential of the
full block-supermatrix generator. -/
theorem finite_operator_block_exp_ratio_law
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (D : Matrix n n ℝ) :
    InfoGeometry.NCG.BerezinianExponentialSupertrace.blockBerezinian
        (InfoGeometry.NCG.BerezinianExponentialSupertrace.expBlockDiag A D) =
      Real.exp (Matrix.trace A - Matrix.trace D) :=
  InfoGeometry.NCG.BerezinianExponentialSupertrace.blockBerezinian_exp_eq_exp_supertrace_generator A D

/-- Finite operator-block certificate: the homogeneous superbracket identity,
the separate diagonal-block exponential ratio law, and an explicit
noncommuting witness. The scalar-entry Section 46 certificate is separate. -/
structure FiniteOperatorBlockCertificate : Prop where
  block_multiplication_associative :
    ∀ {m n R : Type*} [Fintype m] [Fintype n]
      [DecidableEq m] [DecidableEq n] [CommRing R]
      (X Y Z : InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix
        (m := m) (n := n) (R := R)),
      (X * Y) * Z = X * (Y * Z)
  homogeneous_operator_superbracket :
    ∀ {m n R : Type*} [Fintype m] [Fintype n]
      [DecidableEq m] [DecidableEq n] [CommRing R]
      (p q : InfoGeometry.NCG.BlockSupermatrixGradedTrace.Parity)
      (X Y : InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix
        (m := m) (n := n) (R := R)),
      InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.IsHomogeneous p X →
      InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.IsHomogeneous q Y →
      InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.supertrace
        (InfoGeometry.NCG.BlockSupermatrixGradedTrace.SuperMatrix.superbracket p q X Y) = 0
  finite_operator_block_exponential :
    ∀ {m n : Type*} [Fintype m] [Fintype n]
      [DecidableEq m] [DecidableEq n]
      (A : Matrix m m ℝ) (D : Matrix n n ℝ),
      InfoGeometry.NCG.BerezinianExponentialSupertrace.blockBerezinian
          (InfoGeometry.NCG.BerezinianExponentialSupertrace.expBlockDiag A D) =
        Real.exp (Matrix.trace A - Matrix.trace D)
  explicit_noncommuting_operators : operatorX * operatorY ≠ operatorY * operatorX

/-- Assemble the finite operator-block results in this bridge. -/
theorem compile_finite_operator_block_certificate : FiniteOperatorBlockCertificate where
  block_multiplication_associative := operator_block_mul_assoc
  homogeneous_operator_superbracket := operator_block_superbracket_supertrace_zero
  finite_operator_block_exponential := finite_operator_block_exp_ratio_law
  explicit_noncommuting_operators := concrete_operator_blocks_noncommute

end InfoGeometry.SuperGrassmannian.RealSuperGrassmannianOperatorBlocks
