import InfoGeometry.Algebra.ZornMatrix
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# One real vector carrier, two genuinely different multiplication laws

The common associative core is the native matrix algebra `M₂(ℝ)`. Its
complexification `M₂(ℂ)` and the native real Zorn algebra are linearly
isomorphic, but not multiplicatively isomorphic. We exhibit the linear
isomorphism, the common core, both doubling laws, and a concrete associator.

The map replaces the central scalar `i` by a Cayley--Dickson generator `ell`.
It preserves real linear structure, not multiplication. The equality `ell²=1`
is incompatible with interpreting `ell` as a supercommutative odd scalar.
-/

noncomputable section

namespace InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation

open InfoGeometry.Algebra

abbrev RealCore := Matrix (Fin 2) (Fin 2) ℝ
abbrev ComplexMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev SplitCarrier := ZornMatrix ℝ

/-- The fixed-axis copy of `M₂(ℝ)` in the native Zorn algebra. -/
def core (A : RealCore) : SplitCarrier where
  a := A 0 0
  v := ![A 0 1, 0, 0]
  w := ![A 1 0, 0, 0]
  b := A 1 1

/-- The split-quaternion conjugation, i.e. the two-by-two adjugate. -/
def coreConj (A : RealCore) : RealCore :=
  !![A 1 1, -A 0 1; -A 1 0, A 0 0]

/-- The Cayley--Dickson generator orthogonal to the fixed-axis core. -/
def ell : SplitCarrier := ZornMatrix.U 1 + ZornMatrix.V 1

/-- Complexification with a CENTRAL scalar square root of minus one. -/
def complexDouble (A B : RealCore) : ComplexMatrix :=
  fun i j => ⟨A i j, B i j⟩

/-- Cayley--Dickson doubling with right coefficient convention `A + B ell`. -/
def splitDouble (A B : RealCore) : SplitCarrier := core A + core B * ell

/-- The two complementary four-dimensional summands cover the native Zorn carrier. -/
theorem splitDouble_coordinates (A B : RealCore) :
    splitDouble A B =
      { a := A 0 0
        v := ![A 0 1, B 0 0, -B 1 0]
        w := ![A 1 0, B 1 1, B 0 1]
        b := A 1 1 } := by
  apply ZornMatrix.ext <;>
    first | (funext i; fin_cases i) | skip
  all_goals
    simp [splitDouble, core, ell, ZornMatrix.U, ZornMatrix.V,
      ZornMatrix.Vec3.basis, ZornMatrix.mul, ZornMatrix.add,
      Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- Multiplication is preserved on the shared split-quaternion core. -/
theorem core_mul (A B : RealCore) : core (A * B) = core A * core B := by
  apply ZornMatrix.ext <;>
    first | (funext i; fin_cases i) | skip
  all_goals
    simp [core, ZornMatrix.mul, Matrix.mul_apply, Fin.sum_univ_two,
      Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

@[simp] theorem core_one : core (1 : RealCore) = ZornMatrix.I := by
  apply ZornMatrix.ext <;>
    first | (funext i; fin_cases i) | skip
  all_goals simp [core, ZornMatrix.I]

/-- The core map is injective, so it really embeds the full four-dimensional algebra. -/
theorem core_injective : Function.Injective core := by
  intro A B h
  have ha := congrArg ZornMatrix.a h
  have hb := congrArg ZornMatrix.b h
  have hv := congrArg (fun Z : SplitCarrier => Z.v 0) h
  have hw := congrArg (fun Z : SplitCarrier => Z.w 0) h
  ext i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hv
  · exact hw
  · exact hb

@[simp] theorem ell_sq : ell * ell = ZornMatrix.I := by
  apply ZornMatrix.ext <;>
    first | (funext i; fin_cases i) | skip
  all_goals
    norm_num [ell, ZornMatrix.U, ZornMatrix.V, ZornMatrix.Vec3.basis,
      ZornMatrix.mul, ZornMatrix.add, ZornMatrix.I,
      Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- The attachment law involves quaternion conjugation, not a universal minus sign. -/
theorem ell_core (A : RealCore) : ell * core A = core (coreConj A) * ell := by
  apply ZornMatrix.ext <;>
    first | (funext i; fin_cases i) | skip
  all_goals
    simp [ell, core, coreConj, ZornMatrix.U, ZornMatrix.V,
      ZornMatrix.Vec3.basis, ZornMatrix.mul, ZornMatrix.add,
      Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul]

/-- Quaternion conjugation negates precisely the trace-zero core. -/
theorem coreConj_eq_neg_of_trace_zero (A : RealCore) (h : Matrix.trace A = 0) :
    coreConj A = -A := by
  have hd : A 0 0 + A 1 1 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coreConj] <;> linarith

/-- The associative central-complex doubling law. -/
theorem complexDouble_mul (A B C D : RealCore) :
    complexDouble A B * complexDouble C D =
      complexDouble (A * C - B * D) (A * D + B * C) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [complexDouble, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- The ACTUAL native Zorn product gives this Cayley--Dickson doubling law.
Conjugation and reversal of factor order are essential. -/
theorem splitDouble_mul (A B C D : RealCore) :
    splitDouble A B * splitDouble C D =
      splitDouble (A * C + coreConj D * B) (D * A + B * coreConj C) := by
  simp only [splitDouble_coordinates]
  apply ZornMatrix.ext <;>
    first | (funext i; fin_cases i) | skip
  all_goals
    simp [coreConj, ZornMatrix.mul, Matrix.mul_apply, Fin.sum_univ_two,
      Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] <;> ring

/-- Replace the central complex direction by the split doubling direction. -/
def matrixToSplit (M : ComplexMatrix) : SplitCarrier where
  a := (M 0 0).re
  v := ![(M 0 1).re, (M 0 0).im, -(M 1 0).im]
  w := ![(M 1 0).re, (M 1 1).im, (M 0 1).im]
  b := (M 1 1).re

/-- The inverse real-coordinate map, with no multiplication claim. -/
def splitToMatrix (Z : SplitCarrier) : ComplexMatrix :=
  !![⟨Z.a, Z.v 1⟩, ⟨Z.v 0, Z.w 2⟩;
     ⟨Z.w 0, -Z.v 2⟩, ⟨Z.b, Z.w 1⟩]

/-- Exact real-linear equivalence of the two eight-dimensional carriers. -/
def matrixSplitLinearEquiv : ComplexMatrix ≃ₗ[ℝ] SplitCarrier where
  toFun := matrixToSplit
  invFun := splitToMatrix
  left_inv M := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      apply Complex.ext <;> simp [matrixToSplit, splitToMatrix]
  right_inv Z := by
    apply ZornMatrix.ext
    · rfl
    · funext i; fin_cases i <;> simp [matrixToSplit, splitToMatrix]
    · funext i; fin_cases i <;> simp [matrixToSplit, splitToMatrix]
    · rfl
  map_add' M N := by
    apply ZornMatrix.ext <;>
      first | (funext i; fin_cases i) | skip
    all_goals simp [matrixToSplit, ZornMatrix.add, Vec3.add] <;> ring
  map_smul' r M := by
    apply ZornMatrix.ext <;>
      first | (funext i; fin_cases i) | skip
    all_goals simp [matrixToSplit, ZornMatrix.smul, Vec3.smul] <;> ring

/-- The complex matrix algebra has real dimension eight. -/
theorem complexMatrix_finrank : Module.finrank ℝ ComplexMatrix = 8 := by
  simp [ComplexMatrix, Module.finrank_matrix]

/-- The native split-octonion carrier has the same REAL dimension. -/
theorem splitCarrier_finrank : Module.finrank ℝ SplitCarrier = 8 := by
  rw [← matrixSplitLinearEquiv.finrank_eq]
  exact complexMatrix_finrank

/-- The linear equivalence carries the central doubling to the split doubling. -/
theorem matrixSplitLinearEquiv_double (A B : RealCore) :
    matrixSplitLinearEquiv (complexDouble A B) = splitDouble A B := by
  rw [splitDouble_coordinates]
  rfl

/-- The central complex generator is sent to `ell` by the linear map. -/
theorem matrixSplitLinearEquiv_I :
    matrixSplitLinearEquiv (Complex.I • (1 : ComplexMatrix)) = ell := by
  apply ZornMatrix.ext <;>
    first | (funext i; fin_cases i) | skip
  all_goals
    simp [matrixSplitLinearEquiv, matrixToSplit, ell,
      ZornMatrix.U, ZornMatrix.V, ZornMatrix.add,
      ZornMatrix.Vec3.basis, Vec3.add]

/-- Left and right reassociations of a native Zorn triple have different diagonal entries. -/
theorem native_associator_witness :
    ((ZornMatrix.U 0 : SplitCarrier) * ZornMatrix.U 1) * ZornMatrix.U 2 ≠
      ZornMatrix.U 0 * (ZornMatrix.U 1 * ZornMatrix.U 2) := by
  intro h
  have ha := congrArg ZornMatrix.a h
  norm_num [ZornMatrix.mul, ZornMatrix.U, ZornMatrix.Vec3.basis,
    Vec3.dot, Vec3.cross, Vec3.add, Vec3.sub, Vec3.smul] at ha

/-- No surjective multiplicative map from an associative matrix algebra can
land in the full native Zorn algebra. This is stronger than failure of one
chosen coordinate identification. -/
theorem no_surjective_multiplicative_matrix_map :
    ¬ ∃ f : ComplexMatrix → SplitCarrier,
      Function.Surjective f ∧ ∀ A B, f (A * B) = f A * f B := by
  rintro ⟨f, hsurj, hmul⟩
  obtain ⟨A, hA⟩ := hsurj (ZornMatrix.U 0)
  obtain ⟨B, hB⟩ := hsurj (ZornMatrix.U 1)
  obtain ⟨C, hC⟩ := hsurj (ZornMatrix.U 2)
  apply native_associator_witness
  calc
    (ZornMatrix.U 0 * ZornMatrix.U 1) * ZornMatrix.U 2 =
        (f A * f B) * f C := by rw [hA, hB, hC]
    _ = f ((A * B) * C) := by rw [hmul, hmul]
    _ = f (A * (B * C)) := by rw [mul_assoc]
    _ = f A * (f B * f C) := by rw [hmul, hmul]
    _ = ZornMatrix.U 0 * (ZornMatrix.U 1 * ZornMatrix.U 2) := by rw [hA, hB, hC]

/-- In particular the explicit real-linear equivalence is not multiplicative. -/
theorem matrixSplitLinearEquiv_not_multiplicative :
    ¬ ∀ A B : ComplexMatrix,
      matrixSplitLinearEquiv (A * B) =
        matrixSplitLinearEquiv A * matrixSplitLinearEquiv B := by
  intro h
  exact no_surjective_multiplicative_matrix_map
    ⟨matrixSplitLinearEquiv, matrixSplitLinearEquiv.surjective, h⟩

/-- A square-one split generator does NOT satisfy odd supercommutative self-exchange. -/
theorem ell_not_supercommutative_odd : ¬ ell * ell = -(ell * ell) := by
  rw [ell_sq]
  intro h
  have ha := congrArg ZornMatrix.a h
  norm_num [ZornMatrix.I] at ha

end InfoGeometry.Algebra.Zorn.MatrixCayleyDicksonSeparation
