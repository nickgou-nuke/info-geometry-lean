import InfoGeometry.Lie.SplitOctonionImaginaryAction
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Split-octonion left multiplication as a Clifford representation

This module formalizes one precise and mathematically honest sense in which
split octonions occur in Clifford algebra theory.

The seven-dimensional imaginary split-octonion space acts on the full
eight-dimensional split-octonion carrier by left multiplication. Alternativity
and the composition quadratic identity imply the Clifford square relation, so
Mathlib's universal property produces an algebra homomorphism

`CliffordAlgebra leftCliffordQuadratic →ₐ[ℝ] Module.End ℝ CanonicalZorn`.

The source and target of this homomorphism are associative. The split-octonion
carrier is only the representation module. In particular, this file does not
claim that split octonions form an associative subalgebra of a Clifford algebra,
or that `X ↦ imaginaryLeftMul X` preserves split-octonion multiplication.
-/

noncomputable section
namespace InfoGeometry.Lie.SplitOctonionImaginaryAction

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Algebra.Zorn.CanonicalVectorMatrixBridge
open InfoGeometry.Algebra.Zorn.G2TrifactorSU3

/-- The bilinear form seen by split-octonion left multiplication. The factor
`-1/2` converts determinant polarization to the square of an imaginary
split octonion. -/
noncomputable def leftCliffordBilin : LinearMap.BilinForm ℝ Imaginary :=
  (-1 / 2 : ℝ) • imaginaryPolarBilin

/-- The quadratic form whose Clifford generators act by left multiplication. -/
noncomputable def leftCliffordQuadratic : QuadraticForm ℝ Imaginary :=
  leftCliffordBilin.toQuadraticMap

@[simp] theorem leftCliffordQuadratic_apply (X : Imaginary) :
    leftCliffordQuadratic X = (-1 / 2 : ℝ) * imaginaryPolar X X := by
  simp [leftCliffordQuadratic, leftCliffordBilin, imaginaryPolarBilin_apply]

/-- Left multiplication by imaginary split octonions, bundled as a real-linear
map into the associative endomorphism algebra of the full carrier. -/
noncomputable def imaginaryLeftMul :
    Imaginary →ₗ[ℝ] Module.End ℝ CanonicalZorn where
  toFun X :=
    { toFun := fun Z => X.1 * Z
      map_add' := fun Y Z => mul_add X.1 Y Z
      map_smul' := fun r Z => mul_smul r X.1 Z }
  map_add' X Y := by
    apply LinearMap.ext
    intro Z
    change (X.1 + Y.1) * Z = X.1 * Z + Y.1 * Z
    exact add_mul X.1 Y.1 Z
  map_smul' r X := by
    apply LinearMap.ext
    intro Z
    change (r • X.1) * Z = r • (X.1 * Z)
    exact smul_mul r X.1 Z

/-- An imaginary split octonion squares to the scalar prescribed by the
left-Clifford quadratic form. -/
theorem imaginary_sq_eq_leftCliffordQuadratic (X : Imaginary) :
    X.1 * X.1 = leftCliffordQuadratic X • (1 : CanonicalZorn) := by
  have h := imaginary_anticommutator_eq X X
  change X.1 * X.1 + X.1 * X.1 =
    -(imaginaryPolar X X) • (1 : CanonicalZorn) at h
  apply smul_right_injective CanonicalZorn (show (2 : ℝ) ≠ 0 by norm_num)
  change (2 : ℝ) • (X.1 * X.1) =
    (2 : ℝ) • (leftCliffordQuadratic X • (1 : CanonicalZorn))
  rw [two_smul, two_smul, h, ← add_smul]
  congr 1
  rw [leftCliffordQuadratic_apply]
  ring

/-- The Clifford quadratic form is the negative split-octonion determinant on
the imaginary hyperplane.  This fixes the sign convention of the resulting
split Clifford representation. -/
@[simp] theorem leftCliffordQuadratic_eq_neg_det (X : Imaginary) :
    leftCliffordQuadratic X =
      -ZornMatrix.detZ realCrossProduct3 X.1 := by
  have hquad := realZorn_quadratic X.1
  have htrace : realZornTrace X.1 = 0 := (mem_imaginary_iff X.1).mp X.2
  rw [htrace, zero_smul] at hquad
  change X.1 * X.1 +
    ZornMatrix.detZ realCrossProduct3 X.1 • (1 : CanonicalZorn) = 0 at hquad
  rw [imaginary_sq_eq_leftCliffordQuadratic] at hquad
  rw [← add_smul] at hquad
  have hone : (1 : CanonicalZorn) ≠ 0 := by
    intro h
    have ha := congrArg (fun Z : CanonicalZorn => Z.a) h
    have h1a : (1 : CanonicalZorn).a = 1 := rfl
    have h0a : (0 : CanonicalZorn).a = 0 := rfl
    change (1 : CanonicalZorn).a = (0 : CanonicalZorn).a at ha
    rw [h1a, h0a] at ha
    norm_num at ha
  have hscalar : leftCliffordQuadratic X +
      ZornMatrix.detZ realCrossProduct3 X.1 = 0 := by
    exact (smul_eq_zero.mp hquad).resolve_right hone
  linarith

/-- Left alternativity makes repeated left multiplication equal multiplication
by the square. -/
theorem imaginary_leftMul_self_apply (X : Imaginary) (Z : CanonicalZorn) :
    X.1 * (X.1 * Z) = (X.1 * X.1) * Z := by
  have h := canonical_left_linearized X.1 X.1 Z
  apply smul_right_injective CanonicalZorn (show (2 : ℝ) ≠ 0 by norm_num)
  change (2 : ℝ) • (X.1 * (X.1 * Z)) =
    (2 : ℝ) • ((X.1 * X.1) * Z)
  rw [two_smul, two_smul]
  exact h.symm

/-- The imaginary left-multiplication map satisfies the Clifford square law. -/
theorem imaginaryLeftMul_sq (X : Imaginary) :
    imaginaryLeftMul X * imaginaryLeftMul X =
      algebraMap ℝ (Module.End ℝ CanonicalZorn) (leftCliffordQuadratic X) := by
  apply LinearMap.ext
  intro Z
  rw [Module.End.mul_apply]
  change X.1 * (X.1 * Z) = _
  rw [imaginary_leftMul_self_apply, imaginary_sq_eq_leftCliffordQuadratic]
  rw [smul_mul]
  change leftCliffordQuadratic X • zMul (1 : CanonicalZorn) Z =
    leftCliffordQuadratic X • Z
  rw [one_zMul]

/-- Native Mathlib Clifford representation on the eight-dimensional
split-octonion carrier. This is an operator representation, not an embedding of
the nonassociative split-octonion algebra as an associative subalgebra. -/
noncomputable def splitOctonionLeftCliffordRepresentation :
    CliffordAlgebra leftCliffordQuadratic →ₐ[ℝ] Module.End ℝ CanonicalZorn :=
  CliffordAlgebra.lift leftCliffordQuadratic ⟨imaginaryLeftMul, imaginaryLeftMul_sq⟩

@[simp] theorem splitOctonionLeftCliffordRepresentation_ι (X : Imaginary) :
    splitOctonionLeftCliffordRepresentation
        (CliffordAlgebra.ι leftCliffordQuadratic X) = imaginaryLeftMul X := by
  exact CliffordAlgebra.lift_ι_apply _ _ X

/-- The operator anticommutator is exactly the polar form of the Clifford
quadratic form. -/
theorem imaginaryLeftMul_anticommutator (X Y : Imaginary) :
    imaginaryLeftMul X * imaginaryLeftMul Y +
        imaginaryLeftMul Y * imaginaryLeftMul X =
      algebraMap ℝ (Module.End ℝ CanonicalZorn)
        (QuadraticMap.polar leftCliffordQuadratic X Y) := by
  have h := congrArg splitOctonionLeftCliffordRepresentation
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := leftCliffordQuadratic) X Y)
  simpa using h

end InfoGeometry.Lie.SplitOctonionImaginaryAction
