import Mathlib.Tactic
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import InfoGeometry.Algebra.Zorn.Concrete
import InfoGeometry.Quantum.PauliSoldering

/-!
# Chiral-cone Pauli/Clifford soldering

The split-Zorn carrier has two scalar/vector rails.  This file resolves each
rail into the existing Pauli basis.  The result is a faithful operator readout;
it does not identify associative matrix multiplication with Zorn multiplication.
-/

noncomputable section

namespace InfoGeometry.Canonical.ChiralConePauliCliffordSoldering

open InfoGeometry.Algebra.Zorn.Concrete
open InfoGeometry.Quantum.PauliSoldering

abbrev RailOperator := Matrix (Fin 2) (Fin 2) ℂ

abbrev Vec3R := Fin 3 → ℝ

/-! The real `Cl₃` coordinate decomposition
`Λ⁰ ⊕ Λ¹ ⊕ Λ² ⊕ Λ³ = 1 + 3 + 3 + 1`. -/
structure Cl3GradeCoordinates where
  scalar : ℝ
  vector : Vec3R
  bivector : Vec3R
  pseudoscalar : ℝ

def zornToCl3 (X : ZornCell ℝ) : Cl3GradeCoordinates where
  scalar := (X.r + X.s) / 2
  vector := ![X.x1, X.x2, X.x3]
  bivector := ![X.y1, X.y2, X.y3]
  pseudoscalar := (X.r - X.s) / 2

def cl3ToZorn (A : Cl3GradeCoordinates) : ZornCell ℝ where
  r := A.scalar + A.pseudoscalar
  s := A.scalar - A.pseudoscalar
  x1 := A.vector 0
  x2 := A.vector 1
  x3 := A.vector 2
  y1 := A.bivector 0
  y2 := A.bivector 1
  y3 := A.bivector 2

theorem cl3ToZorn_zornToCl3 (X : ZornCell ℝ) :
    cl3ToZorn (zornToCl3 X) = X := by
  rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
  simp [cl3ToZorn, zornToCl3]
  constructor <;> ring

theorem zornToCl3_cl3ToZorn (A : Cl3GradeCoordinates) :
    zornToCl3 (cl3ToZorn A) = A := by
  rcases A with ⟨a, x, y, b⟩
  simp [zornToCl3, cl3ToZorn]
  constructor <;> funext i <;> fin_cases i <;> rfl

theorem cl3ToZorn_injective :
    Function.Injective cl3ToZorn := by
  intro A B h
  rcases A with ⟨a, x, y, b⟩
  rcases B with ⟨c, u, v, d⟩
  have ha : a = c := by
    have h₁ := congrArg (fun Z : ZornCell ℝ => Z.r) h
    have h₂ := congrArg (fun Z : ZornCell ℝ => Z.s) h
    simp [cl3ToZorn] at h₁ h₂
    linarith
  have hb : b = d := by
    have h₁ := congrArg (fun Z : ZornCell ℝ => Z.r) h
    have h₂ := congrArg (fun Z : ZornCell ℝ => Z.s) h
    simp [cl3ToZorn] at h₁ h₂
    linarith
  have hx : x = u := by
    funext i
    fin_cases i
    · simpa [cl3ToZorn] using congrArg (fun Z : ZornCell ℝ => Z.x1) h
    · simpa [cl3ToZorn] using congrArg (fun Z : ZornCell ℝ => Z.x2) h
    · simpa [cl3ToZorn] using congrArg (fun Z : ZornCell ℝ => Z.x3) h
  have hy : y = v := by
    funext i
    fin_cases i
    · simpa [cl3ToZorn] using congrArg (fun Z : ZornCell ℝ => Z.y1) h
    · simpa [cl3ToZorn] using congrArg (fun Z : ZornCell ℝ => Z.y2) h
    · simpa [cl3ToZorn] using congrArg (fun Z : ZornCell ℝ => Z.y3) h
  cases ha
  cases hb
  cases hx
  cases hy
  simp_all

theorem zornToCl3_injective :
    Function.Injective zornToCl3 := by
  intro X Y h
  have := congrArg cl3ToZorn h
  simpa [cl3ToZorn_zornToCl3] using this

theorem zornToCl3_eq_iff (X Y : ZornCell ℝ) :
    zornToCl3 X = zornToCl3 Y ↔ X = Y := by
  constructor
  · intro h
    exact zornToCl3_injective h
  · intro h
    simpa [h]

def railSolder (u s₁ s₂ s₃ : ℂ) : RailOperator :=
  solder (u, s₁, s₂, s₃)

def plusRail (X : ZornCell ℂ) : RailOperator :=
  railSolder X.r X.x1 X.x2 X.x3

def minusRail (X : ZornCell ℂ) : RailOperator :=
  railSolder X.s X.y1 X.y2 X.y3

def chiralConeSolder (X : ZornCell ℂ) : RailOperator × RailOperator :=
  (plusRail X, minusRail X)

/-! The real `Cl₃` packet is presented in the Pauli algebra by
`(a + I b) 1 + Σᵢ (xᵢ + I yᵢ) σᵢ`.

This is a presentation/readout map, not a claim that the split-octonion
product is represented by associative matrix multiplication. -/
def cl3PauliOperator (A : Cl3GradeCoordinates) : RailOperator :=
  railSolder
    (A.scalar + Complex.I * A.pseudoscalar)
    (A.vector 0 + Complex.I * A.bivector 0)
    (A.vector 1 + Complex.I * A.bivector 1)
    (A.vector 2 + Complex.I * A.bivector 2)

theorem railSolder_explicit (u s₁ s₂ s₃ : ℂ) :
    railSolder u s₁ s₂ s₃ =
      !![u + s₃, s₁ - Complex.I * s₂;
         s₁ + Complex.I * s₂, u - s₃] := by
  exact solder_explicit u s₁ s₂ s₃

theorem plusRail_explicit (X : ZornCell ℂ) :
    plusRail X =
      !![X.r + X.x3, X.x1 - Complex.I * X.x2;
         X.x1 + Complex.I * X.x2, X.r - X.x3] := by
  exact railSolder_explicit X.r X.x1 X.x2 X.x3

theorem minusRail_explicit (X : ZornCell ℂ) :
    minusRail X =
      !![X.s + X.y3, X.y1 - Complex.I * X.y2;
         X.y1 + Complex.I * X.y2, X.s - X.y3] := by
  exact railSolder_explicit X.s X.y1 X.y2 X.y3

theorem cl3PauliOperator_explicit (A : Cl3GradeCoordinates) :
    cl3PauliOperator A =
      !![ A.scalar + Complex.I * A.pseudoscalar
            + (A.vector 2 + Complex.I * A.bivector 2),
          (A.vector 0 + Complex.I * A.bivector 0)
            - Complex.I * (A.vector 1 + Complex.I * A.bivector 1);
          (A.vector 0 + Complex.I * A.bivector 0)
            + Complex.I * (A.vector 1 + Complex.I * A.bivector 1),
          A.scalar + Complex.I * A.pseudoscalar
            - (A.vector 2 + Complex.I * A.bivector 2)] := by
  exact railSolder_explicit _ _ _ _

theorem cl3PauliOperator_injective :
    Function.Injective cl3PauliOperator := by
  intro A B h
  have h' := congrArg (fun M : RailOperator =>
    !![M 0 0, M 0 1; M 1 0, M 1 1]) h
  simp only [cl3PauliOperator, railSolder_explicit] at h'
  rcases A with ⟨a, x, y, b⟩
  rcases B with ⟨c, u, v, d⟩
  simp at h'
  rcases h' with ⟨⟨h00, h01⟩, h10, h11⟩
  have h00r := congrArg Complex.re h00
  have h00i := congrArg Complex.im h00
  have h01r := congrArg Complex.re h01
  have h01i := congrArg Complex.im h01
  have h10r := congrArg Complex.re h10
  have h10i := congrArg Complex.im h10
  have h11r := congrArg Complex.re h11
  have h11i := congrArg Complex.im h11
  simp at h00r h00i h01r h01i h10r h10i h11r h11i
  have ha : a = c := by linear_combination (h00r + h11r) / 2
  have hb : b = d := by linear_combination (h00i + h11i) / 2
  have hx : x = u := by
    funext i
    fin_cases i
    · change x 0 = u 0
      linear_combination (h01r + h10r) / 2
    · change x 1 = u 1
      linear_combination (h10i - h01i) / 2
    · change x 2 = u 2
      linear_combination (h00r - h11r) / 2
  have hy : y = v := by
    funext i
    fin_cases i
    · change y 0 = v 0
      linear_combination (h01i + h10i) / 2
    · change y 1 = v 1
      linear_combination (h01r - h10r) / 2
    · change y 2 = v 2
      linear_combination (h00i - h11i) / 2
  cases ha
  cases hb
  cases hx
  cases hy
  rfl

theorem cl3PauliOperator_eq_zero_iff (A : Cl3GradeCoordinates) :
    cl3PauliOperator A = 0 ↔
      A.scalar = 0 ∧ A.vector = 0 ∧ A.bivector = 0 ∧ A.pseudoscalar = 0 := by
  let Z : Cl3GradeCoordinates :=
    { scalar := 0, vector := 0, bivector := 0, pseudoscalar := 0 }
  have hZ : cl3PauliOperator Z = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Z, cl3PauliOperator, railSolder_explicit]
  constructor
  · intro h
    have hA : A = Z := cl3PauliOperator_injective (h.trans hZ.symm)
    simpa using congrArg (fun B : Cl3GradeCoordinates =>
      (B.scalar, B.vector, B.bivector, B.pseudoscalar)) hA
  · rintro ⟨ha, hx, hy, hb⟩
    have hA : A = Z := by
      rcases A with ⟨a, x, y, b⟩
      simp_all [Z]
    rw [hA]
    exact hZ

theorem railSolder_reconstruct (u s₁ s₂ s₃ : ℂ) :
    railSolder u s₁ s₂ s₃ =
      (u + s₃) • !![1, 0; 0, 0] +
      (s₁ - Complex.I * s₂) • !![0, 1; 0, 0] +
      (s₁ + Complex.I * s₂) • !![0, 0; 1, 0] +
      (u - s₃) • !![0, 0; 0, 1] := by
  rw [railSolder_explicit]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem chiralConeSolder_injective :
    Function.Injective chiralConeSolder := by
  intro X Y h
  rcases X with ⟨xr, xs, xx1, xx2, xx3, xy1, xy2, xy3⟩
  rcases Y with ⟨yr, ys, yx1, yx2, yx3, yy1, yy2, yy3⟩
  simp [chiralConeSolder, plusRail, minusRail, railSolder,
    solder_explicit] at h
  rcases h with ⟨hplus, hminus⟩
  rcases hplus with ⟨⟨h00, h01⟩, h10, h11⟩
  rcases hminus with ⟨⟨k00, k01⟩, k10, k11⟩
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  congr
  · linear_combination (h00 + h11) / 2
  · linear_combination (k00 + k11) / 2
  · linear_combination (h01 + h10) / 2
  · apply (mul_left_cancel₀ hI)
    linear_combination (h10 - h01) / 2
  · linear_combination (h00 - h11) / 2
  · linear_combination (k01 + k10) / 2
  · apply (mul_left_cancel₀ hI)
    linear_combination (k10 - k01) / 2
  · linear_combination (k00 - k11) / 2

/-! ## The complex eight-coordinate carrier and the tensor/Clifford quotient

The tensor algebra is free and associative; `CliffordAlgebra` is reached by
sending a tensor generator to the native Clifford generator.  No
multiplication claim about the nonassociative Zorn carrier is made here.
-/

def zornComplexCoordinates (X : ZornCell ℂ) : Fin 8 → ℂ :=
  ![X.r, X.s, X.x1, X.x2, X.x3, X.y1, X.y2, X.y3]

def fin8ToZorn (x : Fin 8 → ℂ) : ZornCell ℂ :=
    { r := x 0
      s := x 1
      x1 := x 2
      x2 := x 3
      x3 := x 4
      y1 := x 5
      y2 := x 6
      y3 := x 7 }

def zornComplexCoordinateEquiv : ZornCell ℂ ≃ (Fin 8 → ℂ) :=
  { toFun := zornComplexCoordinates
    invFun := fin8ToZorn
    left_inv := by
      intro X
      rcases X with ⟨r, s, x1, x2, x3, y1, y2, y3⟩
      rfl
    right_inv := by
      intro x
      funext i
      fin_cases i <;> rfl }

abbrev Cl3Vector := Fin 3 → ℂ

def cl3Dot (x y : Cl3Vector) : ℂ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

noncomputable def cl3Quadratic : QuadraticForm ℂ Cl3Vector :=
  Matrix.toQuadraticMap' (Matrix.diagonal (fun _ : Fin 3 => (1 : ℂ)))

theorem cl3Quadratic_apply (x : Cl3Vector) :
    cl3Quadratic x = cl3Dot x x := by
  simp [cl3Quadratic, cl3Dot, Matrix.toQuadraticMap',
    Matrix.toLinearMap₂'_apply, Matrix.diagonal, Fin.sum_univ_three]

def cl3Generator (x : Cl3Vector) : CliffordAlgebra cl3Quadratic :=
  CliffordAlgebra.ι cl3Quadratic x

noncomputable def cl3TensorToClifford :
    TensorAlgebra ℂ Cl3Vector →ₐ[ℂ] CliffordAlgebra cl3Quadratic :=
  TensorAlgebra.lift ℂ (CliffordAlgebra.ι cl3Quadratic)

@[simp] theorem cl3TensorToClifford_ι (x : Cl3Vector) :
    cl3TensorToClifford (TensorAlgebra.ι ℂ x) = cl3Generator x := by
  exact TensorAlgebra.lift_ι_apply _ x

theorem cl3Generator_square (x : Cl3Vector) :
    cl3Generator x * cl3Generator x =
      algebraMap ℂ (CliffordAlgebra cl3Quadratic) (cl3Quadratic x) := by
  exact CliffordAlgebra.ι_sq_scalar _ _

theorem cl3Tensor_square_relation (x : Cl3Vector) :
    cl3TensorToClifford
        (TensorAlgebra.ι ℂ x * TensorAlgebra.ι ℂ x) =
      algebraMap ℂ (CliffordAlgebra cl3Quadratic) (cl3Quadratic x) := by
  rw [map_mul, cl3TensorToClifford_ι, cl3Generator_square]

end InfoGeometry.Canonical.ChiralConePauliCliffordSoldering

end noncomputable section
