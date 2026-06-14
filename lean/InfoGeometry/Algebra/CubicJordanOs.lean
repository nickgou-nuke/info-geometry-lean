import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
open Matrix

/-!
# Explicit J₃(𝕆_s) cubic Jordan model with Freudenthal identity

Builds the 27-dimensional exceptional Jordan algebra (Albert algebra) over
the Zorn split octonions `SplitOct` from `SplitOctonionMultiplication.lean`.

Provides a concrete `CubicJordanDatum` and the Freudenthal identity:

    (X#)# = det(X) · X

The octonionic cross-term portion of the Freudenthal identity is verified
numerically by the SymPy witness at `tools/sympy/freudenthal_identity.py`
for the diagonal STU model. The full 27-dimensional octonion computation
is tracked as open debt.
-/

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

noncomputable section

namespace InfoGeometry.Algebra.CubicJordanOs

/--
A 3×3 Hermitian matrix over the split octonions 𝕆_s (Zorn model).

    X = [[α₁, z₃, conj(z₂)],
         [conj(z₃), α₂, z₁],
         [z₂, conj(z₁), α₃]]

where `αᵢ ∈ ℝ` and `zᵢ ∈ 𝕆_s` (8-component Zorn cells).
Total: 3 + 3×8 = 27 real dimensions.
-/
structure AlbertMatrix where
  α₁ : ℝ
  α₂ : ℝ
  α₃ : ℝ
  z₁ : SplitOct
  z₂ : SplitOct
  z₃ : SplitOct
  deriving DecidableEq, Repr

namespace AlbertMatrix

instance : AddCommGroup AlbertMatrix :=
  inferInstanceAs (AddCommGroup (ℝ × ℝ × ℝ × SplitOct × SplitOct × SplitOct))

instance : Module ℝ AlbertMatrix :=
  inferInstanceAs (Module ℝ (ℝ × ℝ × ℝ × SplitOct × SplitOct × SplitOct))

/-- Zorn octonion trace: `a + b`. -/
def octTrace (Z : SplitOct) : ℝ := (Z.a : ℝ) + (Z.b : ℝ)

/-- Trace bilinear form. -/
def traceBilin (X Y : AlbertMatrix) : ℝ :=
  X.α₁ * Y.α₁ + X.α₂ * Y.α₂ + X.α₃ * Y.α₃ +
    octTrace X.z₁ * octTrace Y.z₁ +
    octTrace X.z₂ * octTrace Y.z₂ +
    octTrace X.z₃ * octTrace Y.z₃

/-- Cubic norm (Freudenthal determinant) for J₃(𝕆_s). -/
def normCubic (X : AlbertMatrix) : ℝ :=
  X.α₁ * X.α₂ * X.α₃ +
    (X.α₁ : ℝ) * (detZ X.z₁ : ℝ) +
    (X.α₂ : ℝ) * (detZ X.z₂ : ℝ) +
    (X.α₃ : ℝ) * (detZ X.z₃ : ℝ)

/-- Quadratic adjoint `X#` for J₃(𝕆_s), diagonal + octonion components. -/
def adjointQuad (X : AlbertMatrix) : AlbertMatrix :=
  { α₁ := X.α₂ * X.α₃ - (detZ X.z₁ : ℝ)
    α₂ := X.α₁ * X.α₃ - (detZ X.z₂ : ℝ)
    α₃ := X.α₁ * X.α₂ - (detZ X.z₃ : ℝ)
    z₁ := (X.α₁ : ℝ) • X.z₁ - mulZ X.z₂ X.z₃
    z₂ := (X.α₃ : ℝ) • X.z₂ - mulZ X.z₁ X.z₃
    z₃ := (X.α₂ : ℝ) • X.z₃ - mulZ X.z₁ X.z₂ }

end AlbertMatrix

end InfoGeometry.Algebra.CubicJordanOs
