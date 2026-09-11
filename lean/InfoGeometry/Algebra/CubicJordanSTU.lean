import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

/-!
# Diagonal STU model: Freudenthal identity (X#)# = N(X)·X

Simplified proof of the core cubic Jordan identity for the diagonal STU
subalgebra of J₃(𝕆_s).  All off-diagonal octonion entries are zero.

The formulas:
  N(X) = α₁·α₂·α₃
  (X#)ᵢ = αⱼ·αₖ   (cyclic, e.g. (X#)₁ = α₂·α₃)
  ((X#)#)ᵢ = (α₁·α₂·α₃)·αᵢ = N(X)·αᵢ
-/

namespace InfoGeometry.Algebra.CubicJordanSTU

/-- Diagonal STU matrix X = diag(α₁, α₂, α₃). -/
structure DiagonalSTU where
  α₁ : ℝ
  α₂ : ℝ
  α₃ : ℝ

namespace DiagonalSTU

/-- Extensionality: two STU matrices equal iff all coordinates equal. -/
@[ext]
theorem ext (x y : DiagonalSTU) (h₁ : x.α₁ = y.α₁) (h₂ : x.α₂ = y.α₂) (h₃ : x.α₃ = y.α₃) : x = y := by
  cases x; cases y
  subst h₁; subst h₂; subst h₃; rfl

/-- Scalar multiplication. -/
instance : SMul ℝ DiagonalSTU :=
  ⟨fun r X => ⟨r * X.α₁, r * X.α₂, r * X.α₃⟩⟩

/-- Cubic norm: N(X) = α₁·α₂·α₃. -/
def normCubic (X : DiagonalSTU) : ℝ := X.α₁ * X.α₂ * X.α₃

/-- Quadratic adjoint: (X#)ᵢ = αⱼ·αₖ. -/
def adjointQuad (X : DiagonalSTU) : DiagonalSTU :=
  ⟨X.α₂ * X.α₃, X.α₁ * X.α₃, X.α₁ * X.α₂⟩

/-- Scalar multiplication by coordinates. -/
def smulVec (r : ℝ) (X : DiagonalSTU) : DiagonalSTU :=
  ⟨r * X.α₁, r * X.α₂, r * X.α₃⟩

/--
**Freudenthal identity for the diagonal STU model.**

  `(X#)# = N(X)·X`

For the cubic Albert algebra J₃(𝕆_s), this is the core algebraic identity
governing the cubic norm.  It implies that the U-duality group E₆ preserves
the cubic norm N(X).
-/
theorem freudenthal_identity (X : DiagonalSTU) :
    adjointQuad (adjointQuad X) = smulVec (normCubic X) X := by
  dsimp [adjointQuad, normCubic, smulVec]
  ext <;> ring

/--
The adjoint is a quadratic map: `(c·X)# = c²·X#` for scalars `c ∈ ℝ`.
-/
theorem adjoint_smul (c : ℝ) (X : DiagonalSTU) :
    adjointQuad (smulVec c X) = smulVec (c ^ 2) (adjointQuad X) := by
  dsimp [adjointQuad, smulVec]
  ext <;> ring

end DiagonalSTU

end InfoGeometry.Algebra.CubicJordanSTU
