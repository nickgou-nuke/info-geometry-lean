import Mathlib
import InfoGeometry.Algebra.F4Derivations
import InfoGeometry.Algebra.H3ZornJordanIdentity

noncomputable section

namespace InfoGeometry.Canonical.H3ZornAlgebraicSoldering

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn

abbrev Zorn := ZornVectorMatrix ℝ
abbrev H3 := H3Zorn ℝ

/-- Six-lane Peirce coordinate carrier with the native module structure coming
from products. -/
abbrev H3Coord := ℝ × (ℝ × (ℝ × (Zorn × (Zorn × Zorn))))

/-- Algebraic soldering from six Peirce coordinate lanes to the native
`H3Zorn` carrier. -/
noncomputable def h3Soldering : H3Coord ≃ₗ[ℝ] H3 where
  toFun X :=
    { α₁ := X.1
      α₂ := X.2.1
      α₃ := X.2.2.1
      a := X.2.2.2.1
      b := X.2.2.2.2.1
      c := X.2.2.2.2.2 }
  invFun X := (X.α₁, (X.α₂, (X.α₃, (X.a, (X.b, X.c)))))
  left_inv X := by rcases X with ⟨a1,a2,a3,a,b,c⟩; rfl
  right_inv X := by cases X; rfl
  map_add' X Y := by rfl
  map_smul' r X := by rfl

@[simp] theorem h3Soldering_apply
    (a1 a2 a3 : ℝ) (a b c : Zorn) :
    h3Soldering (a1, (a2, (a3, (a, (b, c))))) =
      ({ α₁ := a1, α₂ := a2, α₃ := a3, a := a, b := b, c := c } : H3) := rfl

/-- Coordinate Jordan multiplication is the pullback of the installed native
split-Albert Jordan product along the soldering.  This definition makes the
algebraic content of the soldering explicit instead of treating it as a bare
linear equivalence. -/
noncomputable def coordJordanMul (X Y : H3Coord) : H3Coord :=
  h3Soldering.symm (candidateJordanMul (h3Soldering X) (h3Soldering Y))

/-- The soldering intertwines the coordinate and native Jordan products. -/
@[simp] theorem h3Soldering_jordan_intertwines (X Y : H3Coord) :
    h3Soldering (coordJordanMul X Y) =
      candidateJordanMul (h3Soldering X) (h3Soldering Y) := by
  simp [coordJordanMul]

/-- The inverse soldering also preserves the product. -/
@[simp] theorem h3Soldering_symm_jordan_intertwines (X Y : H3) :
    h3Soldering.symm (candidateJordanMul X Y) =
      coordJordanMul (h3Soldering.symm X) (h3Soldering.symm Y) := by
  simp [coordJordanMul]

/-- Generic transport-of-derivations lemma through a product-preserving linear
equivalence.  This is the reusable algebraic soldering principle. -/
theorem jordanDerivation_transport
    {A J : Type*}
    [AddCommGroup A] [Module ℝ A]
    [AddCommGroup J] [Module ℝ J]
    (coordMul : A → A → A) (jordanMul : J → J → J)
    (S : A ≃ₗ[ℝ] J)
    (hS : ∀ x y, S (coordMul x y) = jordanMul (S x) (S y))
    (D : Module.End ℝ A)
    (hD : ∀ x y, D (coordMul x y) =
      coordMul (D x) y + coordMul x (D y)) :
    let Dhat : Module.End ℝ J :=
      S.toLinearMap.comp (D.comp S.symm.toLinearMap)
    ∀ x y : J,
      Dhat (jordanMul x y) =
        jordanMul (Dhat x) y + jordanMul x (Dhat y) := by
  intro Dhat x y
  have hsymm :
      S.symm (jordanMul x y) =
        coordMul (S.symm x) (S.symm y) := by
    apply S.injective
    simp [hS]
  change S (D (S.symm (jordanMul x y))) = _
  rw [hsymm, hD, map_add, hS, hS]
  simp

/-- Specialization of generic transport to the split-Albert soldering. -/
theorem h3JordanDerivation_transport
    (D : Module.End ℝ H3Coord)
    (hD : ∀ x y, D (coordJordanMul x y) =
      coordJordanMul (D x) y + coordJordanMul x (D y)) :
    H3ZornJordanDerivation
      (h3Soldering.toLinearMap.comp
        (D.comp h3Soldering.symm.toLinearMap)) := by
  simpa [H3ZornJordanDerivation, candidateJordanMul_eq_mul] using
    (jordanDerivation_transport coordJordanMul candidateJordanMul
      h3Soldering h3Soldering_jordan_intertwines D hD)

end InfoGeometry.Canonical.H3ZornAlgebraicSoldering
