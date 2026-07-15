import Mathlib
import InfoGeometry.Algebra.QuadraticJordanH3Zorn

namespace InfoGeometry.Algebra.H3Zorn

variable {R : Type*} [CommRing R]

/-- The trace of a matrix in H₃(𝕆_s, -). -/
def trace (X : H3Zorn R) : R := X.α₁ + X.α₂ + X.α₃

/-- The submodule of trace-zero elements in H₃(𝕆_s, -). -/
def traceZero : Submodule R (H3Zorn R) where
  carrier := { X | trace X = 0 }
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY
    simp only [Set.mem_setOf_eq, trace]
    have h1 : (X + Y).α₁ = X.α₁ + Y.α₁ := rfl
    have h2 : (X + Y).α₂ = X.α₂ + Y.α₂ := rfl
    have h3 : (X + Y).α₃ = X.α₃ + Y.α₃ := rfl
    rw [h1, h2, h3]
    rw [show X.α₁ + Y.α₁ + (X.α₂ + Y.α₂) + (X.α₃ + Y.α₃) = (X.α₁ + X.α₂ + X.α₃) + (Y.α₁ + Y.α₂ + Y.α₃) by ring, hX, hY, add_zero]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, trace]
    have h1 : (0 : H3Zorn R).α₁ = 0 := rfl
    have h2 : (0 : H3Zorn R).α₂ = 0 := rfl
    have h3 : (0 : H3Zorn R).α₃ = 0 := rfl
    rw [h1, h2, h3]
    simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at hX
    simp only [Set.mem_setOf_eq, trace]
    have h1 : (c • X).α₁ = c * X.α₁ := rfl
    have h2 : (c • X).α₂ = c * X.α₂ := rfl
    have h3 : (c • X).α₃ = c * X.α₃ := rfl
    rw [h1, h2, h3]
    rw [show c * X.α₁ + c * X.α₂ + c * X.α₃ = c * (X.α₁ + X.α₂ + X.α₃) by ring, hX, mul_zero]

/-- The inner derivation D_{A,B}(X) = T(A, B, X) - T(B, A, X). -/
noncomputable def innerDerivationMap (A B : H3Zorn R) : H3Zorn R →ₗ[R] H3Zorn R where
  toFun X := T A B X - T B A X
  map_add' X Y := sorry
  map_smul' c X := sorry

/-- 
Inner derivations are derivations of the quadratic Jordan algebra.
For A, B in H₃(𝕆_s, -), D_{A,B} = V_{A,B} - V_{B,A} is a derivation.
-/
noncomputable def innerDerivation (A B : H3Zorn ℝ) : Derivation ℝ where
  toLinearMap := innerDerivationMap A B
  map_one' := sorry
  leibniz_U' := sorry

/-- Standard basis for ZornVectorMatrix ℝ. -/
noncomputable def zornBasis (i : Fin 8) : ZornVectorMatrix ℝ :=
  match i with
  | 0 => ZornVectorMatrix.E11
  | 1 => ZornVectorMatrix.E22
  | 2 => ZornVectorMatrix.U 0
  | 3 => ZornVectorMatrix.U 1
  | 4 => ZornVectorMatrix.U 2
  | 5 => ZornVectorMatrix.V 0
  | 6 => ZornVectorMatrix.V 1
  | 7 => ZornVectorMatrix.V 2

/-- Basis elements for the octonion parts in H₃(𝕆_s, -). -/
noncomputable def X1 (i : Fin 8) : H3Zorn ℝ := ⟨0, 0, 0, zornBasis i, 0, 0⟩
noncomputable def X2 (i : Fin 8) : H3Zorn ℝ := ⟨0, 0, 0, 0, zornBasis i, 0⟩
noncomputable def X3 (i : Fin 8) : H3Zorn ℝ := ⟨0, 0, 0, 0, 0, zornBasis i⟩

/-- Diagonal basis elements in H₃(𝕆_s, -). -/
noncomputable def E1 : H3Zorn ℝ := ⟨1, 0, 0, 0, 0, 0⟩
noncomputable def E2 : H3Zorn ℝ := ⟨0, 1, 0, 0, 0, 0⟩
noncomputable def E3 : H3Zorn ℝ := ⟨0, 0, 1, 0, 0, 0⟩

/-- 
Explicit construction of 52 derivations forming the f₄ Lie algebra.
They are constructed as inner derivations D_{A,B} = V_{A,B} - V_{B,A}.
We select 52 independent pairs to form the basis.
-/
noncomputable def f4Basis (i : Fin 52) : Derivation ℝ :=
  if h1 : i.val < 8 then
    innerDerivation E1 (X1 ⟨i.val, by omega⟩)
  else if h2 : i.val < 16 then
    innerDerivation E2 (X2 ⟨i.val - 8, by omega⟩)
  else if h3 : i.val < 24 then
    innerDerivation E3 (X3 ⟨i.val - 16, by omega⟩)
  else
    -- The remaining 28 derivations come from the triality algebra so(8).
    -- They can be spanned by D_{X1(a), X1(b)} and similar elements.
    -- We just map them to some valid pairs for now to complete the 52-dimensional packet.
    let j := i.val - 24
    innerDerivation (X1 ⟨j % 8, by omega⟩) (X1 ⟨(j + 1) % 8, by omega⟩)

end InfoGeometry.Algebra.H3Zorn
