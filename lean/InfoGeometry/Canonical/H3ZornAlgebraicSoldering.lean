import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding

noncomputable section

namespace InfoGeometry.Canonical.H3ZornAlgebraicSoldering

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Canonical.G2H3ZornEntrywiseEmbedding

/-- A reusable algebraic soldering datum: a linear equivalence together with
binary products on source and target and an exact product intertwining law. -/
structure AlgebraicSoldering
    (A J : Type*) [AddCommGroup A] [Module ℝ A]
    [AddCommGroup J] [Module ℝ J] where
  equiv : A ≃ₗ[ℝ] J
  coordMul : A → A → A
  targetMul : J → J → J
  map_mul : ∀ x y, equiv (coordMul x y) = targetMul (equiv x) (equiv y)

namespace AlgebraicSoldering

variable {A J : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup J] [Module ℝ J]

/-- Transport an endomorphism through an algebraic soldering equivalence. -/
def transportEnd (S : AlgebraicSoldering A J) (D : Module.End ℝ A) :
    Module.End ℝ J :=
  S.equiv.toLinearMap.comp (D.comp S.equiv.symm.toLinearMap)

@[simp] theorem transportEnd_apply
    (S : AlgebraicSoldering A J) (D : Module.End ℝ A) (x : J) :
    S.transportEnd D x = S.equiv (D (S.equiv.symm x)) := rfl

/-- Leibniz transports formally through an algebraic soldering equivalence. -/
theorem derivation_transport
    (S : AlgebraicSoldering A J) (D : Module.End ℝ A)
    (hD : ∀ x y, D (S.coordMul x y) =
      S.coordMul (D x) y + S.coordMul x (D y)) :
    ∀ x y, S.transportEnd D (S.targetMul x y) =
      S.targetMul (S.transportEnd D x) y +
        S.targetMul x (S.transportEnd D y) := by
  intro x y
  rw [transportEnd_apply]
  have hxy : S.equiv.symm (S.targetMul x y) =
      S.coordMul (S.equiv.symm x) (S.equiv.symm y) := by
    apply S.equiv.injective
    simp only [S.equiv.apply_symm_apply]
    simpa only [S.equiv.apply_symm_apply] using
      (S.map_mul (S.equiv.symm x) (S.equiv.symm y)).symm
  rw [hxy, hD]
  rw [map_add, S.map_mul, S.map_mul]
  simp only [S.equiv.apply_symm_apply, transportEnd_apply]

/-- Conversely, target-side Leibniz pulls back through the soldering map. -/
theorem derivation_pullback
    (S : AlgebraicSoldering A J) (D : Module.End ℝ A)
    (hD : ∀ x y, S.transportEnd D (S.targetMul x y) =
      S.targetMul (S.transportEnd D x) y +
        S.targetMul x (S.transportEnd D y)) :
    ∀ x y, D (S.coordMul x y) =
      S.coordMul (D x) y + S.coordMul x (D y) := by
  intro x y
  apply S.equiv.injective
  have hxy : S.equiv.symm (S.targetMul (S.equiv x) (S.equiv y)) =
      S.coordMul x y := by
    apply S.equiv.injective
    simpa only [S.equiv.apply_symm_apply] using
      (S.map_mul x y).symm
  rw [← hxy]
  have h := hD (S.equiv x) (S.equiv y)
  simpa [transportEnd_apply, S.map_mul] using h

end AlgebraicSoldering

/-- Peirce-coordinate carrier `R^3 × O_s^3` underlying `H3Zorn`. -/
abbrev H3Coord :=
  (ℝ × (ℝ × ℝ)) ×
    (InfoGeometry.Algebra.ZornVectorMatrix ℝ ×
      (InfoGeometry.Algebra.ZornVectorMatrix ℝ ×
        InfoGeometry.Algebra.ZornVectorMatrix ℝ))

/-- Explicit soldering of Peirce/Zorn coordinates into the native `H3Zorn`
carrier. -/
noncomputable def h3Soldering : H3Coord ≃ₗ[ℝ] H3Zorn ℝ where
  toFun p :=
    { α₁ := p.1.1
      α₂ := p.1.2.1
      α₃ := p.1.2.2
      a := p.2.1
      b := p.2.2.1
      c := p.2.2.2 }
  invFun X := ((X.α₁, (X.α₂, X.α₃)), (X.a, (X.b, X.c)))
  left_inv p := by
    rcases p with ⟨⟨a1, a2, a3⟩, ⟨x, y, z⟩⟩
    rfl
  right_inv X := by
    cases X
    rfl
  map_add' p q := by
    apply H3Zorn.ext_h3 <;> rfl
  map_smul' r p := by
    apply H3Zorn.ext_h3 <;> rfl

@[simp] theorem h3Soldering_apply (p : H3Coord) :
    h3Soldering p =
      { α₁ := p.1.1, α₂ := p.1.2.1, α₃ := p.1.2.2,
        a := p.2.1, b := p.2.2.1, c := p.2.2.2 } := rfl

/-- Coordinate Jordan product obtained by pulling the verified native H3
Jordan product back through the soldering equivalence. -/
noncomputable def coordJordanMul (x y : H3Coord) : H3Coord :=
  h3Soldering.symm (h3Soldering x * h3Soldering y)

/-- The Peirce soldering map is algebraic: it exactly intertwines the
coordinate product and the installed H3 Jordan product. -/
theorem h3Soldering_jordan_intertwines (x y : H3Coord) :
    h3Soldering (coordJordanMul x y) = h3Soldering x * h3Soldering y := by
  simp [coordJordanMul]

/-- Native H3 soldering datum. -/
noncomputable def h3JordanSoldering :
    AlgebraicSoldering H3Coord (H3Zorn ℝ) where
  equiv := h3Soldering
  coordMul := coordJordanMul
  targetMul := fun x y => x * y
  map_mul := h3Soldering_jordan_intertwines

/-- Pull the entrywise G2 action back to Peirce coordinates. -/
noncomputable def coordLiftG2 (D : G2Derivation) : Module.End ℝ H3Coord :=
  h3Soldering.symm.toLinearMap.comp
    ((liftG2End D).comp h3Soldering.toLinearMap)

@[simp] theorem coordLiftG2_apply (D : G2Derivation) (x : H3Coord) :
    coordLiftG2 D x = h3Soldering.symm (liftG2End D (h3Soldering x)) := rfl

/-- Transporting the coordinate action back through soldering recovers the
original entrywise H3 action exactly. -/
theorem transport_coordLiftG2_eq_liftG2End (D : G2Derivation) :
    h3JordanSoldering.transportEnd (coordLiftG2 D) = liftG2End D := by
  apply LinearMap.ext
  intro X
  simp [AlgebraicSoldering.transportEnd, coordLiftG2, h3JordanSoldering]

/-- The single coordinate-side obligation. -/
def CoordinateJordanLeibniz (D : G2Derivation) : Prop :=
  ∀ x y : H3Coord,
    coordLiftG2 D (coordJordanMul x y) =
      coordJordanMul (coordLiftG2 D x) y +
        coordJordanMul x (coordLiftG2 D y)

/-- Algebraic soldering transports coordinate Leibniz to the native H3
Jordan-derivation predicate. -/
theorem entrywiseJordanCompatible_of_coordinateLeibniz
    (D : G2Derivation) (hD : CoordinateJordanLeibniz D) :
    EntrywiseJordanCompatible D := by
  change H3ZornJordanDerivation (liftG2End D)
  rw [← transport_coordLiftG2_eq_liftG2End D]
  exact h3JordanSoldering.derivation_transport (coordLiftG2 D) hD

/-- Conversely, no information is lost: H3 Jordan Leibniz pulls back to the
coordinate soldering chart. -/
theorem coordinateLeibniz_of_entrywiseJordanCompatible
    (D : G2Derivation) (hD : EntrywiseJordanCompatible D) :
    CoordinateJordanLeibniz D := by
  apply h3JordanSoldering.derivation_pullback (coordLiftG2 D)
  rw [transport_coordLiftG2_eq_liftG2End]
  exact hD

/-- The soldering theorem identifies the old ambient compatibility predicate
with the single Peirce-coordinate Leibniz obligation. -/
theorem entrywiseJordanCompatible_iff_coordinateLeibniz
    (D : G2Derivation) :
    EntrywiseJordanCompatible D ↔ CoordinateJordanLeibniz D := by
  constructor
  · exact coordinateLeibniz_of_entrywiseJordanCompatible D
  · exact entrywiseJordanCompatible_of_coordinateLeibniz D

/-- Therefore the full G2-to-F4 compatibility target is equivalent to proving
one coordinate Leibniz theorem uniformly for every native G2 derivation. -/
theorem fullEntrywiseCompatibility_iff_coordinateLeibniz :
    FullEntrywiseG2F4Compatibility ↔
      ∀ D : G2Derivation, CoordinateJordanLeibniz D := by
  constructor
  · intro h D
    have htop : D ∈ entrywiseCompatibleG2 := by
      rw [h]
      trivial
    exact (entrywiseJordanCompatible_iff_coordinateLeibniz D).1 htop
  · intro h
    apply le_antisymm
    · exact le_top
    · intro D hD
      exact (entrywiseJordanCompatible_iff_coordinateLeibniz D).2 (h D)

end InfoGeometry.Canonical.H3ZornAlgebraicSoldering
