/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornVectorMatrix
import InfoGeometry.Exceptional.DiagonalCompositionTriality

/-! # Derivations are exactly the diagonal local-triality Lie algebra

This constructs the inverse map and a native Lie equivalence, not just an
iff between two renamed predicates. The multiplication is the existing
nonassociative Zorn product, over an arbitrary commutative ring.
-/

namespace InfoGeometry.Algebra.ZornVectorMatrix

open InfoGeometry.Exceptional.CompositionTriality

variable {R : Type*} [CommRing R]

/-- Bilinear packaging of the actual Zorn multiplication. -/
def multiplicationBilinear : ZornVectorMatrix R →ₗ[R] ZornVectorMatrix R →ₗ[R]
    ZornVectorMatrix R where
  toFun X :=
    { toFun := mul X
      map_add' := mul_add X
      map_smul' := fun r Y => mul_smul r X Y }
  map_add' X Y := by
    apply LinearMap.ext
    intro Z
    exact add_mul X Y Z
  map_smul' r X := by
    apply LinearMap.ext
    intro Z
    exact smul_mul r X Z

/-- Every native Zorn derivation yields a linear triality triple. -/
def derivationTriality (D : Derivation (R := R)) :
    TrialityTriple (multiplicationBilinear (R := R)) where
  t₁ := ⟨⟨D.toFun, D.map_add⟩, D.map_smul⟩
  t₂ := ⟨⟨D.toFun, D.map_add⟩, D.map_smul⟩
  t₃ := ⟨⟨D.toFun, D.map_add⟩, D.map_smul⟩
  triality := D.map_mul

/-- Recover the derivation from any equal-component triality triple. -/
def derivationOfDiagonalTriality
    (T : TrialityTriple.diagonalLieSubalgebra (multiplicationBilinear (R := R))) :
    Derivation (R := R) where
  toFun := T.1.t₁
  map_add' := T.1.t₁.map_add
  map_smul' := T.1.t₁.map_smul
  map_mul' X Y := by
    have h := T.1.triality X Y
    rw [← T.2.1, ← T.2.2] at h
    exact h

/-- The exact diagonal locus, with linear and Lie structure preserved both ways. -/
def derivationDiagonalTrialityEquiv :
    Derivation (R := R) ≃ₗ⁅R⁆
      TrialityTriple.diagonalLieSubalgebra (multiplicationBilinear (R := R)) where
  toFun D := ⟨derivationTriality D, ⟨rfl, rfl⟩⟩
  invFun := derivationOfDiagonalTriality
  left_inv D := by
    apply Derivation.ext
    intro X
    rfl
  right_inv T := by
    apply Subtype.ext
    apply TrialityTriple.ext
    · rfl
    · exact T.2.1
    · exact T.2.2
  map_add' D E := by
    apply Subtype.ext
    apply TrialityTriple.ext <;> rfl
  map_smul' r D := by
    apply Subtype.ext
    apply TrialityTriple.ext <;> rfl
  map_lie' {D E} := by
    apply Subtype.ext
    apply TrialityTriple.ext <;> rfl

/-- Explicit obstruction to treating all linear triality triples as orthogonal. -/
theorem scalarTriality_norm_variation :
    let T := TrialityTriple.scalarTriple (multiplicationBilinear (R := ℚ)) 1 0
    norm (add (T.t₁ one) one) - norm (T.t₁ one) - norm one = 2 := by
  norm_num [TrialityTriple.scalarTriple, LinearMap.smul_apply, one, add, norm,
    smul, ZornVec3.dot, Fin.sum_univ_three]

end InfoGeometry.Algebra.ZornVectorMatrix
