import InfoGeometry.Algebra.AlternativeDerivations
import InfoGeometry.Exceptional.CompositionTriality

/-!
# Alternative derivations as diagonal triality triples

The existing non-associative derivation API already provides the Leibniz law.
This file transports that law into the generic triality carrier by using the
diagonal triple `(D,D,D)`.  It does not identify the resulting carrier with a
specific exceptional Lie algebra.
-/

namespace InfoGeometry.Exceptional.CompositionTrialityAlternativeBridge

open InfoGeometry.Algebra
open InfoGeometry.Exceptional.CompositionTriality

variable {R A : Type*} [CommRing R]
variable [NonUnitalNonAssocRing A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

def multiplicationLinear : A →ₗ[R] A →ₗ[R] A :=
  { toFun := fun a => L_map a
    map_add' := by
      intro a b
      ext x
      simp [L_map, add_mul]
    map_smul' := by
      intro r a
      ext x
      simp [L_map, smul_mul_assoc] }

def diagonalTriality
    (D : NonAssocDerivation R A) :
    TrialityTriple (multiplicationLinear (R := R) (A := A)) :=
  { t₁ := D.toLinearMap
    t₂ := D.toLinearMap
    t₃ := D.toLinearMap
    triality := by
      intro x y
      exact D.leibniz x y }

@[simp] theorem diagonalTriality_t₁
    (D : NonAssocDerivation R A) :
    (diagonalTriality (R := R) (A := A) D).t₁ = D.toLinearMap := rfl

@[simp] theorem diagonalTriality_t₂
    (D : NonAssocDerivation R A) :
    (diagonalTriality (R := R) (A := A) D).t₂ = D.toLinearMap := rfl

@[simp] theorem diagonalTriality_t₃
    (D : NonAssocDerivation R A) :
    (diagonalTriality (R := R) (A := A) D).t₃ = D.toLinearMap := rfl

theorem diagonalTriality_add
    (D E : NonAssocDerivation R A) :
    diagonalTriality (R := R) (A := A) (D + E) =
      diagonalTriality (R := R) (A := A) D +
        diagonalTriality (R := R) (A := A) E := by
  apply TrialityTriple.ext <;> rfl

theorem diagonalTriality_smul
    (r : R) (D : NonAssocDerivation R A) :
    diagonalTriality (R := R) (A := A) (r • D) =
      r • diagonalTriality (R := R) (A := A) D := by
  apply TrialityTriple.ext <;> rfl

def derivationCommutator
    (D E : NonAssocDerivation R A) : NonAssocDerivation R A :=
  { toLinearMap := D.toLinearMap * E.toLinearMap -
      E.toLinearMap * D.toLinearMap
    leibniz' := by
      intro x y
      change D (E (x * y)) - E (D (x * y)) =
        (D (E x) - E (D x)) * y +
          x * (D (E y) - E (D y))
      rw [E.leibniz, D.map_add, D.leibniz, D.leibniz]
      rw [D.leibniz, E.map_add, E.leibniz, E.leibniz]
      rw [sub_mul, mul_sub]
      abel }

theorem diagonalTriality_commutator
    (D E : NonAssocDerivation R A) :
    @TrialityTriple.commutator R A _ _ _
      (multiplicationLinear (R := R) (A := A))
        (diagonalTriality (R := R) (A := A) D)
        (diagonalTriality (R := R) (A := A) E) =
      diagonalTriality (R := R) (A := A) (derivationCommutator D E) := by
  apply TrialityTriple.ext <;> rfl

end InfoGeometry.Exceptional.CompositionTrialityAlternativeBridge
