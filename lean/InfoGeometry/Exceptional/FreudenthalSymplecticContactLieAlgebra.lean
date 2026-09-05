import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Exceptional.FreudenthalSymplecticContactRepresentation

/-!
# Native Lie algebra structure for the corrected symplectic contact bracket

Jacobi is not postulated and is not proved by an exhaustive table of 216
homogeneous cells. It is pulled back from the associative commutator through
the faithful block representation constructed in
`FreudenthalSymplecticContactRepresentation`.

The native bracket installed here is `symplecticContactBracket`; it is not the
legacy `fiveGradedBracket`, whose mixed-triple obstruction is already witnessed
elsewhere in the repository.
-/

noncomputable section

namespace InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (D : CubicJordanDatum J)

/-- Additivity in the first argument, inherited faithfully from the
endomorphism commutator. -/
theorem symplecticContactBracket_add_left
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D (u + v) w =
      symplecticContactBracket D u w +
        symplecticContactBracket D v w := by
  apply symplecticContactRepresentation_injective D
  simp only [map_add, symplecticContactRepresentation_bracket]
  noncomm_ring

/-- Additivity in the second argument. -/
theorem symplecticContactBracket_add_right
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D u (v + w) =
      symplecticContactBracket D u v +
        symplecticContactBracket D u w := by
  apply symplecticContactRepresentation_injective D
  simp only [map_add, symplecticContactRepresentation_bracket]
  noncomm_ring

/-- Compatibility with scalar multiplication in the first argument. -/
theorem symplecticContactBracket_smul_left
    (c : ℝ) (u v : FiveGradedCarrier D) :
    symplecticContactBracket D (c • u) v =
      c • symplecticContactBracket D u v := by
  apply symplecticContactRepresentation_injective D
  simp only [map_smul, symplecticContactRepresentation_bracket]
  simp [smul_mul_assoc, mul_smul_comm, smul_sub]

/-- Compatibility with scalar multiplication in the second argument. -/
theorem symplecticContactBracket_smul_right
    (c : ℝ) (u v : FiveGradedCarrier D) :
    symplecticContactBracket D u (c • v) =
      c • symplecticContactBracket D u v := by
  apply symplecticContactRepresentation_injective D
  simp only [map_smul, symplecticContactRepresentation_bracket]
  simp [smul_mul_assoc, mul_smul_comm, smul_sub]

/-- Alternation follows from alternation of the associative commutator. -/
theorem symplecticContactBracket_self
    (u : FiveGradedCarrier D) :
    symplecticContactBracket D u u = 0 := by
  apply symplecticContactRepresentation_injective D
  simp [symplecticContactRepresentation_bracket]

/-- Skew-symmetry of the corrected contact bracket. -/
theorem symplecticContactBracket_skew
    (u v : FiveGradedCarrier D) :
    symplecticContactBracket D u v =
      -symplecticContactBracket D v u := by
  apply symplecticContactRepresentation_injective D
  simp only [map_neg, symplecticContactRepresentation_bracket]
  noncomm_ring

/-- Leibniz form of the Jacobi identity, pulled back through the faithful
representation. -/
theorem symplecticContactBracket_leibniz
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D u (symplecticContactBracket D v w) =
      symplecticContactBracket D (symplecticContactBracket D u v) w +
        symplecticContactBracket D v (symplecticContactBracket D u w) := by
  apply symplecticContactRepresentation_injective D
  simp only [map_add, symplecticContactRepresentation_bracket]
  noncomm_ring

/-- Cyclic Jacobi identity in the convention used by the earlier five-grade
owners. -/
theorem symplecticContactBracket_jacobi
    (u v w : FiveGradedCarrier D) :
    symplecticContactBracket D u (symplecticContactBracket D v w) +
        symplecticContactBracket D v (symplecticContactBracket D w u) +
        symplecticContactBracket D w (symplecticContactBracket D u v) = 0 := by
  apply symplecticContactRepresentation_injective D
  simp only [map_add, map_zero, symplecticContactRepresentation_bracket]
  noncomm_ring

/-- The corrected contact bracket supplies the native Lie-ring structure on
the six-lane carrier. -/
noncomputable instance symplecticContactLieRing :
    LieRing (FiveGradedCarrier D) where
  bracket := symplecticContactBracket D
  add_lie := symplecticContactBracket_add_left D
  lie_add := symplecticContactBracket_add_right D
  lie_self := symplecticContactBracket_self D
  leibniz_lie := symplecticContactBracket_leibniz D

/-- The real module and corrected bracket form a native Mathlib Lie algebra. -/
noncomputable instance symplecticContactLieAlgebra :
    LieAlgebra ℝ (FiveGradedCarrier D) where
  lie_smul := symplecticContactBracket_smul_right D

@[simp] theorem symplecticContact_lieBracket_eq
    (u v : FiveGradedCarrier D) :
    ⁅u, v⁆ = symplecticContactBracket D u v := rfl

/-- The faithful block representation as a native Lie-algebra morphism. -/
def symplecticContactRepresentationLieHom :
    FiveGradedCarrier D →ₗ⁅ℝ⁆ SymplecticContactEnd (J := J) where
  toLinearMap := symplecticContactRepresentation D
  map_lie' u v := by
    simpa [Ring.lie_def] using
      symplecticContactRepresentation_bracket D u v

@[simp] theorem symplecticContactRepresentationLieHom_apply
    (u : FiveGradedCarrier D) :
    symplecticContactRepresentationLieHom D u =
      symplecticContactRepresentation D u := rfl

/-- Faithfulness of the native Lie representation. -/
theorem symplecticContactRepresentationLieHom_injective :
    Function.Injective (symplecticContactRepresentationLieHom D) :=
  symplecticContactRepresentation_injective D

/-- The image is a native Lie subalgebra of the associative endomorphism
algebra. -/
def symplecticContactImage :
    LieSubalgebra ℝ (SymplecticContactEnd (J := J)) :=
  LieHom.range (symplecticContactRepresentationLieHom D)

/-- The source is Lie-equivalent to its faithful image. -/
noncomputable def symplecticContactImageEquiv :
    FiveGradedCarrier D ≃ₗ⁅ℝ⁆ symplecticContactImage D :=
  (symplecticContactRepresentationLieHom D).equivRangeOfInjective
    (symplecticContactRepresentationLieHom_injective D)

/-- Compact closure theorem: native Jacobi, native Lie representation, and
faithfulness. -/
theorem symplectic_contact_native_closure_packet
    (u v w : FiveGradedCarrier D) :
    ⁅u, ⁅v, w⁆⁆ = ⁅⁅u, v⁆, w⁆ + ⁅v, ⁅u, w⁆⁆ ∧
      symplecticContactRepresentationLieHom D ⁅u, v⁆ =
        ⁅symplecticContactRepresentationLieHom D u,
          symplecticContactRepresentationLieHom D v⁆ ∧
      Function.Injective (symplecticContactRepresentationLieHom D) := by
  exact ⟨leibniz_lie u v w,
    (symplecticContactRepresentationLieHom D).map_lie u v,
    symplecticContactRepresentationLieHom_injective D⟩

end InfoGeometry.Exceptional.Freudenthal
