import InfoGeometry.OperatorAlgebra.FiveGradeZornShadowProjection
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Typed algebraic Bianchi defect for a projected nonassociative shadow

This owner is deliberately smaller than a differential-form Yang--Mills
connection.  A `ProjectedConnection` only supplies a shadow-valued one-form;
the product, commutator, associator, and projection leakage are inherited from
the existing projected-shadow owner.  Thus the theorem below is an algebraic
right-nested Bianchi readout, not a claim about a differential gauge theory.
-/

namespace InfoGeometry.Canonical.ProjectedNonassociativeBianchi

open InfoGeometry.OperatorAlgebra.FiveGradeZornShadowProjection

variable {R Z E : Type*}
  [CommRing R]
  [AddCommGroup Z] [Module R Z]
  [Ring E] [Algebra R E]

/-- A shadow-valued connection one-form, with no unproved differential data. -/
structure ProjectedConnection (Point Tangent : Type*) where
  form : Point → Tangent → Z

/-- The cyclic right-nested commutator readout of a projected connection. -/
def rightNestedBianchi
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (C : ProjectedConnection (Z := Z) Point Tangent)
    (p : Point) (X Y Z₁ : Tangent) : Z :=
  shadowRightNestedJacobiator inclusion readout
    (C.form p X) (C.form p Y) (C.form p Z₁)

/-- Ambient discarded-product readout corresponding to a shadow associator. -/
def associatorLeakage
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y z : Z) : Z :=
  readout (
    inclusion x * operatorDefect inclusion readout (inclusion y * inclusion z) -
      operatorDefect inclusion readout (inclusion x * inclusion y) * inclusion z)

theorem shadowAssociator_eq_associatorLeakage
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (x y z : Z) :
    shadowAssociator inclusion readout x y z = associatorLeakage inclusion readout x y z := by
  exact shadowAssociator_eq_readout_of_defect inclusion readout x y z

theorem rightNestedBianchi_eq_neg_shadowJacobiator
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (C : ProjectedConnection (Z := Z) Point Tangent)
    (p : Point) (X Y Z₁ : Tangent) :
    rightNestedBianchi inclusion readout C p X Y Z₁ =
      -shadowJacobiator inclusion readout
        (C.form p X) (C.form p Y) (C.form p Z₁) := by
  exact shadowRightNestedJacobiator_eq_neg inclusion readout
    (C.form p X) (C.form p Y) (C.form p Z₁)

/-- The projected Bianchi defect is the alternating sum of shadow associators. -/
theorem rightNestedBianchi_eq_neg_associator_leakage
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (C : ProjectedConnection (Z := Z) Point Tangent)
    (p : Point) (X Y Z₁ : Tangent) :
    rightNestedBianchi inclusion readout C p X Y Z₁ =
      -((shadowAssociator inclusion readout (C.form p X) (C.form p Y) (C.form p Z₁) +
          shadowAssociator inclusion readout (C.form p Y) (C.form p Z₁) (C.form p X) +
          shadowAssociator inclusion readout (C.form p Z₁) (C.form p X) (C.form p Y)) -
        (shadowAssociator inclusion readout (C.form p Y) (C.form p X) (C.form p Z₁) +
          shadowAssociator inclusion readout (C.form p Z₁) (C.form p Y) (C.form p X) +
          shadowAssociator inclusion readout (C.form p X) (C.form p Z₁) (C.form p Y))) := by
  rw [rightNestedBianchi_eq_neg_shadowJacobiator]
  rw [shadow_akivis_identity]

/-- Fully expanded projected Bianchi defect in terms of ambient leakage readouts. -/
theorem rightNestedBianchi_eq_neg_leakage_sum
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (C : ProjectedConnection (Z := Z) Point Tangent)
    (p : Point) (X Y Z₁ : Tangent) :
    rightNestedBianchi inclusion readout C p X Y Z₁ =
      -((associatorLeakage inclusion readout (C.form p X) (C.form p Y) (C.form p Z₁) +
          associatorLeakage inclusion readout (C.form p Y) (C.form p Z₁) (C.form p X) +
          associatorLeakage inclusion readout (C.form p Z₁) (C.form p X) (C.form p Y)) -
        (associatorLeakage inclusion readout (C.form p Y) (C.form p X) (C.form p Z₁) +
          associatorLeakage inclusion readout (C.form p Z₁) (C.form p Y) (C.form p X) +
          associatorLeakage inclusion readout (C.form p X) (C.form p Z₁) (C.form p Y))) := by
  rw [rightNestedBianchi_eq_neg_associator_leakage]
  rw [shadowAssociator_eq_associatorLeakage,
    shadowAssociator_eq_associatorLeakage,
    shadowAssociator_eq_associatorLeakage,
    shadowAssociator_eq_associatorLeakage,
    shadowAssociator_eq_associatorLeakage,
    shadowAssociator_eq_associatorLeakage]

end InfoGeometry.Canonical.ProjectedNonassociativeBianchi
