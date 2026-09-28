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

/-- The projected algebraic Bianchi defect vanishes exactly when the cyclic
associator-leakage balance vanishes.  This is an algebraic criterion only; it
does not assert a differential-form or torsion identity. -/
theorem rightNestedBianchi_eq_zero_iff_leakage_balance_eq_zero
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (C : ProjectedConnection (Z := Z) Point Tangent)
    (p : Point) (X Y Z₁ : Tangent) :
    rightNestedBianchi inclusion readout C p X Y Z₁ = 0 ↔
      ((associatorLeakage inclusion readout (C.form p X) (C.form p Y) (C.form p Z₁) +
          associatorLeakage inclusion readout (C.form p Y) (C.form p Z₁) (C.form p X) +
          associatorLeakage inclusion readout (C.form p Z₁) (C.form p X) (C.form p Y)) -
        (associatorLeakage inclusion readout (C.form p Y) (C.form p X) (C.form p Z₁) +
          associatorLeakage inclusion readout (C.form p Z₁) (C.form p Y) (C.form p X) +
          associatorLeakage inclusion readout (C.form p X) (C.form p Z₁) (C.form p Y))) = 0 := by
  rw [rightNestedBianchi_eq_neg_leakage_sum]
  simp

/-- If the included shadow is closed under the ambient product and `readout`
is a left inverse to `inclusion`, then the projected product is associative.
Thus its associator defect vanishes for a structural reason: projection loses
no products. -/
theorem shadowAssociator_eq_zero_of_mul_closed_image
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (hsection : ∀ x, readout (inclusion x) = x)
    (hclosed : ∀ x y, ∃ w, inclusion x * inclusion y = inclusion w)
    (x y z : Z) :
    shadowAssociator inclusion readout x y z = 0 := by
  have hmul (a b : Z) :
      inclusion (shadowMul inclusion readout a b) = inclusion a * inclusion b := by
    obtain ⟨w, hw⟩ := hclosed a b
    calc
      inclusion (shadowMul inclusion readout a b) =
          inclusion (readout (inclusion a * inclusion b)) := rfl
      _ = inclusion (readout (inclusion w)) := by rw [hw]
      _ = inclusion w := by rw [hsection]
      _ = inclusion a * inclusion b := hw.symm
  unfold shadowAssociator shadowMul
  rw [← map_sub]
  congr 1
  rw [hmul x y, hmul y z]
  simp [mul_assoc]

/-- Under multiplicative closure of the included shadow, the projected
right-nested commutator Bianchi expression vanishes. This does not assert the
same for a genuinely nonassociative projected product whose image is not
closed. -/
theorem rightNestedBianchi_eq_zero_of_mul_closed_image
    (inclusion : Z →ₗ[R] E) (readout : E →ₗ[R] Z)
    (hsection : ∀ x, readout (inclusion x) = x)
    (hclosed : ∀ x y, ∃ w, inclusion x * inclusion y = inclusion w)
    (C : ProjectedConnection (Z := Z) Point Tangent)
    (p : Point) (X Y Z₁ : Tangent) :
    rightNestedBianchi inclusion readout C p X Y Z₁ = 0 := by
  have hassoc (a b c : Z) : shadowAssociator inclusion readout a b c = 0 :=
    shadowAssociator_eq_zero_of_mul_closed_image
      inclusion readout hsection hclosed a b c
  have hjac : shadowJacobiator inclusion readout
      (C.form p X) (C.form p Y) (C.form p Z₁) = 0 := by
    rw [shadow_akivis_identity]
    simp [hassoc]
  rw [rightNestedBianchi_eq_neg_shadowJacobiator, hjac]
  simp

end InfoGeometry.Canonical.ProjectedNonassociativeBianchi
