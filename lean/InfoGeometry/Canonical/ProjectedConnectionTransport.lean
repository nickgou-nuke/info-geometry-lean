import InfoGeometry.Canonical.ProjectedNonassociativeBianchi
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorValuedConnection

/-!
# Transport of an associative connection into a projected shadow

This owner connects the existing associative `Connection` datum to the typed
projected-shadow Bianchi readout.  The readout is only linear; no multiplicative
or differential compatibility is inferred.
-/

namespace InfoGeometry.Canonical.ProjectedConnectionTransport

open InfoGeometry.Canonical.ProjectedNonassociativeBianchi
open InfoGeometry.Optics.OperatorValuedConnection

variable {R Z E Point Tangent : Type*}
  [CommRing R]
  [AddCommGroup Z] [Module R Z]
  [Ring E] [Algebra R E]

def projectConnection
    (readout : E →ₗ[R] Z)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := E)) :
    ProjectedConnection (Z := Z) Point Tangent :=
  { form := fun p X => readout (C.form p X) }

@[simp] theorem projectConnection_form
    (readout : E →ₗ[R] Z)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := E))
    (p : Point) (X : Tangent) :
    (projectConnection readout C).form p X = readout (C.form p X) := rfl

theorem projectedConnection_rightNestedBianchi_eq_neg_leakage_sum
    (inclusion : Z →ₗ[R] E)
    (readout : E →ₗ[R] Z)
    (C : Connection (Point := Point) (Tangent := Tangent) (Value := E))
    (p : Point) (X Y Z₁ : Tangent) :
    rightNestedBianchi inclusion readout (projectConnection readout C) p X Y Z₁ =
      -((associatorLeakage inclusion readout
          ((projectConnection readout C).form p X)
          ((projectConnection readout C).form p Y)
          ((projectConnection readout C).form p Z₁) +
          associatorLeakage inclusion readout
            ((projectConnection readout C).form p Y)
            ((projectConnection readout C).form p Z₁)
            ((projectConnection readout C).form p X) +
          associatorLeakage inclusion readout
            ((projectConnection readout C).form p Z₁)
            ((projectConnection readout C).form p X)
            ((projectConnection readout C).form p Y)) -
        (associatorLeakage inclusion readout
            ((projectConnection readout C).form p Y)
            ((projectConnection readout C).form p X)
            ((projectConnection readout C).form p Z₁) +
          associatorLeakage inclusion readout
            ((projectConnection readout C).form p Z₁)
            ((projectConnection readout C).form p Y)
            ((projectConnection readout C).form p X) +
          associatorLeakage inclusion readout
            ((projectConnection readout C).form p X)
            ((projectConnection readout C).form p Z₁)
            ((projectConnection readout C).form p Y))) := by
  exact
    (rightNestedBianchi_eq_neg_leakage_sum inclusion readout
      (projectConnection readout C) p X Y Z₁)

end InfoGeometry.Canonical.ProjectedConnectionTransport
