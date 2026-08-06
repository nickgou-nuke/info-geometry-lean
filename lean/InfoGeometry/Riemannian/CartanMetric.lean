import InfoGeometry.Clifford.HestenesNaturalConeStandardForm

namespace InfoGeometry.Riemannian

open CliffordAlgebra
open InfoGeometry.Clifford.Hestenes

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

/-- 
The Cartan Metric at the identity of the positive definite cone.
g_I(V_1, V_2) = Tr(V_1 V_2).
For Hestenes paravectors, the trace form can be defined via the Clifford scalar part,
but algebraically, it is a symmetric bilinear form invariant under the conjugation action of the unitary group.
-/
-- We define it abstractly as a generic invariant bilinear form first, 
-- or we can use the quadratic form polar if we restrict to the Jordan algebra.
-- To provide a 0-sorry base, we define the property of being an invariant metric.

def IsCartanMetricAtIdentity (B : (ClPlus Q) →ₗ[R] (ClPlus Q) →ₗ[R] R) : Prop :=
  -- Symmetry
  (∀ X Y, B X Y = B Y X) ∧ 
  -- Invariance under unitary conjugation (where U * U^\dagger = 1)
  -- For any U in the Clifford algebra with U * U^\dagger = 1, B(U X U^\dagger, U Y U^\dagger) = B(X, Y)
  (∀ U X Y, (U * J_mod Q v0 U = 1) → 
    B (L_action Q U (R_action Q (J_mod Q v0 U) X)) 
      (L_action Q U (R_action Q (J_mod Q v0 U) Y)) = B X Y)

/-- 
The Cartan metric at an arbitrary point Σ in the positive definite cone.
g_Σ(V_1, V_2) = Tr(Σ^{-1} V_1 Σ^{-1} V_2).
Here we define its invariant transport property.
-/
def CartanMetricTransport 
    (g : ClPlus Q → (ClPlus Q) →ₗ[R] (ClPlus Q) →ₗ[R] R) : Prop :=
  -- Isometric transport: g_I(V_1, V_2) = g_Σ(Σ^{1/2} V_1 Σ^{1/2}, Σ^{1/2} V_2 Σ^{1/2})
  -- Equivalently: g_{A A^\dagger}(A X A^\dagger, A Y A^\dagger) = g_I(X, Y)
  ∀ A X Y, 
    g (L_action Q A (J_mod Q v0 A)) 
      (L_action Q A (R_action Q (J_mod Q v0 A) X)) 
      (L_action Q A (R_action Q (J_mod Q v0 A) Y)) = 
    g 1 X Y

end InfoGeometry.Riemannian
