import InfoGeometry.Clifford.HestenesNaturalConeStandardForm

namespace InfoGeometry.Clifford.Hestenes

open CliffordAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [PartialOrder R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)
variable (v0 : M) (hv0_norm : Q v0 = 1)

variable (Tr : ClPlus Q →ₗ[R] R)

/--
The Hilbert-Schmidt Inner Product.
For ClPlus Q, this is \langle X, Y \rangle_{HS} = Tr (X^† * Y).
-/
def hsInnerProduct (X Y : ClPlus Q) : R :=
  Tr (L_action Q (J_mod Q v0 X) Y)

/--
The Dual Cone \mathcal{P}^\circ relative to the Hilbert-Schmidt inner product.
-/
def DualCone : Set (ClPlus Q) :=
  { Y | ∀ X ∈ NaturalCone Q v0, hsInnerProduct Q v0 Tr X Y ≥ 0 }

/--
The Tomita-Takesaki Self-Duality Theorem for the Natural Cone.
\mathcal{P}^\natural = (\mathcal{P}^\natural)^\circ

This is the ultimate bridge between the algebraic future Lorentz cone
and the thermodynamic KMS state generator.
We leave this as the final strategic bridge proposition.
-/
def selfDuality_statement : Prop :=
  NaturalCone Q v0 = DualCone Q v0 Tr

end InfoGeometry.Clifford.Hestenes
