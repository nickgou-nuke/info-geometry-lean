import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix representation induced by an exterior-algebra basis

Given a rank-32 module basis of an exterior algebra and an algebra
representation into its endomorphism ring, this file transports the
representation to `32 × 32` matrices and proves that this change of carrier
preserves and reflects injectivity.  This generic construction does not itself
define a Pin(5,5) group action or prove a Pin representation theorem.
-/

namespace InfoGeometry.AQFT.Pin55Pullback

variable {R W A : Type*}
variable [CommRing R] [AddCommGroup W] [Module R W]
variable [Ring A] [Algebra R A]

/-- The algebra equivalence from endomorphisms to matrices in the chosen basis. -/
noncomputable def endomorphismMatrixEquiv
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W)) :
    Module.End R (ExteriorAlgebra R W) ≃ₐ[R] Matrix (Fin 32) (Fin 32) R :=
  LinearMap.toMatrixAlgEquiv exteriorBasis

/-- Matrix form of an algebra representation, obtained by changing its target
from endomorphisms to matrices in `exteriorBasis`. -/
noncomputable def matrixRepresentationOfBasis
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W))
    (ρ : A →ₐ[R] Module.End R (ExteriorAlgebra R W)) :
    A →ₐ[R] Matrix (Fin 32) (Fin 32) R :=
  (endomorphismMatrixEquiv exteriorBasis).toAlgHom.comp ρ

/-- Passing from endomorphisms to matrices in a basis preserves and reflects
injectivity of the represented algebra map. -/
theorem matrixRepresentationOfBasis_injective_iff
    (exteriorBasis : Module.Basis (Fin 32) R (ExteriorAlgebra R W))
    (ρ : A →ₐ[R] Module.End R (ExteriorAlgebra R W)) :
    Function.Injective (matrixRepresentationOfBasis exteriorBasis ρ) ↔
      Function.Injective ρ := by
  change Function.Injective ((endomorphismMatrixEquiv exteriorBasis).toAlgHom.comp ρ) ↔
    Function.Injective ρ
  constructor
  · intro h a b hab
    apply h
    exact congrArg (endomorphismMatrixEquiv exteriorBasis) hab
  · intro h a b hab
    apply h
    apply (endomorphismMatrixEquiv exteriorBasis).injective
    exact hab

end InfoGeometry.AQFT.Pin55Pullback
