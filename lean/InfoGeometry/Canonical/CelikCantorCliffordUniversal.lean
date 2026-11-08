import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Universal finite Clifford lift for the Çelik operator layer

This owner exposes the native Mathlib universal property needed by the finite
Çelik construction.  A concrete family of Cantor or Pauli operators must first
be packaged as a square-preserving linear map; the lift below then produces the
algebra homomorphism from the Clifford algebra.  No matrix/tensor isomorphism
is inferred from the universal property alone.
-/

namespace InfoGeometry.Canonical.CelikCantorClifford

theorem cliffordAlgHom_of_square_preserving
    {R M A : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    [Semiring A] [Algebra R A]
    (Q : QuadraticForm R M)
    (f : M →ₗ[R] A)
    (hf : ∀ m, f m * f m = (algebraMap R A) (Q m)) :
    ∃ φ : CliffordAlgebra Q →ₐ[R] A,
      ∀ m, φ (CliffordAlgebra.ι Q m) = f m := by
  let φ : CliffordAlgebra Q →ₐ[R] A :=
    CliffordAlgebra.lift Q ⟨f, hf⟩
  refine ⟨φ, ?_⟩
  intro m
  exact CliffordAlgebra.lift_ι_apply f hf m

theorem cliffordAlgHom_unique_of_generator_eq
    {R M A : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    [Semiring A] [Algebra R A]
    {Q : QuadraticForm R M}
    {φ ψ : CliffordAlgebra Q →ₐ[R] A}
    (h : ∀ m, φ (CliffordAlgebra.ι Q m) = ψ (CliffordAlgebra.ι Q m)) :
    φ = ψ := by
  apply CliffordAlgebra.hom_ext
  ext m
  exact h m

end InfoGeometry.Canonical.CelikCantorClifford
