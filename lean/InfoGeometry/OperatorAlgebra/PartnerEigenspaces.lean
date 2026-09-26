import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Nonzero spectral pairing of two composable linear maps

For `A : X → Y` and `B : Y → X`, `A` identifies the nonzero eigenspaces of
`BA` and `AB`; its inverse is `μ⁻¹ B`. This works for unequal and infinite
ambient dimensions. The finite-dimensional corollary compares multiplicities.
An unbounded Dirac realization must additionally establish its domains,
adjoint relation, spectral completeness, and heat trace summability.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PartnerEigenspaces

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

theorem partner_eigenvector (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    {μ : K} {x : X} (hx : B (A x) = μ • x) :
    A (B (A x)) = μ • A x := by
  rw [hx, map_smul]

/-- The actual linear isomorphism, including its inverse on the eigenspaces. -/
def nonzeroEigenspaceEquiv (A : X →ₗ[K] Y) (B : Y →ₗ[K] X)
    (μ : K) (hμ : μ ≠ 0) :
    Module.End.eigenspace (B.comp A) μ ≃ₗ[K] Module.End.eigenspace (A.comp B) μ where
  toFun x := ⟨A x, by
    apply Module.End.mem_eigenspace_iff.mpr
    exact partner_eigenvector A B (Module.End.mem_eigenspace_iff.mp x.property)⟩
  invFun y := ⟨μ⁻¹ • B y, by
    apply Module.End.mem_eigenspace_iff.mpr
    have hy : A (B y) = μ • (y : Y) :=
      Module.End.mem_eigenspace_iff.mp y.property
    simp only [LinearMap.comp_apply, map_smul]
    rw [hy, map_smul, smul_smul, smul_smul]
    congr 1
    exact mul_comm _ _⟩
  left_inv x := by
    apply Subtype.ext
    have hx : B (A x) = μ • (x : X) :=
      Module.End.mem_eigenspace_iff.mp x.property
    change μ⁻¹ • B (A x) = (x : X)
    rw [hx, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  right_inv y := by
    apply Subtype.ext
    have hy : A (B y) = μ • (y : Y) :=
      Module.End.mem_eigenspace_iff.mp y.property
    change A (μ⁻¹ • B y) = (y : Y)
    rw [map_smul, hy, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  map_add' x y := by apply Subtype.ext; exact map_add A (x : X) (y : X)
  map_smul' c x := by apply Subtype.ext; exact map_smul A c (x : X)

theorem nonzero_eigenspace_finrank_eq
    (A : X →ₗ[K] Y) (B : Y →ₗ[K] X) (μ : K) (hμ : μ ≠ 0) :
    Module.finrank K (Module.End.eigenspace (B.comp A) μ) =
      Module.finrank K (Module.End.eigenspace (A.comp B) μ) :=
  (nonzeroEigenspaceEquiv A B μ hμ).finrank_eq

end InfoGeometry.OperatorAlgebra.PartnerEigenspaces
