import InfoGeometry.Algebra.Zorn.G2RootPCAlignment
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.GroupTheory.G2BruhatInversions

namespace InfoGeometry.Algebra.Zorn.G2CanonicalTopInversionOrder

open InfoGeometry.Algebra.Zorn.G2RootPCAlignment
open InfoGeometry.Algebra.Zorn.G2Combinatorics
open InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
open InfoGeometry.GroupTheory.G2BruhatInversions

noncomputable def topOrderedInversionRoots :
    Fin 6 ≃ {α : G2PositiveRoot // α ∈ bruhatInversionRoots (3, false)} := by
  have hmem : ∀ i : Fin 6,
      rootPCAlignment.symm i ∈ bruhatInversionRoots (3, false) := by
    intro i
    rw [bruhatInversionRoots_longest]
    simp
  exact
    { toFun := fun i => ⟨rootPCAlignment.symm i, hmem i⟩
      invFun := fun α => rootPCAlignment α.1
      left_inv := by intro i; simp
      right_inv := by
        intro α
        apply Subtype.ext
        change rootPCAlignment.symm (rootPCAlignment α.1) = α.1
        exact rootPCAlignment.symm_apply_apply α.1 }

theorem topOrderedInversionRoots_apply (i : Fin 6) :
    (topOrderedInversionRoots i).1 = rootPCAlignment.symm i := by
  rfl

theorem topOrderedInversionRoots_bijective :
    Function.Bijective topOrderedInversionRoots :=
  topOrderedInversionRoots.bijective

end InfoGeometry.Algebra.Zorn.G2CanonicalTopInversionOrder
