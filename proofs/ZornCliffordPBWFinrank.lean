import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import proofs.ZornCliffordIsomorphismClosure

/-!
# PBW finrank certificate for the canonical Zorn Clifford algebra

This module constructs the finite basis of the full exterior algebra by
collecting the native bases of all homogeneous exterior powers.  Its index is
then reindexed from the dependent sum of fixed-cardinality subsets to all
subsets of `Fin 8`.
-/

noncomputable section

namespace ZornCliffordPBWFinrank

open scoped DirectSum

open CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open ZornCliffordBasisMonomials

/-- The dependent union of subsets of each fixed cardinality is canonically
equivalent to the type of all finite subsets. -/
def sigmaPowersetCardEquiv :
    (Σ n : ℕ, Set.powersetCard (Fin 8) n) ≃ Finset (Fin 8) where
  toFun x := x.2.1
  invFun s := ⟨s.card, ⟨s, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨n, s, hs⟩
    subst n
    rfl
  right_inv s := rfl

/-- The basis obtained by joining the standard bases of all homogeneous
exterior powers and transporting through the exterior-algebra grading. -/
def exteriorAlgebraVector8Basis :
    Module.Basis (Finset (Fin 8)) ℂ (ExteriorAlgebra ℂ Vector8) := by
  let homogeneousBasis :
      Module.Basis (Σ n : ℕ, Set.powersetCard (Fin 8) n) ℂ
        (⨁ n : ℕ, ExteriorAlgebra.exteriorPower ℂ n Vector8) :=
    DFinsupp.basis (fun n => sageZornBasis.exteriorPower n)
  let transported := homogeneousBasis.map
    (DirectSum.decomposeLinearEquiv
      (fun n : ℕ => ExteriorAlgebra.exteriorPower ℂ n Vector8)).symm
  exact transported.reindex sigmaPowersetCardEquiv

/-- The full exterior algebra on the eight-dimensional Zorn carrier has
dimension `2^8 = 256`. -/
theorem exteriorAlgebra_vector8_finrank :
    Module.finrank ℂ (ExteriorAlgebra ℂ Vector8) = 256 := by
  rw [Module.finrank_eq_card_basis exteriorAlgebraVector8Basis]
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

/-- PBW dimension of the native Clifford algebra, transported through
`CliffordAlgebra.equivExterior`. -/
theorem cliffordAlgebra_vector8_finrank :
    Module.finrank ℂ (CliffordAlgebra vectorQuadratic) = 256 := by
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior vectorQuadratic)]
  exact exteriorAlgebra_vector8_finrank

/-! ## The native Clifford PBW basis and the remaining equivalence criterion -/

/-- The native Clifford basis obtained by transporting the exterior basis
backward through the PBW linear equivalence. -/
def cliffordAlgebraVector8Basis :
    Module.Basis (Finset (Fin 8)) ℂ (CliffordAlgebra vectorQuadratic) :=
  exteriorAlgebraVector8Basis.map
    (CliffordAlgebra.equivExterior vectorQuadratic).symm

/-- Since source and target both have dimension 256, injectivity and
surjectivity of the canonical Zorn representation are equivalent. -/
theorem zornCliffordRepresentation_injective_iff_surjective :
    Function.Injective zornCliffordRepresentation ↔
      Function.Surjective zornCliffordRepresentation := by
  letI : FiniteDimensional ℂ (CliffordAlgebra vectorQuadratic) :=
    cliffordAlgebraVector8Basis.finiteDimensional_of_finite
  have hdim :
      Module.finrank ℂ (CliffordAlgebra vectorQuadratic) =
        Module.finrank ℂ (Module.End ℂ DiracSpinor16) := by
    rw [cliffordAlgebra_vector8_finrank]
    exact CanonicalZornCliffordIsomorphism.diracEnd_finrank.symm
  exact LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    hdim (f := zornCliffordRepresentation.toLinearMap)

/-- A surjectivity certificate is now sufficient to package the complete
algebra equivalence; injectivity follows from the dimension theorem. -/
def zornCliffordFullIsomorphismOfSurjective
    (hsurj : Function.Surjective zornCliffordRepresentation) :
    CliffordAlgebra vectorQuadratic ≃ₐ[ℂ] Module.End ℂ DiracSpinor16 :=
  AlgEquiv.ofBijective zornCliffordRepresentation
    ⟨zornCliffordRepresentation_injective_iff_surjective.mpr hsurj, hsurj⟩

/-- Dually, an injectivity certificate suffices to package the same complete
algebra equivalence. -/
def zornCliffordFullIsomorphismOfInjective
    (hinj : Function.Injective zornCliffordRepresentation) :
    CliffordAlgebra vectorQuadratic ≃ₐ[ℂ] Module.End ℂ DiracSpinor16 :=
  AlgEquiv.ofBijective zornCliffordRepresentation
    ⟨hinj, zornCliffordRepresentation_injective_iff_surjective.mp hinj⟩

end ZornCliffordPBWFinrank

end noncomputable section
