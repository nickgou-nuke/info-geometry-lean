import InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
import InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
import InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
import InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

/-! The root-coordinate and native inner-derivation carriers have the same
span.  This file is only the bridge between their two existing owners. -/

namespace InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge

open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.G2ZornDerivationRootRepresentation
open InfoGeometry.Algebra.Zorn.NativeStanDerivationCoverage
open InfoGeometry.Algebra.Zorn.G2RootWeylAdjointCharacter
open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Lie.CanonicalZornDerivation
open InfoGeometry.Lie.CanonicalZornDerivationDimension
open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition

theorem cartanRootSpan_eq_innerDerivationPairSpan :
    Submodule.span ℝ
        (Set.range cartanDerivation ∪
          Set.range zornDerivationRootRepresentation) =
      Submodule.span ℝ
        (Set.range (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
          NativeStanDerivationBilinear.innerDerivation p.1 p.2)) := by
  rw [cartan_root_span_eq_top, vector_inner_derivations_span_top]

theorem rootRepresentation_mem_innerDerivationPairSpan
    (r : G2TwoRootSystem.G2Root) :
    zornDerivationRootRepresentation r ∈
      Submodule.span ℝ
        (Set.range (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
          NativeStanDerivationBilinear.innerDerivation p.1 p.2)) := by
  rw [vector_inner_derivations_span_top]
  exact Submodule.mem_top

theorem finiteRootDerivationReadout_mem_innerDerivationPairSpan
    (r : G2TwoRootSystem.G2Root) :
    InfoGeometry.Lie.CanonicalZornDerivation.canonicalToVectorDerivation
        (rootDerivation (G2ZornDerivationRootRepresentation.rootCoordinate r)) ∈
      Submodule.span ℝ
        (Set.range (fun p : ZornVectorMatrix ℝ × ZornVectorMatrix ℝ =>
          NativeStanDerivationBilinear.innerDerivation p.1 p.2)) := by
  rw [← finiteRoot_derivation_readout r]
  exact rootRepresentation_mem_innerDerivationPairSpan r

/-! The preceding readout has the canonical derivation on the right of the
vector equivalence.  Exposing the inverse direction is the exact typed
identification needed by canonical-side consumers. -/
theorem finiteRoot_derivation_canonical_transport
    (r : G2TwoRootSystem.G2Root) :
    InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (zornDerivationRootRepresentation r) =
      rootDerivation (G2ZornDerivationRootRepresentation.rootCoordinate r) := by
  rw [finiteRoot_derivation_readout]
  exact InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv.apply_symm_apply _

/-! The preceding transport also has an exact parameter-coordinate readback.
    This is the coordinate statement needed before any pair-witness or sign
    calculation: no root is identified with a pair derivation here. -/
theorem finiteRoot_derivation_parameter_coordinates
    (r : G2TwoRootSystem.G2Root) :
    InfoGeometry.Lie.CanonicalZornDerivationDimension.canonicalParameterLinearEquiv.symm
        (InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
          (zornDerivationRootRepresentation r)) =
      InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.parameterUnit
        (G2ZornDerivationRootRepresentation.rootCoordinate r) := by
  rw [finiteRoot_derivation_canonical_transport]
  simp [InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition.rootDerivation]

theorem rootCoordinate_ne_cartan_indices
    (r : G2TwoRootSystem.G2Root) :
    G2ZornDerivationRootRepresentation.rootCoordinate r ≠ 6 ∧
      G2ZornDerivationRootRepresentation.rootCoordinate r ≠ 13 := by
  rcases r with ⟨l, k⟩
  fin_cases l <;> fin_cases k <;> decide

theorem finiteRoot_canonical_derivation_injective :
    Function.Injective (fun r : G2TwoRootSystem.G2Root =>
      InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv
        (zornDerivationRootRepresentation r)) := by
  intro r s h
  apply zornDerivationRootRepresentation_injective
  exact InfoGeometry.Lie.CanonicalZornDerivation.vectorCanonicalLinearEquiv.injective h

/-- The root/Cartan decomposition and the chiral operator readout generate
    the same native derivation space.  This is the exact carrier-level bridge:
    it does not identify a chiral label with a root label, but identifies the
    two spans after both have been transported to the native derivation type. -/
theorem cartanRootSpan_eq_chiralReadoutPairSpan :
    Submodule.span ℝ
        (Set.range cartanDerivation ∪
          Set.range zornDerivationRootRepresentation) =
      Submodule.span ℝ
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          NativeStanDerivationBilinear.innerDerivation
            (chiralReadoutBasis p.1) (chiralReadoutBasis p.2))) := by
  rw [cartan_root_span_eq_top, chiralReadoutPairDerivations_span_top]

theorem rootRepresentation_mem_chiralReadoutPairSpan
    (r : G2TwoRootSystem.G2Root) :
    zornDerivationRootRepresentation r ∈
      Submodule.span ℝ
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          NativeStanDerivationBilinear.innerDerivation
            (chiralReadoutBasis p.1) (chiralReadoutBasis p.2))) := by
  rw [← cartanRootSpan_eq_chiralReadoutPairSpan]
  exact Submodule.subset_span (Or.inr (Set.mem_range_self r))

theorem cartanDerivation_mem_chiralReadoutPairSpan
    (j : Fin 2) :
    cartanDerivation j ∈
      Submodule.span ℝ
        (Set.range (fun p :
          InfoGeometry.OperatorAlgebra.ChiralGenerator ×
            InfoGeometry.OperatorAlgebra.ChiralGenerator =>
          NativeStanDerivationBilinear.innerDerivation
            (chiralReadoutBasis p.1) (chiralReadoutBasis p.2))) := by
  rw [← cartanRootSpan_eq_chiralReadoutPairSpan]
  exact Submodule.subset_span (Or.inl (Set.mem_range_self j))

theorem chiralReadoutPairDerivation_mem_cartanRootSpan
    (g h : InfoGeometry.OperatorAlgebra.ChiralGenerator) :
    NativeStanDerivationBilinear.innerDerivation
        (chiralReadoutBasis g) (chiralReadoutBasis h) ∈
      Submodule.span ℝ
        (Set.range cartanDerivation ∪
          Set.range zornDerivationRootRepresentation) := by
  rw [cartanRootSpan_eq_chiralReadoutPairSpan]
  exact Submodule.subset_span (Set.mem_range_self (g, h))

end InfoGeometry.Algebra.Zorn.G2RootInnerDerivationBridge
