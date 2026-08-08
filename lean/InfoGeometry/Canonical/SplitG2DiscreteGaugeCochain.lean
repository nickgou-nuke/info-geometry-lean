import InfoGeometry.Canonical.SplitG2DiscreteCoframePullback
import InfoGeometry.Canonical.G2HolonomyGaugeConnections

namespace InfoGeometry.Canonical

/-!
# Discrete gauge pullback of split-`G₂` forms

This file connects the existing edge transport to the coframe pullback layer.
Form invariance is an explicit property: the carrier automorphism preserves
the canonical three-form, but an arbitrary alternating form need not be fixed.
-/

noncomputable def pathPullbackForm
    {E : Type*} {k : ℕ}
    (A : SplitG2GaugeConnection E)
    (path : List E)
    (ω : AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin k)) :
    AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin k) :=
  ω.compLinearMap (parallelTransport A path).toLinearEquiv.toLinearMap

noncomputable def pathTransportThreeCochain
    {E : Type*} {K : FiniteOrientedCellComplex}
    (A : SplitG2GaugeConnection E)
    (F : SplitG2DiscreteCoframe K)
    (path : List E)
    (φ : SplitG2ThreeForms) :
    RationalScalarCochain K 3 :=
  pullbackThreeForm F (pathPullbackForm A path φ)

noncomputable def pathTransportFourCochain
    {E : Type*} {K : FiniteOrientedCellComplex}
    (A : SplitG2GaugeConnection E)
    (F : SplitG2DiscreteCoframe K)
    (path : List E)
    (ψ : SplitG2FourForms) :
    RationalScalarCochain K 4 :=
  pullbackFourForm F (pathPullbackForm A path ψ)

@[simp] theorem pathPullbackForm_nil
    {E : Type*} {k : ℕ}
    (A : SplitG2GaugeConnection E)
    (ω : AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin k)) :
    pathPullbackForm A [] ω = ω := by
  ext v
  rfl

@[simp] theorem pathTransportThreeCochain_nil
    {E : Type*} {K : FiniteOrientedCellComplex}
    (A : SplitG2GaugeConnection E)
    (F : SplitG2DiscreteCoframe K)
    (φ : SplitG2ThreeForms) :
    pathTransportThreeCochain A F [] φ = pullbackThreeForm F φ := by
  rfl

@[simp] theorem pathTransportFourCochain_nil
    {E : Type*} {K : FiniteOrientedCellComplex}
    (A : SplitG2GaugeConnection E)
    (F : SplitG2DiscreteCoframe K)
    (ψ : SplitG2FourForms) :
    pathTransportFourCochain A F [] ψ = pullbackFourForm F ψ := by
  rfl

theorem pathTransportThreeCochain_eq_of_invariant
    {E : Type*} {K : FiniteOrientedCellComplex}
    (A : SplitG2GaugeConnection E)
    (F : SplitG2DiscreteCoframe K)
    (path : List E)
    (φ : SplitG2ThreeForms)
    (hφ : pathPullbackForm A path φ = φ) :
    pathTransportThreeCochain A F path φ = pullbackThreeForm F φ := by
  simp [pathTransportThreeCochain, hφ]

theorem pathTransportFourCochain_eq_of_invariant
    {E : Type*} {K : FiniteOrientedCellComplex}
    (A : SplitG2GaugeConnection E)
    (F : SplitG2DiscreteCoframe K)
    (path : List E)
    (ψ : SplitG2FourForms)
    (hψ : pathPullbackForm A path ψ = ψ) :
    pathTransportFourCochain A F path ψ = pullbackFourForm F ψ := by
  simp [pathTransportFourCochain, hψ]

structure PathInvariantForm
    {E : Type*} (A : SplitG2GaugeConnection E)
    (ω : AlternatingMap ℚ imaginarySplitOctonion ℚ (Fin 3)) where
  invariant : ∀ path : List E, pathPullbackForm A path ω = ω

theorem pathTransportThreeCochain_eq
    {E : Type*} {K : FiniteOrientedCellComplex}
    (A : SplitG2GaugeConnection E)
    (F : SplitG2DiscreteCoframe K)
    (ω : SplitG2ThreeForms)
    (I : PathInvariantForm A ω)
    (path : List E) :
    pathTransportThreeCochain A F path ω =
      pullbackThreeForm F ω := by
  exact pathTransportThreeCochain_eq_of_invariant A F path ω (I.invariant path)

end InfoGeometry.Canonical
