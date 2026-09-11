import InfoGeometry.Canonical.HodgeStar4DFiniteLinearBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HestenesBivectorCarrier
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Signed Hodge operators on finite and Clifford carriers

This owner packages the two existing Lorentzian Hodge realizations behind one
native linear-operator interface: the coordinate six-component two-form
carrier and the Clifford bivector submodule.  Both carry the proved law
`star² = -id`; no identification of the two carriers is asserted.
-/

namespace InfoGeometry.Canonical.SignedHodgeCliffordOperatorBridge

open InfoGeometry.Canonical.CliffordParity
open InfoGeometry.Canonical.HestenesBivectorCarrier

structure SignedHodgeOperator (R W : Type*)
    [CommRing R] [AddCommGroup W] [Module R W] where
  operator : W →ₗ[R] W
  squareSign : R
  square : operator.comp operator = squareSign • LinearMap.id

theorem SignedHodgeOperator.square_apply
    {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (S : SignedHodgeOperator R W) (w : W) :
    S.operator (S.operator w) = S.squareSign • w := by
  have h := congrArg (fun f : W →ₗ[R] W => f w) S.square
  simpa [LinearMap.comp_apply] using h

noncomputable def finiteLorentzianHodge :
    SignedHodgeOperator ℂ
      InfoGeometry.Canonical.HodgeStar4DFinite.TwoFormC where
  operator := InfoGeometry.Canonical.HodgeStar4DFiniteLinearBridge.hodgeStarLinear
  squareSign := -1
  square :=
    InfoGeometry.Canonical.HodgeStar4DFiniteLinearBridge.hodgeStarLinear_signed_square

theorem finiteLorentzianHodge_squareSign :
    finiteLorentzianHodge.squareSign = (-1 : ℂ) := rfl

theorem finiteLorentzianHodge_square_apply (F :
    InfoGeometry.Canonical.HodgeStar4DFinite.TwoFormC) :
    finiteLorentzianHodge.operator (finiteLorentzianHodge.operator F) =
      (-1 : ℂ) • F := by
  exact finiteLorentzianHodge.square_apply F

noncomputable def CliffordBivectorHodge
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M)
    [HasVolumeElement R M Q]
    [InfoGeometry.Canonical.HestenesBivectorCarrier.HasSpacetimeBasis
      (R := R) (M := M) Q] :
    SignedHodgeOperator R
      (InfoGeometry.Canonical.HestenesBivectorCarrier.Bivector13 Q) where
  operator := InfoGeometry.Canonical.HestenesBivectorCarrier.hodgeBivector Q
  squareSign := -1
  square := by
    simpa using
      (InfoGeometry.Canonical.HestenesBivectorCarrier.hodgeBivector_comp_self Q)

theorem CliffordBivectorHodge_squareSign
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M)
    [HasVolumeElement R M Q]
    [InfoGeometry.Canonical.HestenesBivectorCarrier.HasSpacetimeBasis
      (R := R) (M := M) Q] :
    (CliffordBivectorHodge Q).squareSign = (-1 : R) := rfl

theorem CliffordBivectorHodge_square_apply
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M)
    [HasVolumeElement R M Q]
    [InfoGeometry.Canonical.HestenesBivectorCarrier.HasSpacetimeBasis
      (R := R) (M := M) Q]
    (B : InfoGeometry.Canonical.HestenesBivectorCarrier.Bivector13 Q) :
    (CliffordBivectorHodge Q).operator
        ((CliffordBivectorHodge Q).operator B) = (-1 : R) • B := by
  exact (CliffordBivectorHodge Q).square_apply B

def basisBivectorMem
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q] (i : Fin 6) :
    basisBivector Q i ∈ Bivector13 Q :=
  Submodule.subset_span ⟨i, rfl⟩

noncomputable def bivectorBasis
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q]
    (hB : LinearIndependent R (basisBivector Q)) :
    Module.Basis (Fin 6) R (Bivector13 Q) := by
  change Module.Basis (Fin 6) R
    (Submodule.span R (Set.range (basisBivector Q)))
  exact Module.Basis.span hB

@[simp] theorem bivectorBasis_apply
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q]
    (hB : LinearIndependent R (basisBivector Q)) (i : Fin 6) :
    (bivectorBasis Q hB i : CliffordAlgebra Q) = basisBivector Q i := by
  exact Module.Basis.span_apply hB i

noncomputable def bivectorCoordinateEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q]
    (hB : LinearIndependent R (basisBivector Q)) :
    Bivector13 Q ≃ₗ[R] (Fin 6 → R) :=
  (bivectorBasis Q hB).equivFun

@[simp] theorem bivectorCoordinateEquiv_apply_basis
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q]
    (hB : LinearIndependent R (basisBivector Q)) (i : Fin 6) :
    bivectorCoordinateEquiv Q hB (bivectorBasis Q hB i) =
      Pi.single i 1 := by
  ext j
  classical
  by_cases h : j = i
  · subst j
    simp [bivectorCoordinateEquiv, Module.Basis.equivFun, Finsupp.single, Pi.single]
  · simp [bivectorCoordinateEquiv, Module.Basis.equivFun, Finsupp.single,
      Pi.single, h]

theorem coordinateEquiv_smul_basis
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q]
    (hB : LinearIndependent R (basisBivector Q)) (r : R) (i : Fin 6) :
    bivectorCoordinateEquiv Q hB (r • bivectorBasis Q hB i) =
      r • (Pi.single i (1 : R) : Fin 6 → R) := by
  rw [map_smul, bivectorCoordinateEquiv_apply_basis]

noncomputable def coordinateHodge
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q]
    (hB : LinearIndependent R (basisBivector Q)) :
    (Fin 6 → R) →ₗ[R] (Fin 6 → R) :=
  (bivectorCoordinateEquiv Q hB).toLinearMap.comp
    ((hodgeBivector Q).comp (bivectorCoordinateEquiv Q hB).symm.toLinearMap)

theorem coordinateHodge_square
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q]
    (hB : LinearIndependent R (basisBivector Q)) :
    (coordinateHodge Q hB).comp (coordinateHodge Q hB) =
      -(LinearMap.id : (Fin 6 → R) →ₗ[R] (Fin 6 → R)) := by
  let e := bivectorCoordinateEquiv Q hB
  let h := hodgeBivector Q
  have hh : h.comp h =
      -(LinearMap.id : Bivector13 Q →ₗ[R] Bivector13 Q) :=
    hodgeBivector_comp_self Q
  apply LinearMap.ext
  intro x
  change e (h (e.symm (e (h (e.symm x))))) =
    (-(LinearMap.id : (Fin 6 → R) →ₗ[R] (Fin 6 → R))) x
  rw [e.symm_apply_apply]
  rw [show h (h (e.symm x)) = -e.symm x by
    have hx := congrArg (fun f : Bivector13 Q →ₗ[R] Bivector13 Q => f (e.symm x)) hh
    simpa [LinearMap.comp_apply] using hx]
  simp

def hodgeBivectorTarget (i : Fin 6) : Fin 6 :=
  match i with
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2

def hodgeBivectorMetricFactor
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q] (i : Fin 6) : R :=
  match i with
  | 0 => -(Q (gamma Q 0) * Q (gamma Q 1))
  | 1 => -(Q (gamma Q 0) * Q (gamma Q 2))
  | 2 => -(Q (gamma Q 0) * Q (gamma Q 3))
  | 3 => -(Q (gamma Q 2) * Q (gamma Q 3))
  | 4 => -(Q (gamma Q 3) * Q (gamma Q 1))
  | 5 => -(Q (gamma Q 1) * Q (gamma Q 2))

theorem hodgeBivector_basis_table
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q] (i : Fin 6) :
    ((hodgeBivector Q) ⟨basisBivector Q i, basisBivectorMem Q i⟩ :
        CliffordAlgebra Q) =
      algebraMap R (CliffordAlgebra Q) (hodgeBivectorMetricFactor Q i) *
        basisBivector Q (hodgeBivectorTarget i) := by
  fin_cases i
  · simpa [hodgeBivector, hodgeBivectorMetricFactor, hodgeBivectorTarget,
      basisBivectorMem] using hodge_basis_0 Q
  · simpa [hodgeBivector, hodgeBivectorMetricFactor, hodgeBivectorTarget,
      basisBivectorMem] using hodge_basis_1 Q
  · simpa [hodgeBivector, hodgeBivectorMetricFactor, hodgeBivectorTarget,
      basisBivectorMem] using hodge_basis_2 Q
  · simpa [hodgeBivector, hodgeBivectorMetricFactor, hodgeBivectorTarget,
      basisBivectorMem] using hodge_basis_3 Q
  · simpa [hodgeBivector, hodgeBivectorMetricFactor, hodgeBivectorTarget,
      basisBivectorMem] using hodge_basis_4 Q
  · simpa [hodgeBivector, hodgeBivectorMetricFactor, hodgeBivectorTarget,
      basisBivectorMem] using hodge_basis_5 Q

theorem coordinateHodge_apply_basis
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) [HasVolumeElement R M Q]
    [HasSpacetimeBasis Q]
    (hB : LinearIndependent R (basisBivector Q)) (i : Fin 6) :
    coordinateHodge Q hB (Pi.single i (1 : R)) =
      hodgeBivectorMetricFactor Q i •
        (Pi.single (hodgeBivectorTarget i) (1 : R) : Fin 6 → R) := by
  rw [← bivectorCoordinateEquiv_apply_basis Q hB i]
  simp only [coordinateHodge, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [(bivectorCoordinateEquiv Q hB).symm_apply_apply]
  rw [← coordinateEquiv_smul_basis Q hB
    (hodgeBivectorMetricFactor Q i) (hodgeBivectorTarget i)]
  have hi : hodgeBivector Q (bivectorBasis Q hB i) =
      hodgeBivectorMetricFactor Q i •
        bivectorBasis Q hB (hodgeBivectorTarget i) := by
    have hbi : bivectorBasis Q hB i =
        ⟨basisBivector Q i, basisBivectorMem Q i⟩ := by
      apply Subtype.ext
      exact bivectorBasis_apply Q hB i
    rw [hbi]
    apply Subtype.ext
    simpa [Algebra.smul_def, bivectorBasis_apply] using
      hodgeBivector_basis_table Q i
  rw [hi]

end InfoGeometry.Canonical.SignedHodgeCliffordOperatorBridge
