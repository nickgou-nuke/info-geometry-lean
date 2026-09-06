import InfoGeometry.Optics.FiniteBKMDiracTransport
import InfoGeometry.Optics.HestenesCl11QGTCurvatureBridge

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.FiniteBKMDiracCurvatureBridge

open CanonicalZornCliffordRepresentation
open InfoGeometry.Optics.FiniteBKMDiracTransport
open InfoGeometry.Optics.HestenesCl11QGTCurvatureBridge
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
open InfoGeometry.Unified
open SouriauOnsagerBKM

variable {W V Point Tangent : Type*}
variable [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup V] [Module ℂ V]

/-- Conjugate a doubled-carrier endomorphism through an internal carrier
equivalence applied independently on both sheets. -/
def transportDoubledEnd (e : W ≃ₗ[ℂ] V) :
    Module.End ℂ (Fin 2 → W) →ₐ[ℂ] Module.End ℂ (Fin 2 → V) :=
  (doubledEquiv e).conjAlgEquiv ℂ

/-- Transport an operator-valued exterior two-form to an equivalent internal
carrier. -/
def transportTwoForm (e : W ≃ₗ[ℂ] V)
    (dQ : Point → Tangent → Tangent → Module.End ℂ (Fin 2 → W)) :
    Point → Tangent → Tangent → Module.End ℂ (Fin 2 → V) :=
  fun p X Y => transportDoubledEnd e (dQ p X Y)

theorem transportTwoForm_swap (e : W ≃ₗ[ℂ] V)
    (dQ : Point → Tangent → Tangent → Module.End ℂ (Fin 2 → W))
    (h : ∀ p X Y, dQ p Y X = -dQ p X Y) :
    ∀ p X Y, transportTwoForm e dQ p Y X =
      -transportTwoForm e dQ p X Y := by
  intro p X Y
  simp [transportTwoForm, h p X Y]

theorem transportTwoForm_same (e : W ≃ₗ[ℂ] V)
    (dQ : Point → Tangent → Tangent → Module.End ℂ (Fin 2 → W))
    (h : ∀ p X, dQ p X X = 0) :
    ∀ p X, transportTwoForm e dQ p X X = 0 := by
  intro p X
  simp [transportTwoForm, h p X]

/-- Simultaneously transporting the QGT one-form and its exterior derivative
is exactly `mapConnection` along conjugation of the doubled carrier. -/
theorem solderedQGTConnection_transport
    (e : W ≃ₗ[ℂ] V)
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → Module.End ℂ (Fin 2 → W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    solderedQGTConnection
        (fun p X => transportQGT e (Q p X))
        (transportTwoForm e dQ)
        (transportTwoForm_swap e dQ dQ_swap)
        (transportTwoForm_same e dQ dQ_same) =
      mapConnection (transportDoubledEnd e).toRingHom
        (solderedQGTConnection Q dQ dQ_swap dQ_same) := by
  rw [Connection.mk.injEq]
  constructor
  · funext p X
    exact QGTSoldering_transportQGT e (Q p X)
  · rfl

/-- Curvature commutes with exact transport of both operator-valued
connection channels. -/
theorem solderedQGTConnection_transport_curvature
    (e : W ≃ₗ[ℂ] V)
    (Q : Point → Tangent → QGTFourVector W)
    (dQ : Point → Tangent → Tangent → Module.End ℂ (Fin 2 → W))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (solderedQGTConnection
          (fun p X => transportQGT e (Q p X))
          (transportTwoForm e dQ)
          (transportTwoForm_swap e dQ dQ_swap)
          (transportTwoForm_same e dQ dQ_same)) p X Y =
      transportDoubledEnd e
        (curvature (solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y) := by
  rw [solderedQGTConnection_transport]
  exact (mapConnection_curvature (transportDoubledEnd e).toRingHom
    (solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y).symm

/-! ## Genuine BKM/Berry specialization -/

/-- A pointwise field of genuine integrated finite BKM/Berry operator QGTs. -/
def finiteBKMAndBerryField
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E) :
    Point → Tangent → QGTFourVector (FiniteHilbertSpace 16) :=
  fun p X => QGTFourVector.ofBKMTransformAndBerryReadout
    (D p X) (observable p X) (berryOperator p X) (left p X) (right p X)

/-- The same genuine BKM/Berry field in the sixteen-component Zorn Dirac
frame. -/
def diracBKMAndBerryField
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E) :
    Point → Tangent → QGTFourVector DiracSpinor16 :=
  fun p X => diracBKMAndBerryQGT
    (D p X) (observable p X) (berryOperator p X) (left p X) (right p X)

@[simp] theorem diracBKMAndBerryField_eq_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (p : Point) (X : Tangent) :
    diracBKMAndBerryField D observable berryOperator left right p X =
      transportQGT finiteHilbertSixteenDiracEquiv
        (finiteBKMAndBerryField D observable berryOperator left right p X) :=
  rfl

/-- The complete Dirac BKM/Berry curvature is the exact conjugate of its
finite-Hilbert-space source curvature. -/
theorem diracBKMAndBerry_curvature_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (solderedQGTConnection
          (diracBKMAndBerryField D observable berryOperator left right)
          (transportTwoForm finiteHilbertSixteenDiracEquiv dQ)
          (transportTwoForm_swap finiteHilbertSixteenDiracEquiv dQ dQ_swap)
          (transportTwoForm_same finiteHilbertSixteenDiracEquiv dQ dQ_same))
        p X Y =
      transportDoubledEnd finiteHilbertSixteenDiracEquiv
        (curvature
          (solderedQGTConnection
            (finiteBKMAndBerryField D observable berryOperator left right)
            dQ dQ_swap dQ_same) p X Y) := by
  exact solderedQGTConnection_transport_curvature
    finiteHilbertSixteenDiracEquiv
    (finiteBKMAndBerryField D observable berryOperator left right)
    dQ dQ_swap dQ_same p X Y

/-- Every curvature power trace of the genuine BKM/Berry connection is
unchanged by passage from the finite Hilbert carrier to the Zorn Dirac
carrier. -/
theorem diracBKMAndBerry_curvature_tracePower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (k : ℕ)
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        ((curvature
          (solderedQGTConnection
            (diracBKMAndBerryField D observable berryOperator left right)
            (transportTwoForm finiteHilbertSixteenDiracEquiv dQ)
            (transportTwoForm_swap finiteHilbertSixteenDiracEquiv dQ dQ_swap)
            (transportTwoForm_same finiteHilbertSixteenDiracEquiv dQ dQ_same))
          p X Y) ^ k) =
      LinearMap.trace ℂ (Fin 2 → FiniteHilbertSpace 16)
        ((curvature
          (solderedQGTConnection
            (finiteBKMAndBerryField D observable berryOperator left right)
            dQ dQ_swap dQ_same) p X Y) ^ k) := by
  rw [diracBKMAndBerry_curvature_transport]
  rw [← map_pow]
  exact LinearMap.trace_conj'
    ((curvature
      (solderedQGTConnection
        (finiteBKMAndBerryField D observable berryOperator left right)
        dQ dQ_swap dQ_same) p X Y) ^ k)
    (doubledEquiv finiteHilbertSixteenDiracEquiv)

/-- Honest theorem boundary for interpreting a transported finite BKM/Berry
field as a Hestenes split-quaternion coordinate field. -/
def IsHestenesRealization
    (colour : Fin 3)
    (symmetric antisymmetric : Point → Tangent → Fin 4 →
      InfoGeometry.Canonical.Cl11CoordinateHestenesBridge.HestenesCl11)
    (Q : Point → Tangent → QGTFourVector DiracSpinor16) : Prop :=
  ∀ p X, Q p X = hestenesDiracQGTFourVector colour
    (symmetric p X) (antisymmetric p X)

/-- A witnessed Hestenes realization gives equality of the corresponding
operator-valued connections, with no identification asserted without the
witness. -/
theorem hestenesQGTConnection_eq_of_realization
    (colour : Fin 3)
    (symmetric antisymmetric : Point → Tangent → Fin 4 →
      InfoGeometry.Canonical.Cl11CoordinateHestenesBridge.HestenesCl11)
    (Q : Point → Tangent → QGTFourVector DiracSpinor16)
    (hQ : IsHestenesRealization colour symmetric antisymmetric Q)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0) :
    solderedQGTConnection Q dQ dQ_swap dQ_same =
      solderedQGTConnection
        (diracQGTField
          (hestenesCoordinateField colour symmetric)
          (hestenesCoordinateField colour antisymmetric))
        dQ dQ_swap dQ_same := by
  rw [Connection.mk.injEq]
  constructor
  · funext p X
    change QGTSoldering (Q p X) =
      QGTSoldering
        (hestenesDiracQGTFourVector colour
          (symmetric p X) (antisymmetric p X))
    rw [hQ p X]
  · rfl

/-- Consequently a witnessed Hestenes realization identifies the complete
noncommutative curvatures. -/
theorem hestenesQGTCurvature_eq_of_realization
    (colour : Fin 3)
    (symmetric antisymmetric : Point → Tangent → Fin 4 →
      InfoGeometry.Canonical.Cl11CoordinateHestenesBridge.HestenesCl11)
    (Q : Point → Tangent → QGTFourVector DiracSpinor16)
    (hQ : IsHestenesRealization colour symmetric antisymmetric Q)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature (solderedQGTConnection Q dQ dQ_swap dQ_same) p X Y =
      curvature
        (solderedQGTConnection
          (diracQGTField
            (hestenesCoordinateField colour symmetric)
            (hestenesCoordinateField colour antisymmetric))
          dQ dQ_swap dQ_same) p X Y := by
  rw [hestenesQGTConnection_eq_of_realization
    colour symmetric antisymmetric Q hQ dQ dQ_swap dQ_same]

/-- If Hestenes fields genuinely realize the transported finite BKM/Berry
operators, their complete curvature is the transported finite curvature.
This is the explicit closure theorem joining Onsager--BKM, Berry, causal
soldering, the Zorn Dirac frame, and the Hestenes split-quaternion sector. -/
theorem hestenesRealization_curvature_eq_finiteBKMTransport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (colour : Fin 3)
    (symmetric antisymmetric : Point → Tangent → Fin 4 →
      InfoGeometry.Canonical.Cl11CoordinateHestenesBridge.HestenesCl11)
    (D : Point → Tangent → FaithfulDensityOperator 16)
    (observable : Point → Tangent → Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Point → Tangent → Fin 4 →
      InfoGeometry.Krein.DoubledSpace E)
    (hQ : IsHestenesRealization colour symmetric antisymmetric
      (diracBKMAndBerryField D observable berryOperator left right))
    (dQ : Point → Tangent → Tangent →
      Module.End ℂ (Fin 2 → FiniteHilbertSpace 16))
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (p : Point) (X Y : Tangent) :
    curvature
        (solderedQGTConnection
          (diracQGTField
            (hestenesCoordinateField colour symmetric)
            (hestenesCoordinateField colour antisymmetric))
          (transportTwoForm finiteHilbertSixteenDiracEquiv dQ)
          (transportTwoForm_swap finiteHilbertSixteenDiracEquiv dQ dQ_swap)
          (transportTwoForm_same finiteHilbertSixteenDiracEquiv dQ dQ_same))
        p X Y =
      transportDoubledEnd finiteHilbertSixteenDiracEquiv
        (curvature
          (solderedQGTConnection
            (finiteBKMAndBerryField D observable berryOperator left right)
            dQ dQ_swap dQ_same) p X Y) := by
  rw [← hestenesQGTCurvature_eq_of_realization
    colour symmetric antisymmetric
    (diracBKMAndBerryField D observable berryOperator left right) hQ
    (transportTwoForm finiteHilbertSixteenDiracEquiv dQ)
    (transportTwoForm_swap finiteHilbertSixteenDiracEquiv dQ dQ_swap)
    (transportTwoForm_same finiteHilbertSixteenDiracEquiv dQ dQ_same)]
  exact diracBKMAndBerry_curvature_transport
    D observable berryOperator left right dQ dQ_swap dQ_same p X Y

end InfoGeometry.Optics.FiniteBKMDiracCurvatureBridge
