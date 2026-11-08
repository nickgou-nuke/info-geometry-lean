import InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Optics.FiniteBKMDiracTransport

open CanonicalZornCliffordRepresentation
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.QuaternionCl44QGTNormedFrechetRealization
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Unified
open SouriauOnsagerBKM

variable {W V : Type*}
variable [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup V] [Module ℂ V]

/-- Transport all four operator coefficients through a change of internal
carrier. -/
def transportFourVector (e : W ≃ₗ[ℂ] V) (v : OperatorFourVector W) :
    OperatorFourVector V :=
  fun i => e.conjAlgEquiv ℂ (v i)

/-- Transport the BKM and Berry channels through the same internal frame. -/
def transportQGT (e : W ≃ₗ[ℂ] V) (Q : QGTFourVector W) : QGTFourVector V where
  symmetricBKM := transportFourVector e Q.symmetricBKM
  antisymmetricBerry := transportFourVector e Q.antisymmetricBerry

@[simp] theorem transportQGT_totalOperator_apply
    (e : W ≃ₗ[ℂ] V) (Q : QGTFourVector W) (i : Fin 4) :
    (transportQGT e Q).totalOperator i =
      e.conjAlgEquiv ℂ (Q.totalOperator i) := by
  simp [transportQGT, transportFourVector, QGTFourVector.totalOperator]

/-- Apply an internal carrier equivalence independently on the two causal
sheets. -/
def doubledEquiv (e : W ≃ₗ[ℂ] V) : (Fin 2 → W) ≃ₗ[ℂ] (Fin 2 → V) :=
  LinearEquiv.piCongrRight (fun _ => e)

/-- Causal soldering is natural under an arbitrary internal linear
equivalence. -/
theorem QGTSoldering_transportQGT
    (e : W ≃ₗ[ℂ] V) (Q : QGTFourVector W) :
    QGTSoldering (transportQGT e Q) =
      (doubledEquiv e).conjAlgEquiv ℂ (QGTSoldering Q) := by
  apply LinearMap.ext
  intro ψ
  funext i
  fin_cases i <;>
    simp [QGTSoldering_apply, operatorSoldering_apply,
      transportQGT, transportFourVector, doubledEquiv,
      LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply]

/-! ## Naturality of internal Bogoliubov frames -/

/-- Transport an invertible internal frame through a carrier equivalence. -/
def transportInternalUnit (e : W ≃ₗ[ℂ] V) (u : (Module.End ℂ W)ˣ) :
    (Module.End ℂ V)ˣ :=
  Units.map (e.conjAlgEquiv ℂ).toMonoidHom u

@[simp] theorem transportInternalUnit_val
    (e : W ≃ₗ[ℂ] V) (u : (Module.End ℂ W)ˣ) :
    (transportInternalUnit e u : Module.End ℂ V) =
      e.conjAlgEquiv ℂ (u : Module.End ℂ W) :=
  rfl

/-- Coefficientwise finite Bogoliubov conjugation commutes with an exact
change of internal carrier. -/
theorem transportQGT_internalConjugation
    (e : W ≃ₗ[ℂ] V) (u : (Module.End ℂ W)ˣ) (Q : QGTFourVector W) :
    transportQGT e (qgtInternalConjugation u Q) =
      qgtInternalConjugation (transportInternalUnit e u) (transportQGT e Q) := by
  cases Q with
  | mk symmetric antisymmetric =>
      rw [QGTFourVector.mk.injEq]
      constructor <;> funext i <;>
        simp [transportQGT, transportFourVector, qgtInternalConjugation,
          internalConjugateFourVector, innerConjugation,
          transportInternalUnit]

/-- Infinitesimal inner Bogoliubov derivations commute with exact carrier
transport. -/
theorem transportFourVector_internalCommutator
    (e : W ≃ₗ[ℂ] V) (X : Module.End ℂ W) (v : OperatorFourVector W) :
    transportFourVector e (internalCommutatorFourVector X v) =
      internalCommutatorFourVector (e.conjAlgEquiv ℂ X)
        (transportFourVector e v) := by
  funext i
  simp [transportFourVector, internalCommutatorFourVector,
    internalCommutator]

/-- Both QGT channels intertwine the infinitesimal Bogoliubov action. -/
theorem transportQGT_internalCommutator
    (e : W ≃ₗ[ℂ] V) (X : Module.End ℂ W) (Q : QGTFourVector W) :
    transportQGT e (qgtInternalCommutator X Q) =
      qgtInternalCommutator (e.conjAlgEquiv ℂ X) (transportQGT e Q) := by
  cases Q with
  | mk symmetric antisymmetric =>
      simp [transportQGT, qgtInternalCommutator,
        transportFourVector_internalCommutator]

/-! ## Canonical sixteen-coordinate Dirac frame -/

/-- Reindex sixteen coordinates as two ordered blocks of eight. -/
def finSixteenSumEightEquiv : Fin 8 ⊕ Fin 8 ≃ Fin 16 :=
  finSumFinEquiv.trans (finCongr (by norm_num))

/-- Split a function on a sum into its two component functions. -/
def sumFunctionProdEquiv :
    ((Fin 8 ⊕ Fin 8) → ℂ) ≃ₗ[ℂ] ((Fin 8 → ℂ) × (Fin 8 → ℂ)) where
  toFun f := (fun i => f (.inl i), fun i => f (.inr i))
  invFun p := Sum.elim p.1 p.2
  left_inv f := by ext i <;> cases i <;> rfl
  right_inv p := by ext i <;> rfl
  map_add' f g := by ext i <;> rfl
  map_smul' c f := by ext i <;> rfl

/-- Native coordinate equivalence from the finite BKM carrier of dimension
sixteen to the existing Zorn-coordinate Dirac carrier. -/
def finiteHilbertSixteenCoordinateEquiv :
    FiniteHilbertSpace 16 ≃ₗ[ℂ] DiracSpinorCoordinates :=
  (WithLp.linearEquiv 2 ℂ (Fin 16 → ℂ)).trans
    (((LinearEquiv.piCongrLeft ℂ (fun _ : Fin 16 => ℂ)
      finSixteenSumEightEquiv).symm).trans sumFunctionProdEquiv)

/-- Canonical transport from the genuine finite BKM carrier to the
sixteen-component Zorn Dirac spinor. -/
def finiteHilbertSixteenDiracEquiv :
    FiniteHilbertSpace 16 ≃ₗ[ℂ] DiracSpinor16 :=
  finiteHilbertSixteenCoordinateEquiv.trans diracSpinorCoordinateEquiv.symm

/-- The genuine integrated BKM/Berry operator four-vector, transported to the
Zorn Dirac carrier without replacing either channel by scalar coordinates. -/
def diracBKMAndBerryQGT
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (observable : Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E) :
    QGTFourVector DiracSpinor16 :=
  transportQGT finiteHilbertSixteenDiracEquiv
    (QGTFourVector.ofBKMTransformAndBerryReadout
      D observable berryOperator left right)

/-- The Dirac realization retains the actual Kubo--Mori transform and Berry
readout, conjugated through the exact sixteen-coordinate frame. -/
@[simp] theorem diracBKMAndBerryQGT_totalOperator_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (observable : Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E)
    (i : Fin 4) :
    (diracBKMAndBerryQGT D observable berryOperator left right).totalOperator i =
      finiteHilbertSixteenDiracEquiv.conjAlgEquiv ℂ
        ((D.kuboMoriTransform (observable i)).toLinearMap +
          Complex.I • centralOperator (W := FiniteHilbertSpace 16)
            ((InfoGeometry.Quantum.GeometricQuantumTensor.berryOfOperator
              (E := E) (berryOperator i) (left i) (right i) : ℝ) : ℂ)) := by
  rw [diracBKMAndBerryQGT, transportQGT_totalOperator_apply,
    QGTFourVector.ofBKMTransformAndBerryReadout_totalOperator_apply]

/-- The complete BKM/Berry causal soldering on the Dirac carrier is exactly
the conjugate of the original finite soldering. -/
theorem QGTSoldering_diracBKMAndBerryQGT
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : FaithfulDensityOperator 16)
    (observable : Fin 4 → FiniteOperatorAlgebra 16)
    (berryOperator : Fin 4 →
      InfoGeometry.Krein.DoubledSpace E →L[ℝ]
        InfoGeometry.Krein.DoubledSpace E)
    (left right : Fin 4 → InfoGeometry.Krein.DoubledSpace E) :
    QGTSoldering (diracBKMAndBerryQGT D observable berryOperator left right) =
      (doubledEquiv finiteHilbertSixteenDiracEquiv).conjAlgEquiv ℂ
        (QGTSoldering
          (QGTFourVector.ofBKMTransformAndBerryReadout
            D observable berryOperator left right)) := by
  exact QGTSoldering_transportQGT _ _

end InfoGeometry.Optics.FiniteBKMDiracTransport
