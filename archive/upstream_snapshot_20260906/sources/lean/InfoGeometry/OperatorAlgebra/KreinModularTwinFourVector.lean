import InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
import InfoGeometry.Canonical.HestenesKreinModularGeometry

/-!
# Krein polarization of twin modular four-operator vectors

Each sheet carries its own real Hestenes--Krein modular datum.  The diagonal
operator in each four-vector is the corresponding modular generator; the
three remaining entries are arbitrary operator rails.  Conjugation by the
sheet's Krein fundamental symmetry is applied componentwise.

This owner is real-linear and bounded.  It does not identify the Krein
fundamental symmetry with Tomita modular conjugation, Kramers time reversal,
or the Klein deck glide.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KreinModularTwinFourVector

open InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
open InfoGeometry.Canonical.HestenesKreinModularGeometry

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev EndE := RealEnd E

/-- Conjugation by a real Krein fundamental symmetry. -/
def kreinConjugate (J T : EndE) : EndE :=
  J * T * J

/-- Conjugation by a square-one symmetry is involutive. -/
theorem kreinConjugate_involutive
    {J : EndE} (hJ : J * J = 1) (T : EndE) :
    kreinConjugate J (kreinConjugate J T) = T := by
  unfold kreinConjugate
  noncomm_ring [hJ]

/-- Two independent real modular/Krein sheets. -/
structure KreinModularTwin (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  plusDatum : KreinHestenesModularDatum E
  minusDatum : KreinHestenesModularDatum E

namespace KreinModularTwin

variable (K : KreinModularTwin E)

/-- Put both modular generators and two three-operator rails into the exact
`4+4` carrier. -/
def fourVectorCarrier (uPlus uMinus : Fin 3 -> EndE) :
    TwinFourOperatorVector EndE :=
  ⟨⟨K.plusDatum.modularGenerator, uPlus⟩,
    ⟨K.minusDatum.modularGenerator, uMinus⟩⟩

/-- Componentwise Krein conjugation on the two four-vector sheets. -/
def polarize (X : TwinFourOperatorVector EndE) :
    TwinFourOperatorVector EndE :=
  ⟨⟨kreinConjugate K.plusDatum.fundamentalSymmetry X.plus.scalar,
      fun i => kreinConjugate K.plusDatum.fundamentalSymmetry
        (X.plus.spatial i)⟩,
    ⟨kreinConjugate K.minusDatum.fundamentalSymmetry X.minus.scalar,
      fun i => kreinConjugate K.minusDatum.fundamentalSymmetry
        (X.minus.spatial i)⟩⟩

/-- Each fundamental symmetry is square one in the endomorphism ring. -/
theorem plus_fundamental_sq :
    K.plusDatum.fundamentalSymmetry *
        K.plusDatum.fundamentalSymmetry = 1 := by
  simpa using K.plusDatum.fundamentalSymmetry_involution

theorem minus_fundamental_sq :
    K.minusDatum.fundamentalSymmetry *
        K.minusDatum.fundamentalSymmetry = 1 := by
  simpa using K.minusDatum.fundamentalSymmetry_involution

/-- The componentwise Krein polarization is involutive. -/
@[simp] theorem polarize_involutive
    (X : TwinFourOperatorVector EndE) :
    K.polarize (K.polarize X) = X := by
  apply TwinFourOperatorVector.ext
  · apply FourOperatorVector.ext
    · exact kreinConjugate_involutive K.plus_fundamental_sq X.plus.scalar
    · funext i
      exact kreinConjugate_involutive K.plus_fundamental_sq
        (X.plus.spatial i)
  · apply FourOperatorVector.ext
    · exact kreinConjugate_involutive K.minus_fundamental_sq X.minus.scalar
    · funext i
      exact kreinConjugate_involutive K.minus_fundamental_sq
        (X.minus.spatial i)

/-- Both stored modular generators are Krein self-adjoint and therefore fixed
by the corresponding polarization. -/
theorem polarize_fourVectorCarrier_scalars
    (uPlus uMinus : Fin 3 -> EndE) :
    (K.polarize (K.fourVectorCarrier uPlus uMinus)).plus.scalar =
        K.plusDatum.modularGenerator ∧
      (K.polarize (K.fourVectorCarrier uPlus uMinus)).minus.scalar =
        K.minusDatum.modularGenerator := by
  constructor
  · simpa [polarize, fourVectorCarrier, kreinConjugate] using
      K.plusDatum.generator_krein_selfadjoint
  · simpa [polarize, fourVectorCarrier, kreinConjugate] using
      K.minusDatum.generator_krein_selfadjoint

/-- Krein-even operator on the positive sheet. -/
def IsPlusKreinEven (T : EndE) : Prop :=
  kreinConjugate K.plusDatum.fundamentalSymmetry T = T

/-- Krein-odd operator on the positive sheet. -/
def IsPlusKreinOdd (T : EndE) : Prop :=
  kreinConjugate K.plusDatum.fundamentalSymmetry T = -T

/-- Krein-even operator on the negative sheet. -/
def IsMinusKreinEven (T : EndE) : Prop :=
  kreinConjugate K.minusDatum.fundamentalSymmetry T = T

/-- Krein-odd operator on the negative sheet. -/
def IsMinusKreinOdd (T : EndE) : Prop :=
  kreinConjugate K.minusDatum.fundamentalSymmetry T = -T

/-- If all rail operators have assigned Krein parity, polarization fixes the
modular generators and applies exactly those signs to the rails. -/
theorem polarize_fourVectorCarrier_of_odd_rails
    (uPlus uMinus : Fin 3 -> EndE)
    (hPlus : forall i, K.IsPlusKreinOdd (uPlus i))
    (hMinus : forall i, K.IsMinusKreinOdd (uMinus i)) :
    K.polarize (K.fourVectorCarrier uPlus uMinus) =
      ⟨⟨K.plusDatum.modularGenerator, -uPlus⟩,
        ⟨K.minusDatum.modularGenerator, -uMinus⟩⟩ := by
  apply TwinFourOperatorVector.ext
  · apply FourOperatorVector.ext
    · simpa [polarize, fourVectorCarrier, kreinConjugate] using
        K.plusDatum.generator_krein_selfadjoint
    · funext i
      exact hPlus i
  · apply FourOperatorVector.ext
    · simpa [polarize, fourVectorCarrier, kreinConjugate] using
        K.minusDatum.generator_krein_selfadjoint
    · funext i
      exact hMinus i

/-- Native operator-Zorn realization of the polarized twin. -/
def nativeZorn (uPlus uMinus : Fin 3 -> EndE) :
    InfoGeometry.Canonical.OperatorZornMatrix EndE :=
  toNativeZorn (K.fourVectorCarrier uPlus uMinus)

end KreinModularTwin

end InfoGeometry.OperatorAlgebra.KreinModularTwinFourVector
