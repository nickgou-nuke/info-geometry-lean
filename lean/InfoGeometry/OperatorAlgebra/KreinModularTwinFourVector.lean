import InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
import InfoGeometry.Canonical.HestenesKreinModularGeometry

/-!
# Krein polarization of twin modular four-operator vectors

This owner records the finite, real-linear part of the PR162 construction.
It does not identify Krein conjugation with Tomita conjugation or a deck
transformation.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.KreinModularTwinFourVector

open InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
open InfoGeometry.Canonical.HestenesKreinModularGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev EndE (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := RealEnd E

def kreinConjugate (J T : EndE E) : EndE E := J * T * J

theorem kreinConjugate_involutive {J : EndE E} (hJ : J * J = 1) (T : EndE E) :
    kreinConjugate J (kreinConjugate J T) = T := by
  unfold kreinConjugate
  calc
    J * (J * T * J) * J = (J * J) * T * (J * J) := by noncomm_ring
    _ = T := by rw [hJ]; simp

structure KreinModularTwin (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  plusDatum : KreinHestenesModularDatum E
  minusDatum : KreinHestenesModularDatum E

namespace KreinModularTwin

variable (K : KreinModularTwin E)

def fourVectorCarrier (uPlus uMinus : Fin 3 → EndE E) :
    TwinFourOperatorVector (A := EndE E) :=
  ⟨⟨K.plusDatum.modularGenerator, uPlus⟩,
    ⟨K.minusDatum.modularGenerator, uMinus⟩⟩

def polarize (X : TwinFourOperatorVector (A := EndE E)) :
    TwinFourOperatorVector (A := EndE E) :=
  ⟨⟨kreinConjugate K.plusDatum.fundamentalSymmetry X.plus.scalar,
      fun i => kreinConjugate K.plusDatum.fundamentalSymmetry (X.plus.spatial i)⟩,
    ⟨kreinConjugate K.minusDatum.fundamentalSymmetry X.minus.scalar,
      fun i => kreinConjugate K.minusDatum.fundamentalSymmetry (X.minus.spatial i)⟩⟩

theorem plus_fundamental_sq :
    K.plusDatum.fundamentalSymmetry * K.plusDatum.fundamentalSymmetry = 1 := by
  simpa using K.plusDatum.fundamentalSymmetry_involution

theorem minus_fundamental_sq :
    K.minusDatum.fundamentalSymmetry * K.minusDatum.fundamentalSymmetry = 1 := by
  simpa using K.minusDatum.fundamentalSymmetry_involution

theorem polarize_fourVectorCarrier_scalars (uPlus uMinus : Fin 3 → EndE E) :
    (K.polarize (K.fourVectorCarrier uPlus uMinus)).plus.scalar =
        K.plusDatum.modularGenerator ∧
      (K.polarize (K.fourVectorCarrier uPlus uMinus)).minus.scalar =
        K.minusDatum.modularGenerator := by
  constructor
  · simpa [polarize, fourVectorCarrier, kreinConjugate] using
      K.plusDatum.generator_krein_selfadjoint
  · simpa [polarize, fourVectorCarrier, kreinConjugate] using
      K.minusDatum.generator_krein_selfadjoint

def IsPlusKreinOdd (T : EndE E) : Prop :=
  kreinConjugate K.plusDatum.fundamentalSymmetry T = -T

def IsMinusKreinOdd (T : EndE E) : Prop :=
  kreinConjugate K.minusDatum.fundamentalSymmetry T = -T

def nativeZorn (uPlus uMinus : Fin 3 → EndE E) :
    InfoGeometry.Canonical.OperatorZornMatrix (EndE E) :=
  toZorn (K.fourVectorCarrier uPlus uMinus)

end KreinModularTwin
end InfoGeometry.OperatorAlgebra.KreinModularTwinFourVector
