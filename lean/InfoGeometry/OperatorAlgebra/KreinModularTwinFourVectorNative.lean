import InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
import InfoGeometry.Canonical.HestenesKreinModularGeometry

/-! Native bounded-operator Krein twin.  Composition is explicit: a bounded
continuous linear map is not treated as an associative ring by notation. -/
noncomputable section
namespace InfoGeometry.OperatorAlgebra.KreinModularTwinFourVectorNative

open InfoGeometry.OperatorAlgebra.TwoFourOperatorVectorZorn
open InfoGeometry.Canonical.HestenesKreinModularGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
abbrev EndE (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] := RealEnd E

def kreinConjugate (J T : EndE E) : EndE E := J.comp (T.comp J)

theorem kreinConjugate_involutive {J : EndE E}
    (hJ : J.comp J = ContinuousLinearMap.id ℝ E) (T : EndE E) :
    kreinConjugate J (kreinConjugate J T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  have hTx : J (J (T x)) = T x := by
    have h := congrArg (fun f : EndE E => f (T x)) hJ
    simpa [ContinuousLinearMap.comp_apply] using h
  have hxx : J (J x) = x := by
    have h := congrArg (fun f : EndE E => f x) hJ
    simpa [ContinuousLinearMap.comp_apply] using h
  simp [kreinConjugate, ContinuousLinearMap.comp_apply, hTx, hxx]

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

theorem polarize_plus_scalar (uPlus uMinus : Fin 3 → EndE E) :
    (K.polarize (K.fourVectorCarrier uPlus uMinus)).plus.scalar =
      K.plusDatum.modularGenerator := by
  simpa [polarize, fourVectorCarrier, kreinConjugate,
    ContinuousLinearMap.comp_apply] using K.plusDatum.generator_krein_selfadjoint

theorem polarize_minus_scalar (uPlus uMinus : Fin 3 → EndE E) :
    (K.polarize (K.fourVectorCarrier uPlus uMinus)).minus.scalar =
      K.minusDatum.modularGenerator := by
  simpa [polarize, fourVectorCarrier, kreinConjugate,
    ContinuousLinearMap.comp_apply] using K.minusDatum.generator_krein_selfadjoint

end KreinModularTwin
end InfoGeometry.OperatorAlgebra.KreinModularTwinFourVectorNative
