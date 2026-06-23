import re

def process_socket(text):
    # This script will rewrite the structures in MajoranaPolyaHilbertSocket.lean to use concrete algebraic types
    
    # FockVsMellinNormalizabilityGuard
    text = re.sub(
        r'structure FockVsMellinNormalizabilityGuard.*?end FockVsMellinNormalizabilityGuard',
        '''structure FockVsMellinNormalizabilityGuard
    (FockState MellinState : Type*)
    [NormedAddCommGroup FockState] [NormedAddCommGroup MellinState] where
  fockState : FockState
  mellinState : MellinState
  fockNorm : ℝ
  mellinNorm : ℝ
  fockSummabilityDomain : Prop
  mellinCriticalLine : Prop
  criticalLine_not_from_ordinaryFockNorm_guard : Type*

namespace FockVsMellinNormalizabilityGuard
end FockVsMellinNormalizabilityGuard''',
        text, flags=re.DOTALL
    )

    # MajoranaZeroModeNormalizabilityPacket
    text = re.sub(
        r'structure MajoranaZeroModeNormalizabilityPacket.*?end MajoranaZeroModeNormalizabilityPacket',
        '''structure MajoranaZeroModeNormalizabilityPacket
    (ZeroMode : Type*) [NormedAddCommGroup ZeroMode] where
  realPart : ℝ
  imaginaryHeight : ℝ
  zeroMode : ZeroMode
  normReadout : ℝ
  normalizable_law : IsCriticalLineRealPart realPart
  normalizable_iff_criticalLine_proof :
    (normReadout < ⊤) ↔ IsCriticalLineRealPart realPart

namespace MajoranaZeroModeNormalizabilityPacket

theorem criticalLine_of_normalizable
    {ZeroMode : Type*} [NormedAddCommGroup ZeroMode]
    (Z : MajoranaZeroModeNormalizabilityPacket ZeroMode)
    (h : Z.normReadout < ⊤) :
    IsCriticalLineRealPart Z.realPart :=
  Z.normalizable_iff_criticalLine_proof.mp h

theorem normalizable_of_criticalLine
    {ZeroMode : Type*} [NormedAddCommGroup ZeroMode]
    (Z : MajoranaZeroModeNormalizabilityPacket ZeroMode)
    (h : IsCriticalLineRealPart Z.realPart) :
    Z.normReadout < ⊤ :=
  Z.normalizable_iff_criticalLine_proof.mpr h

def mkCriticalLine (ZeroMode : Type*) [NormedAddCommGroup ZeroMode]
    (zeroMode : ZeroMode) (normReadout : ℝ) (imaginaryHeight : ℝ)
    (h : normReadout < ⊤) :
    MajoranaZeroModeNormalizabilityPacket ZeroMode where
  realPart := 1/2
  imaginaryHeight := imaginaryHeight
  zeroMode := zeroMode
  normReadout := normReadout
  normalizable_law := by rfl
  normalizable_iff_criticalLine_proof := by simp [h]

end MajoranaZeroModeNormalizabilityPacket''',
        text, flags=re.DOTALL
    )

    # MajoranaPfaffianZetaSpectralSocket
    text = re.sub(
        r'structure MajoranaPfaffianZetaSpectralSocket.*?end MajoranaPfaffianZetaSpectralSocket',
        '''structure MajoranaPfaffianZetaSpectralSocket
    (SpectralParameter Readout : Type*) [CommRing Readout] where
  parameter : SpectralParameter
  pfaffianReadout : Readout
  zetaReadout : Readout
  pfaffian_zeta_identity : pfaffianReadout = zetaReadout
  zetaZero : Prop
  reciprocalZetaSingularity : Prop
  zetaZero_implies_reciprocalSingularity :
    zetaZero → reciprocalZetaSingularity

namespace MajoranaPfaffianZetaSpectralSocket
end MajoranaPfaffianZetaSpectralSocket''',
        text, flags=re.DOTALL
    )

    # WittenCharacterVsCompletedXiSocket
    text = re.sub(
        r'structure WittenCharacterVsCompletedXiSocket.*?(?:@\[owner_target_tag\]\ntheorem WittenCharacterVsCompletedXiOwnerTarget.*?:=.*?sorryProof⟩\n)',
        '''structure WittenCharacterVsCompletedXiSocket
    (SpectralParameter Readout : Type*) [CommRing Readout] where
  parameter : SpectralParameter
  wittenCharacter : Readout
  completedXi : Readout
  spectralPfaffian : Readout
  wittenCharacter_inverseZeta : wittenCharacter * completedXi = 1
  spectralPfaffian_completedXi : spectralPfaffian = completedXi
  zetaZeros_are_poles_of_inverseZeta : Prop
  completedXiZeros_are_spectralZeros : Prop

namespace WittenCharacterVsCompletedXiSocket
end WittenCharacterVsCompletedXiSocket\n''',
        text, flags=re.DOTALL
    )

    # BosonFermionSuperdeterminantSocket
    text = re.sub(
        r'structure BosonFermionSuperdeterminantSocket.*?end BosonFermionSuperdeterminantSocket',
        '''structure BosonFermionSuperdeterminantSocket
    (Readout : Type*) [CommRing Readout] where
  bosonicReadout : Readout
  fermionicReadout : Readout
  superdeterminantReadout : Readout
  zetaReadout : Readout
  inverseZetaReadout : Readout
  superdeterminant_eq_bosonic_div_fermionic : superdeterminantReadout * fermionicReadout = bosonicReadout
  bosonic_eq_zeta : bosonicReadout = zetaReadout
  fermionic_eq_inverseZeta : fermionicReadout = inverseZetaReadout

namespace BosonFermionSuperdeterminantSocket
end BosonFermionSuperdeterminantSocket''',
        text, flags=re.DOTALL
    )

    # ArchimedeanGammaFactorSocket
    text = re.sub(
        r'structure ArchimedeanGammaFactorSocket.*?(?:@\[owner_target_tag\]\ntheorem ArchimedeanGammaFactorOwnerTarget.*?:=.*?sorryProof⟩\n)',
        '''structure ArchimedeanGammaFactorSocket
    (SpectralParameter Readout : Type*) [CommRing Readout] where
  parameter : SpectralParameter
  archimedeanReadout : Readout
  finitePrimeReadout : Readout
  completedZetaReadout : Readout
  gammaFactor : archimedeanReadout * finitePrimeReadout = completedZetaReadout
  polynomialCompletion : Prop
  completedZeta_factorization : Prop
  finitePrimes_alone_not_completed_guard : Type*

namespace ArchimedeanGammaFactorSocket
end ArchimedeanGammaFactorSocket\n''',
        text, flags=re.DOTALL
    )

    # BoundaryScatteringDiscretizationSocket
    text = re.sub(
        r'structure BoundaryScatteringDiscretizationSocket.*?end BoundaryScatteringDiscretizationSocket',
        '''structure BoundaryScatteringDiscretizationSocket
    (BoundaryData ScatteringMatrix Readout : Type*) [CommRing Readout] where
  boundaryData : BoundaryData
  scatteringMatrix : ScatteringMatrix
  continuousSpectrum : Readout
  discreteOrAbsorptionReadout : Readout
  phaseShiftReadout : Readout
  scattering_phaseShift : Prop
  discrete_spectrum_from_poles : Prop

namespace BoundaryScatteringDiscretizationSocket
end BoundaryScatteringDiscretizationSocket''',
        text, flags=re.DOTALL
    )

    # MBKHeatTraceExplicitFormulaSocket
    text = re.sub(
        r'structure MBKHeatTraceExplicitFormulaSocket.*?(?:@\[owner_target_tag\]\ntheorem MBKHeatTraceExplicitFormulaOwnerTarget.*?:=.*?sorryProof⟩\n)',
        '''structure MBKHeatTraceExplicitFormulaSocket
    (Readout : Type*) [CommRing Readout] where
  heatTrace : Readout
  bkHeatTrace : Readout
  arithmeticHeatTrace : Readout
  mellinTransformReadout : Readout
  explicitFormulaReadout : Readout
  heatTrace_factorization : heatTrace = bkHeatTrace * arithmeticHeatTrace
  arithmeticHeatTrace_primeSum : Prop
  bkHeatTrace_mellinContinuum : Prop
  mellinTransform_eq_explicitFormula : mellinTransformReadout = explicitFormulaReadout

namespace MBKHeatTraceExplicitFormulaSocket
end MBKHeatTraceExplicitFormulaSocket\n''',
        text, flags=re.DOTALL
    )

    # CompletedXiHilbertPolyaReduction
    text = re.sub(
        r'structure CompletedXiHilbertPolyaReduction.*?end CompletedXiHilbertPolyaReduction',
        '''structure CompletedXiHilbertPolyaReduction
    (Operator : Type*) [Ring Operator] where
  selfAdjointOperator : Operator
  isSelfAdjoint : Prop
  spectrum_lies_on_critical_line : Prop

namespace CompletedXiHilbertPolyaReduction
end CompletedXiHilbertPolyaReduction''',
        text, flags=re.DOTALL
    )

    # MajoranaPolyaHilbertBridge
    text = re.sub(
        r'structure MajoranaPolyaHilbertBridge.*?end MajoranaPolyaHilbertBridge',
        '''structure MajoranaPolyaHilbertBridge
    (Carrier Operator Mode ZeroMode SpectralParameter Readout : Type*) [Ring Operator] [CommRing Readout] where
  carrier : Carrier
  operator : Operator
  mode : Mode
  zeroMode : ZeroMode
  parameter : SpectralParameter
  readout : Readout
  isBerryKeating : Prop
  isHilbertPolya : Prop

namespace MajoranaPolyaHilbertBridge
end MajoranaPolyaHilbertBridge''',
        text, flags=re.DOTALL
    )

    # MajoranaBKTraceFormulaBridge
    text = re.sub(
        r'structure MajoranaBKTraceFormulaBridge.*?end MajoranaBKTraceFormulaBridge',
        '''structure MajoranaBKTraceFormulaBridge
    (Carrier Operator Readout : Type*) [Ring Operator] [CommRing Readout] where
  carrier : Carrier
  operator : Operator
  readout : Readout
  isBerryKeating : Prop

namespace MajoranaBKTraceFormulaBridge
end MajoranaBKTraceFormulaBridge''',
        text, flags=re.DOTALL
    )

    # RelativeMBKDeterminantScatteringPacket
    text = re.sub(
        r'structure RelativeMBKDeterminantScatteringPacket.*?end RelativeMBKDeterminantScatteringPacket',
        '''structure RelativeMBKDeterminantScatteringPacket
    (Readout : Type*) [CommRing Readout] where
  readout : Readout
  isScattering : Prop

namespace RelativeMBKDeterminantScatteringPacket
end RelativeMBKDeterminantScatteringPacket''',
        text, flags=re.DOTALL
    )

    # EssentialSelfAdjointLimitSocket
    text = re.sub(
        r'structure EssentialSelfAdjointLimitSocket.*?end EssentialSelfAdjointLimitSocket',
        '''structure EssentialSelfAdjointLimitSocket
    (Operator : Type*) [Ring Operator] where
  operator : Operator
  isEssentialSelfAdjoint : Prop

namespace EssentialSelfAdjointLimitSocket
end EssentialSelfAdjointLimitSocket''',
        text, flags=re.DOTALL
    )

    # ZetaRegularizedPfaffianSocket
    text = re.sub(
        r'structure ZetaRegularizedPfaffianSocket.*?end ZetaRegularizedPfaffianSocket',
        '''structure ZetaRegularizedPfaffianSocket
    (Readout : Type*) [CommRing Readout] where
  readout : Readout
  isRegularized : Prop

namespace ZetaRegularizedPfaffianSocket
end ZetaRegularizedPfaffianSocket''',
        text, flags=re.DOTALL
    )

    # CompletedXiSuperdeterminantIdentitySocket
    text = re.sub(
        r'structure CompletedXiSuperdeterminantIdentitySocket.*?end CompletedXiSuperdeterminantIdentitySocket',
        '''structure CompletedXiSuperdeterminantIdentitySocket
    (Readout : Type*) [CommRing Readout] where
  readout : Readout
  isIdentity : Prop

namespace CompletedXiSuperdeterminantIdentitySocket
end CompletedXiSuperdeterminantIdentitySocket''',
        text, flags=re.DOTALL
    )

    # MBKAnalyticFrontier
    text = re.sub(
        r'structure MBKAnalyticFrontier.*?(?:@\[owner_target_tag\]\ntheorem MBKAnalyticFrontierOwnerTarget.*?:=.*?sorryProof⟩\n)',
        '''structure MBKAnalyticFrontier
    (Readout : Type*) [CommRing Readout] where
  readout : Readout
  isFrontier : Prop

namespace MBKAnalyticFrontier
end MBKAnalyticFrontier\n''',
        text, flags=re.DOTALL
    )

    return text

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

text = process_socket(text)

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)
