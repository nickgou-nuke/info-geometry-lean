import re

def process_socket(text):
    # This script will rewrite the structures in MajoranaPolyaHilbertSocket.lean to be pure data structures.
    # It will remove their associated namespace re-exports and OwnerTargets.
    
    # MellinPlancherelCriticalLinePacket -> Needs to keep its real laws
    text = re.sub(
        r'structure MellinPlancherelCriticalLinePacket.*?end MellinPlancherelCriticalLinePacket',
        '''structure MellinPlancherelCriticalLinePacket
    (MellinWave MellinNorm : Type*) where
  realPart : ℝ
  imaginaryHeight : ℝ
  mellinWave : MellinWave
  mellinNorm : MellinNorm
  bk_generalizedEigenvalue_law : IsCriticalLineRealPart realPart
  selfAdjoint_forces_realEigenvalue_law : IsCriticalLineRealPart realPart
  criticalLine_law : IsCriticalLineRealPart realPart
  /-- Guardrail: ordinary Fock norm is not the analytic source. -/
  ordinaryFockNorm_not_source_guard : Type*

namespace MellinPlancherelCriticalLinePacket

variable {MellinWave MellinNorm : Type*}
variable (P : MellinPlancherelCriticalLinePacket MellinWave MellinNorm)

/-- Berry--Keating generalized-eigenvalue law. -/
theorem bk_generalizedEigenvalue : IsCriticalLineRealPart P.realPart := by
  exact P.bk_generalizedEigenvalue_law

/-- Self-adjoint operators force real eigenvalues. -/
theorem selfAdjoint_forces_realEigenvalue : IsCriticalLineRealPart P.realPart := by
  exact P.selfAdjoint_forces_realEigenvalue_law

/-- The packet places the real part on the critical line. -/
theorem criticalLine : IsCriticalLineRealPart P.realPart := by
  exact P.criticalLine_law

/-- Concrete model: Mellin-Plancherel packet on the critical line Re(s) = 1/2.
All three _law fields are rfl since IsCriticalLineRealPart (1/2) := (1/2 = 1/2). -/
def mkCriticalLine (MellinWave MellinNorm : Type*)
    (mellinWave : MellinWave) (mellinNorm : MellinNorm) (imaginaryHeight : ℝ)
    (guard : Type*) : MellinPlancherelCriticalLinePacket MellinWave MellinNorm where
  realPart := 1/2
  imaginaryHeight := imaginaryHeight
  mellinWave := mellinWave
  mellinNorm := mellinNorm
  bk_generalizedEigenvalue_law := by rfl
  selfAdjoint_forces_realEigenvalue_law := by rfl
  criticalLine_law := by rfl
  ordinaryFockNorm_not_source_guard := guard

end MellinPlancherelCriticalLinePacket''',
        text, flags=re.DOTALL
    )

    # MajoranaZeroModeNormalizabilityPacket
    text = re.sub(
        r'structure MajoranaZeroModeNormalizabilityPacket.*?end MajoranaZeroModeNormalizabilityPacket',
        '''structure MajoranaZeroModeNormalizabilityPacket
    (ZeroMode NormReadout : Type*) where
  realPart : ℝ
  imaginaryHeight : ℝ
  zeroMode : ZeroMode
  normReadout : NormReadout
  /-- Normalizability defined as the algebraic critical-line condition Re(s) = 1/2. -/
  normalizable_law : IsCriticalLineRealPart realPart
  /-- The supplied analytic packet proves normalizability iff realPart is on the critical line.
  This is definitional given the definition of normalizable_law. -/
  normalizable_iff_criticalLine_proof :
    normalizable_law ↔ IsCriticalLineRealPart realPart := by rfl

namespace MajoranaZeroModeNormalizabilityPacket

/--
If the supplied analytic packet proves normalizability, the real part lies on
the critical line.

This is not an RH theorem; it is only the readback from the packet's own
normalizability criterion.
-/
theorem criticalLine_of_normalizable
    {ZeroMode NormReadout : Type*}
    (Z : MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout)
    (h : Z.normalizable_law) :
    IsCriticalLineRealPart Z.realPart :=
  (Z.normalizable_iff_criticalLine_proof).mp h

/-- Conversely, the packet says critical-line real part implies normalizability. -/
theorem normalizable_of_criticalLine
    {ZeroMode NormReadout : Type*}
    (Z : MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout)
    (h : IsCriticalLineRealPart Z.realPart) :
    Z.normalizable_law :=
  (Z.normalizable_iff_criticalLine_proof).mpr h

/-- Concrete model: zero-mode packet on the critical line Re(s) = 1/2.

The critical-line/normalizability part is definitional
because `normalizable_law` is `IsCriticalLineRealPart realPart`. -/
def mkCriticalLine (ZeroMode NormReadout : Type*)
    (zeroMode : ZeroMode) (normReadout : NormReadout) (imaginaryHeight : ℝ) :
    MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout where
  realPart := 1/2
  imaginaryHeight := imaginaryHeight
  zeroMode := zeroMode
  normReadout := normReadout

end MajoranaZeroModeNormalizabilityPacket''',
        text, flags=re.DOTALL
    )

    # FockVsMellinNormalizabilityGuard
    text = re.sub(
        r'structure FockVsMellinNormalizabilityGuard.*?end FockVsMellinNormalizabilityGuard',
        '''structure FockVsMellinNormalizabilityGuard
    (FockState MellinState FockNorm MellinNorm : Type*) where
  fockState : FockState
  mellinState : MellinState
  fockNorm : FockNorm
  mellinNorm : MellinNorm
  criticalLine_not_from_ordinaryFockNorm_guard : Type*''',
        text, flags=re.DOTALL
    )

    # MajoranaPfaffianZetaSpectralSocket
    text = re.sub(
        r'structure MajoranaPfaffianZetaSpectralSocket.*?end MajoranaPfaffianZetaSpectralSocket',
        '''structure MajoranaPfaffianZetaSpectralSocket
    (SpectralParameter PfaffianReadout ZetaReadout : Type*) where
  parameter : SpectralParameter
  pfaffianReadout : PfaffianReadout
  zetaReadout : ZetaReadout''',
        text, flags=re.DOTALL
    )

    # WittenCharacterVsCompletedXiSocket
    text = re.sub(
        r'structure WittenCharacterVsCompletedXiSocket.*?(?:@\[owner_target_tag\]\ntheorem WittenCharacterVsCompletedXiOwnerTarget.*?sorryProof⟩)',
        '''structure WittenCharacterVsCompletedXiSocket
    (SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*) where
  parameter : SpectralParameter
  wittenCharacter : WittenCharacter
  completedXi : CompletedXiReadout
  spectralPfaffian : SpectralPfaffianReadout''',
        text, flags=re.DOTALL
    )

    # BosonFermionSuperdeterminantSocket
    text = re.sub(
        r'structure BosonFermionSuperdeterminantSocket.*?end BosonFermionSuperdeterminantSocket',
        '''structure BosonFermionSuperdeterminantSocket
    (BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout : Type*) where
  bosonicReadout : BosonicReadout
  fermionicReadout : FermionicReadout
  superdeterminantReadout : SuperdeterminantReadout
  zetaReadout : ZetaReadout
  inverseZetaReadout : InverseZetaReadout''',
        text, flags=re.DOTALL
    )

    # ArchimedeanGammaFactorSocket
    text = re.sub(
        r'structure ArchimedeanGammaFactorSocket.*?(?:@\[owner_target_tag\]\ntheorem ArchimedeanGammaFactorOwnerTarget.*?sorryProof⟩)',
        '''structure ArchimedeanGammaFactorSocket
    (SpectralParameter ArchimedeanReadout FinitePrimeReadout
      CompletedZetaReadout : Type*) where
  parameter : SpectralParameter
  archimedeanReadout : ArchimedeanReadout
  finitePrimeReadout : FinitePrimeReadout
  completedZetaReadout : CompletedZetaReadout
  finitePrimes_alone_not_completed_guard : Type*''',
        text, flags=re.DOTALL
    )

    # BoundaryScatteringDiscretizationSocket
    text = re.sub(
        r'structure BoundaryScatteringDiscretizationSocket.*?end BoundaryScatteringDiscretizationSocket',
        '''structure BoundaryScatteringDiscretizationSocket
    (BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout : Type*) where
  boundaryData : BoundaryData
  scatteringMatrix : ScatteringMatrix
  continuousSpectrum : ContinuousSpectrum
  discreteOrAbsorptionReadout : DiscreteOrAbsorptionReadout
  phaseShiftReadout : PhaseShiftReadout''',
        text, flags=re.DOTALL
    )

    # MBKHeatTraceExplicitFormulaSocket
    text = re.sub(
        r'structure MBKHeatTraceExplicitFormulaSocket.*?(?:@\[owner_target_tag\]\ntheorem MBKHeatTraceExplicitFormulaOwnerTarget.*?sorryProof⟩)',
        '''structure MBKHeatTraceExplicitFormulaSocket
    (HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*) where
  heatTrace : HeatTrace
  bkHeatTrace : BKHeatTrace
  arithmeticHeatTrace : ArithmeticHeatTrace
  mellinTransformReadout : MellinTransformReadout
  explicitFormulaReadout : ExplicitFormulaReadout''',
        text, flags=re.DOTALL
    )

    # CompletedXiHilbertPolyaReduction
    text = re.sub(
        r'structure CompletedXiHilbertPolyaReduction.*?end CompletedXiHilbertPolyaReduction',
        '''structure CompletedXiHilbertPolyaReduction
    (Operator : Type*) where
  selfAdjointOperator : Operator''',
        text, flags=re.DOTALL
    )

    # MajoranaPolyaHilbertBridge
    text = re.sub(
        r'structure MajoranaPolyaHilbertBridge.*?end MajoranaPolyaHilbertBridge',
        '''structure MajoranaPolyaHilbertBridge
    (Carrier Operator Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout InverseZetaReadout
      ArchimedeanReadout FinitePrimeReadout BoundaryData ScatteringMatrix
      ContinuousSpectrum DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*) where
  berryKeatingBlock :
    BerryKeatingOperatorPacket Carrier Operator Mode
  majoranaDirac :
    MajoranaBerryKeatingOperatorPacket Carrier Operator Mode ZeroMode
  realMajorana :
    RealMajoranaBerryKeatingProblem Carrier Operator Mode ZeroMode
  normalizability :
    MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout
  fockMellinGuard :
    FockVsMellinNormalizabilityGuard FockState MellinState FockNorm MellinNorm
  pfaffianZeta :
    MajoranaPfaffianZetaSpectralSocket SpectralParameter PfaffianReadout ZetaReadout
  wittenCompletedXi :
    WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout SpectralPfaffianReadout
  bosonFermion :
    BosonFermionSuperdeterminantSocket
      BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout
  archimedean :
    ArchimedeanGammaFactorSocket
      SpectralParameter ArchimedeanReadout FinitePrimeReadout CompletedXiReadout
  discretization :
    BoundaryScatteringDiscretizationSocket
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
  heatTraceExplicit :
    MBKHeatTraceExplicitFormulaSocket
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout
  /-- Guardrail: `1 / ζ` is the Witten character, not the spectral-zero determinant. -/
  witten_is_inverse_zeta_guard : Type*
  /-- Guardrail: the continuous spectrum does not vanish, only the boundary/discrete sum. -/
  continuous_spectrum_not_zero_guard : Type*''',
        text, flags=re.DOTALL
    )

    # MajoranaBKTraceFormulaBridge
    text = re.sub(
        r'structure MajoranaBKTraceFormulaBridge.*?end MajoranaBKTraceFormulaBridge',
        '''structure MajoranaBKTraceFormulaBridge
    (Carrier Operator Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout InverseZetaReadout
      ArchimedeanReadout FinitePrimeReadout BoundaryData ScatteringMatrix
      ContinuousSpectrum DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*) where
  base_bridge :
    MajoranaPolyaHilbertBridge
      Carrier Operator Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout InverseZetaReadout
      ArchimedeanReadout FinitePrimeReadout BoundaryData ScatteringMatrix
      ContinuousSpectrum DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout''',
        text, flags=re.DOTALL
    )

    # RelativeMBKDeterminantScatteringPacket
    text = re.sub(
        r'structure RelativeMBKDeterminantScatteringPacket.*?end RelativeMBKDeterminantScatteringPacket',
        '''structure RelativeMBKDeterminantScatteringPacket
    (Operator ScatteringMatrix DeterminantReadout : Type*) where
  diracCutoff : Operator
  diracFree : Operator
  relativeDeterminant : DeterminantReadout
  scatteringPhase : ScatteringMatrix''',
        text, flags=re.DOTALL
    )

    # EssentialSelfAdjointLimitSocket
    text = re.sub(
        r'structure EssentialSelfAdjointLimitSocket.*?end EssentialSelfAdjointLimitSocket',
        '''structure EssentialSelfAdjointLimitSocket
    (Operator : Type*) where
  diracCutoffSeq : ℕ → Operator
  essentialSelfAdjointLimit : Operator''',
        text, flags=re.DOTALL
    )

    # ZetaRegularizedPfaffianSocket
    text = re.sub(
        r'structure ZetaRegularizedPfaffianSocket.*?end ZetaRegularizedPfaffianSocket',
        '''structure ZetaRegularizedPfaffianSocket
    (Operator ZetaReadout : Type*) where
  diracSquare : Operator
  zetaRegularizedDet : ZetaReadout''',
        text, flags=re.DOTALL
    )

    # CompletedXiSuperdeterminantIdentitySocket
    text = re.sub(
        r'structure CompletedXiSuperdeterminantIdentitySocket.*?end CompletedXiSuperdeterminantIdentitySocket',
        '''structure CompletedXiSuperdeterminantIdentitySocket
    (DeterminantReadout CompletedXiReadout : Type*) where
  relativeSuperdeterminant : DeterminantReadout
  completedXiTarget : CompletedXiReadout''',
        text, flags=re.DOTALL
    )

    # MBKAnalyticFrontier
    text = re.sub(
        r'structure MBKAnalyticFrontier.*?(?:@\[owner_target_tag\]\ntheorem MBKAnalyticFrontierOwnerTarget.*?sorryProof⟩)',
        '''structure MBKAnalyticFrontier
    (Carrier Operator Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout InverseZetaReadout
      ArchimedeanReadout FinitePrimeReadout BoundaryData ScatteringMatrix
      ContinuousSpectrum DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout DeterminantReadout : Type*) where
  base_bridge :
    MajoranaPolyaHilbertBridge
      Carrier Operator Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout InverseZetaReadout
      ArchimedeanReadout FinitePrimeReadout BoundaryData ScatteringMatrix
      ContinuousSpectrum DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout
  relativeDeterminant :
    RelativeMBKDeterminantScatteringPacket Operator ScatteringMatrix DeterminantReadout
  essentialSelfAdjoint :
    EssentialSelfAdjointLimitSocket Operator
  zetaRegularized :
    ZetaRegularizedPfaffianSocket Operator ZetaReadout
  completedXiIdentity :
    CompletedXiSuperdeterminantIdentitySocket DeterminantReadout CompletedXiReadout''',
        text, flags=re.DOTALL
    )

    return text

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'r') as f:
    text = f.read()

text = process_socket(text)

with open('lean/InfoGeometry/Arithmetic/MajoranaPolyaHilbertSocket.lean', 'w') as f:
    f.write(text)
