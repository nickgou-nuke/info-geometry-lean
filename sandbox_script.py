import re

with open("agent_memory_recovery/MajoranaPolyaHilbertSocket.lean/2026-07-06_03-36-57_3937e0bb.lean", "r") as f:
    code = f.read()

# Add concrete instantiations at the end
instantiations = """
/-! ## 9. Concrete Instantiations -/

def concreteMellinPlancherelCriticalLinePacket : MellinPlancherelCriticalLinePacket Unit Unit := sorry
def concreteBerryKeatingOperatorPacket : BerryKeatingOperatorPacket Unit Unit Unit := sorry
def concreteMajoranaBerryKeatingOperatorPacket : MajoranaBerryKeatingOperatorPacket Unit Unit Unit Unit := sorry
def concreteRealMajoranaBerryKeatingProblem : RealMajoranaBerryKeatingProblem Unit Unit Unit Unit := sorry
def concreteFockVsMellinNormalizabilityGuard : FockVsMellinNormalizabilityGuard Unit Unit Unit Unit := sorry
def concreteMajoranaZeroModeNormalizabilityPacket : MajoranaZeroModeNormalizabilityPacket Unit Unit := sorry
def concreteMajoranaPfaffianZetaSpectralSocket : MajoranaPfaffianZetaSpectralSocket Unit Unit Unit := sorry
def concreteWittenCharacterVsCompletedXiSocket : WittenCharacterVsCompletedXiSocket Unit Unit Unit Unit := sorry
def concreteBosonFermionSuperdeterminantSocket : BosonFermionSuperdeterminantSocket Unit Unit Unit Unit Unit := sorry
def concreteArchimedeanGammaFactorSocket : ArchimedeanGammaFactorSocket Unit Unit Unit Unit := sorry
def concreteBoundaryScatteringDiscretizationSocket : BoundaryScatteringDiscretizationSocket Unit Unit Unit Unit Unit := sorry
def concreteMBKHeatTraceExplicitFormulaSocket : MBKHeatTraceExplicitFormulaSocket Unit Unit Unit Unit Unit := sorry
def concreteCompletedXiHilbertPolyaReduction : CompletedXiHilbertPolyaReduction Unit := sorry
def concreteMajoranaPolyaHilbertBridge : MajoranaPolyaHilbertBridge Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit := sorry
def concreteMajoranaBKTraceFormulaBridge : MajoranaBKTraceFormulaBridge Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit := sorry
def concreteRelativeMBKDeterminantScatteringPacket : RelativeMBKDeterminantScatteringPacket Unit Unit Unit := sorry
def concreteEssentialSelfAdjointLimitSocket : EssentialSelfAdjointLimitSocket Unit := sorry
def concreteZetaRegularizedPfaffianSocket : ZetaRegularizedPfaffianSocket Unit Unit := sorry
def concreteCompletedXiSuperdeterminantIdentitySocket : CompletedXiSuperdeterminantIdentitySocket Unit Unit := sorry
def concreteMBKAnalyticFrontier : MBKAnalyticFrontier Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit Unit := sorry
"""

# write to sandbox
with open("sandbox/MajoranaPolyaHilbertSocket.lean", "w") as f:
    f.write(code.replace("end InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket", instantiations + "\nend InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket"))

