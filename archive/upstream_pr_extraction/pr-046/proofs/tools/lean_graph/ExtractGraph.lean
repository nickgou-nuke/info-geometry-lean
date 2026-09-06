import proofs.FureyZornFermionBridge
import proofs.KleinFundamentalGroup
import proofs.KleinEquivariantHamiltonian
import proofs.ZornColorLieRepresentation
import proofs.ZornChiralColorActions
import proofs.ZornColorSectorWeights
import proofs.ZornColorChargeConjugation
import proofs.ZornChiralColorRepresentations
import proofs.MirrorNucleiIsospinGNS
import proofs.TrialityBridge
import proofs.Clifford55
import proofs.ConformalCGA
import proofs.ArtinCentralizerMonodromy
import proofs.Q8NuclearChirality
import Lean
import proofs.ChiralCausalCone
import proofs.TwoSheetChiralTKKDerivations
import proofs.ChiralTensorRecoupling
import proofs.TLChain
import proofs.JonesBraidB3
import proofs.YangBaxterQSwap
import proofs.YangBaxterZornBridge
import proofs.B3PresentedGroup
import proofs.YangBaxterQuotientDescent
import proofs.BraidIdealDescent
import proofs.ChiralTensorMatrixBridge
import proofs.ChiralTLDescent
import proofs.ChiralB3PresentedBridge
import proofs.AlgebraicCuntzQuotient
import proofs.CStarCuntzTensorQuotient
import proofs.ComplexStarCuntzRedesign
import proofs.SupergradedCuntzBdG
import proofs.HestenesCuntzSpacetimeAlgebra
import proofs.HestenesCuntzPhaseSpace
import proofs.BogoliubovWeylChemicalPotential
import proofs.RelativeModularStateDikin
import proofs.RescaledPhaseVolumeCanonical
import proofs.GaugeUHFLift
import proofs.WeylGaugeColimitWeld
import proofs.WeylColimitCanonicalLimit
import proofs.BogoliubovSU3ParafermionWeld
import proofs.BogoliubovSU3ParafermionProofChain
import proofs.WeylSU3ColorSymmetry
import proofs.GellMannParafermionSolder
import proofs.ParafermionIdentityRealization
import proofs.CantorBoundaryCuntzFamily
import proofs.WeylSolderedParafermionSymmetry
import proofs.CuntzBoundarySolderRealization
import proofs.GellMannParafermionRealizationRoutesSynthesis
import proofs.ColorParafermionCuntzBusSpine
import proofs.BogoliubovBraidGraphWeld
-- Clifford / Zorn / Souriau / Twistor tower
import proofs.SplitCliffordAlgebras
import proofs.AtomicCliffordKAN
import proofs.BiquaternionCliffordIso
import proofs.BiquaternionExpClosure
import InfoGeometry.Canonical.BiquaternionKANnilpotent
import InfoGeometry.Canonical.BiquaternionLaplaceTripotent
import proofs.TrifactorGeometry
import proofs.TripotentCliffordColimit
import proofs.SpinNetworkTwistorQuantization
import proofs.RindlerWignerBogoliubovEquivalence
import proofs.GraphLaplacianSpanningTree
import proofs.TripotentTwistorDeRhamSynthesis
import proofs.ZornParavectorNullspace
import proofs.ZornScalingFlow
import proofs.ZornBraidScalingCovariance
import InfoGeometry.Canonical.CanonicalZornProjectiveTKKBridge
import InfoGeometry.Canonical.IntegralZornII44Bridge
import InfoGeometry.Canonical.CanonicalZornFiveGradedClosure
import InfoGeometry.Canonical.CanonicalZornCompositionTriality
import InfoGeometry.Canonical.CanonicalZornCliffordRepresentation
import InfoGeometry.Canonical.CanonicalZornCliffordIsomorphism
import proofs.ZornCliffordBasisMonomials
import proofs.ZornCliffordIsomorphismClosure
import proofs.ZornCliffordPBWFinrank
import proofs.ZornCliffordTraceOrthogonality
import proofs.ZornCliffordBijectivity
import proofs.ZornCliffordParityAPI
import proofs.ZornChiralLightcone
import proofs.ZornLightconeCAR
import proofs.ZornLightconeChannelOperator
import proofs.ZornThreeChannelCAR
import proofs.ZornChannelKernelMultiplication
import proofs.ZornColorLieAction
import proofs.ZornQuasiHopfCocycle
import proofs.ZornGromovWitten
import proofs.ZornParabolicHolography
import proofs.ZornMajoranaBraiding
import proofs.TopologicalQuantumGates
import proofs.ZornRindlerHorizon
import proofs.ZornRindlerKMSBridge
import InfoGeometry.Canonical.CanonicalZornRealSpin44
import InfoGeometry.Canonical.CanonicalZornTrialitySpinEquivariance
import InfoGeometry.Canonical.CanonicalZornOuterTrialityGroup
import InfoGeometry.Canonical.CanonicalZornSpinRelatedFiber
import InfoGeometry.Canonical.CanonicalZornSpinChirality
import InfoGeometry.Canonical.CanonicalZornSpinVectorAction
import InfoGeometry.Canonical.CanonicalZornRealSpinTrialityClosure
import InfoGeometry.Canonical.CanonicalZornRealComplexSpinBaseChange
import InfoGeometry.Canonical.CanonicalZornIntegralSpinTrialityClosure
import InfoGeometry.Canonical.CanonicalZornIntegralSpinSubgroup
import InfoGeometry.Canonical.CanonicalZornIntegralSpinRepresentation
import InfoGeometry.Canonical.CanonicalZornIntegralTrialityEquivariance
import InfoGeometry.Canonical.IntegralZornCompositionAlgebra
import InfoGeometry.Canonical.IntegralZornAlternativeAlgebra
import InfoGeometry.Canonical.IntegralZornBilinearComposition
import InfoGeometry.Canonical.CanonicalZornUnifiedClosure
import proofs.ZornKleinGlideBridge
import proofs.SouriauMoebiusCoupling
import proofs.SouriauBiquaternionGaussian
import proofs.SouriauHestenesKrein
import proofs.ExceptionalBraidTopology
import proofs.ExceptionalPointCollapse
import proofs.MobiusWittenIndex
import proofs.OctonionMatrixEncodings
import proofs.SplitOctonionBraidSU3
import proofs.SplitOctonionTomitaTakesaki
import proofs.ZornOPParavector
import proofs.SplitOctonionChiralClosure
import proofs.SplitOctonionMinkowski
import proofs.Clifford55AnomalyOSP
import proofs.MinkowskiBiquaternion
import proofs.PolynomialSymmetryOperators
import proofs.BraidCliffordIntegration
import proofs.ColorCARStandardModel
import proofs.FureyCharges
import proofs.KreinMoorePenrose
import proofs.GoutevTonevPrinciple
import proofs.DikinGoutevTonevBridge
import proofs.AffineDynkinGoutevTonev
import proofs.GellMannCartan
import proofs.GellMannSU3
import proofs.WeakIsospinSU2
import proofs.FierzIdentities
import proofs.SpectralSquashCayleyDKT
import proofs.QSuperCuntzRegularization
import proofs.QRootOfUnityTruncation
import proofs.QuadraticConfiguration3
import proofs.NonIsoConf3OrlikSolomon
import proofs.NonIsoConf3DeRhamCooperad
import proofs.NonIsoConf3RankDecision
import proofs.LogCFTGeneratingPotential
import proofs.LogCFTPotentialBranchChoice
import proofs.NonIsoConf3LogCFTLiteratureBridge
import proofs.LightConeConf3DeRhamCooperad
import proofs.InfiniteLightConeConfColimit
import proofs.BraidedCocycleWilsonEntropy
import proofs.QuadricConf3BraidingCooperadBridge
import proofs.PenroseQuadricTopologySynthesis
import proofs.LightConeTripotentMatrixBridge
import proofs.CooperadEnvironmentalRank32
import proofs.ChemicalPotentialTKKGradeZero
import proofs.ChemicalPotentialMetricBridge
import proofs.ThermodynamicTKKBridge
import proofs.ChemicalPotentialDeRhamG0Bridge
import proofs.ModularRadonNikodymJacobianBridge
import proofs.ModularTimeDeRhamBridge
import proofs.ModularParabolicTimeBridge
import proofs.EntropicChiralDeRhamDictionary
import proofs.EntropicChiralDeRhamFormalization
import proofs.PrimonCuntzTower
import proofs.CuntzP6MBoundary
import proofs.WallpaperHolographicSelectionRules
import proofs.KleinBrillouinRamanDynamics
import proofs.TrappedHarmonicModes
import proofs.NuclearSpectroscopyEnergyLevels
import proofs.NuclearWallpaperSpectraClassification
import proofs.ClebschGordanPenroseNonequilibriumSpinGraph
import proofs.SpectroscopicCapstone
import proofs.FinalSpectroscopicSynthesisAudit
import proofs.SmithHatIsingDuality
import proofs.BashoreSpinNetworkQubit
import proofs.BashoreLQGReportExtraction
import proofs.TrainsumQuanticsTensorTrainsDigest
import proofs.MellinWaveletScaleShiftDigest
import proofs.EastSU2EquivariantSpinNetworkCircuits
import proofs.QuaternionQuanticsBackendDigest
import proofs.PenroseChiralNuclearTrainsumToy
import proofs.BoltzmannLnQTensorFlowToy
import proofs.Mirror31PSLnQFlowToy
import proofs.GaugeLnQTensorNetworkToy
import proofs.XanaduSpinNetworkCodeDigest
import proofs.O55GradedGeneratorBasis
import proofs.O55CartanPhononReduction
import proofs.WallpaperO55FrozenSelectionBridge
import proofs.TorusKleinO55Bridge
import proofs.TwistedTorusVacuumMachine
import proofs.DoubledChargeLatticeKasparovKreinBridge
import proofs.KasparovKreinKleinO55Kernel
import proofs.JackiwRebbiCantorEdgeStates
import proofs.StimulatedScatteringAmplituhedron
import InfoGeometry.External.Auto.BuresInformationGeodesicFlow
import proofs.TopologicalAndreevPump
import proofs.PhaseConjugateVacuumMirror
import proofs.MetamaterialQuasicrystalBloch
import proofs.ConformalScaleRecurrence
import proofs.CosmologicalSynthesis
import proofs.SuperconductingHolographicResonator
import proofs.TopologicalMetasurfaceSupercurrent
import proofs.CuntzP6MWallpaperBoundary
import proofs.ThermalBoostLorentzSuperalgebra
import proofs.DiracCuntzCrystalDispersion
import proofs.KTheoryChernConfinementSignature
import proofs.NonAbelianBrillouinKleinBottle
import proofs.ThermodynamicLorentzBoost
import proofs.ThermodynamicNetworkSpine
import proofs.BuresFisherAndreevGeodesicFlow
import proofs.NonIsoConf3QuadricD4EPolynomial
import proofs.GrothendieckGromovWittenYangBaxter
import proofs.PenroseSpinTilingConfig
import proofs.PenroseSpinIncidenceTessellation
import proofs.KleinErlangenGrothendieckBridge
import proofs.MotivicHolographyGroebnerLFunction
import proofs.AmariChentsovFierzTorsion
import proofs.TKKJordanPairData
import proofs.GNSQuotientFinite
import proofs.FiniteMatrixElementDuality
import proofs.KreinCuntzShadow
import proofs.EuclideanNilpotentObstruction
import proofs.ZornChiralBridge
import proofs.ArithmeticHamiltonianZeta
import proofs.PrimonSuperThermodynamics
import proofs.RiemannHypothesis
import proofs.MajoranaPrimonSpectralBridge
import proofs.PrimonHilbertPolyaSeparation
import proofs.IJIRTRiemannDigest
import proofs.MisraPrimeEntropyDigest
import proofs.PrimonBosonFermionDuality
import proofs.PrimonCoarseGraining
import proofs.PrimonCoarseGrainedHilbertPolyaPotential
import proofs.JaynesLDDPGNSColimit
import proofs.JaynesLeanColimitBridge
import proofs.ContinuumAsColimitCounting
import proofs.CurryHowardLambekColimit
import InfoGeometry.Canonical.ProjectiveAffineConformalClosure55
import proofs.TwistorParafermionBoundary
import proofs.CP3CantorGeometricObstruction
import proofs.HillWheelerProjection
import proofs.HillWheelerUniversalProjection
import proofs.SU3LoopBraidCuntzBoundary
import proofs.SU3LoopBraidDuality
import proofs.HolographicGaugeSymmetryUniqueness
import proofs.GravitationalQuantumBraidDuality
import proofs.SUNQuantumBraidDuality
import proofs.TopologicalColorCrystalFormal
import proofs.SolovievQPNMChiralCuntz
import proofs.UnorientedS3KleinTQFT
import proofs.SpectralCPTKleinBottle

/-!
# ExtractGraph — export Environment dependency graph as JSON

Run: `lake env lean tools/ExtractGraph.lean`

Output: `proof_graph.json` with one JSON object per line.

Uses `run_cmd` for Environment access + `IO.FS.writeFile`.
-/


open Lean

def ourPrefixes : List String :=
  ["ChiralCausalCone", "TwoSheetChiralClosure", "TwoSheetChiralTKKDerivations",
   "ChiralTensor", "TLChain",
   "JonesBraid", "YangBaxter", "OctonionMatrixEncodings",
   "SplitOctonionBraidSU3", "SplitOctonionPeirce",
   "ZornOPParavector", "SplitOctonionChiralClosure", "ZornCore",
   "ZornTrialityTKKBridge", "ProjectiveAffineConformalClosure55",
   "GrandUnifiedTKK", "ZornScalingFlow",
   "ZornBraidScalingCovariance", "CanonicalZornProjectiveTKKBridge",
   "IntegralZornII44Bridge", "CanonicalZornFiveGradedClosure",
   "CanonicalZornCompositionTriality",
   "CanonicalZornCliffordRepresentation",
   "CanonicalZornCliffordIsomorphism",
   "ZornCliffordBasisMonomials",
   "ZornCliffordIsomorphismClosure",
   "ZornCliffordPBWFinrank",
   "ZornCliffordTraceOrthogonality",
   "ZornCliffordBijectivity",
   "ZornCliffordParityAPI",
   "ZornChiralLightcone",
   "ZornLightconeCAR",
   "ZornLightconeChannelOperator",
   "ZornThreeChannelCAR",
   "ZornChannelKernelMultiplication",
   "ZornColorLieAction",
   "ZornQuasiHopfCocycle",
   "ZornGromovWitten",
   "ZornParabolicHolography",
   "ZornMajoranaBraiding",
   "TopologicalQuantumGates",
   "ZornRindlerHorizon",
   "ZornRindlerKMSBridge",
   "CanonicalZornRealSpin44",
   "CanonicalZornTrialitySpinEquivariance",
   "CanonicalZornOuterTrialityGroup",
   "CanonicalZornSpinRelatedFiber",
   "CanonicalZornSpinChirality",
   "CanonicalZornSpinVectorAction",
   "CanonicalZornRealSpinTrialityClosure",
   "CanonicalZornRealComplexSpinBaseChange",
   "CanonicalZornIntegralSpinTrialityClosure",
   "CanonicalZornIntegralSpinSubgroup",
   "CanonicalZornIntegralSpinRepresentation",
   "CanonicalZornIntegralTrialityEquivariance",
   "IntegralZornCompositionAlgebra",
   "IntegralZornAlternativeAlgebra",
   "IntegralZornBilinearComposition",
   "CanonicalZornUnifiedClosure",
   "TKKJordanPairData", "ZornKleinGlideBridge", "TitsBruhatBrillouinKlein",
   "B3Presented",
   "BraidIdeal", "IdealDescent", "BaxterAnchor", "B3Representation",
   "AlgebraicCuntzQuotient", "CStarCuntzTensorQuotient",
   "ComplexStarCuntzRedesign", "SupergradedCuntzBdG",
   "HestenesCuntzSpacetimeAlgebra", "HestenesCuntzPhaseSpace",
   "BogoliubovWeylChemicalPotential", "RelativeModularStateDikin",
   "RescaledPhaseVolumeCanonical", "GaugeUHFLift",
   "WeylGaugeColimitWeld", "WeylColimitCanonicalLimit",
   "BogoliubovSU3ParafermionWeld", "BogoliubovSU3ParafermionProofChain",
   "WeylSU3ColorSymmetry", "GellMannParafermionSolder",
   "ParafermionIdentityRealization", "CantorBoundaryCuntzFamily",
   "WeylSolderedParafermionSymmetry", "CuntzBoundarySolderRealization",
   "GellMannParafermionRealizationRoutesSynthesis",
   "BogoliubovBraidGraphWeld", "ColorCARStandardModel",
   "FureyCharges", "GellMannCartan", "GellMannSU3",
   "arithmetic", "finiteArithmetic", "finiteZeta", "boltzmann",
   "rh", "RHStatement", "HilbertPolyaShape", "hilbert_polya",
   "criticalDamping", "complexTemperature", "hagedornTemperature",
   "PrimonSuperThermo", "MajoranaPrimonSpectralBridge",
   "PrimonHilbertPolyaSeparation", "PrimonBosonFermionDuality",
   "PrimonCoarseGraining", "PrimonCoarseGrainedHilbertPolyaPotential",
   "JaynesLDDPGNSColimit", "ContinuumAsColimitCounting",
   "CurryHowardLambekColimit", "Clifford55AnomalyOSP",
   "ProjectiveAffineConformalClosure55", "TwistorParafermionBoundary",
   "CP3CantorGeometricObstruction", "HillWheelerProjection", "HillWheelerUniversalProjection",
   "SU3LoopBraidCuntzBoundary", "SU3LoopBraidDuality",
   "HolographicGaugeSymmetryUniqueness", "GravitationalQuantumBraidDuality",
   "SUNQuantumBraidDuality", "TopologicalColorCrystalFormal", "SolovievQPNMChiralCuntz",
   "SpectralCPTKleinBottle", "ZornColorLieRepresentation",
   "KleinAffineDeckGroup", "KleinUniversalAffineAction", "KleinFundamentalGroup",
   "KleinEquivariantHamiltonian",
   "ZornChiralColorActions", "ZornColorSectorWeights",
   "ZornColorChargeConjugation", "ZornChiralColorRepresentations"]

def isOurs (name : Name) : Bool :=
  ourPrefixes.any (fun p => name.toString.startsWith p)

def kindString (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .opaqueInfo _ => "opaque"
  | _ => "other"

def escapeJson (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def extractOne (name : Name) (ci : ConstantInfo) : String :=
  let deps := (ci.getUsedConstantsAsSet.toList.filter isOurs).map Name.toString
  let depStrs := deps.map (fun d => "\"" ++ escapeJson d ++ "\"")
  let depJson := "[" ++ (",".intercalate depStrs) ++ "]"
  let jname := escapeJson (name.toString)
  let dbHash := toString (hash ci.type)
  "{\"name\": \"" ++ jname ++
    "\", \"kind\": \"" ++ kindString ci ++
    "\", \"de_bruijn_hash\": \"" ++ dbHash ++
    "\", \"deps\": " ++ depJson ++ "}"

run_cmd do
  let env ← getEnv
  let ours := env.constants.toList.filter (fun (n, _) => isOurs n)
  let lines := ours.map (fun (n, ci) => extractOne n ci)
  let json := "[\n" ++ (",\n".intercalate lines) ++ "\n]\n"
  IO.FS.writeFile "proof_graph.json" json
  let count := ours.length
  logInfo s!"Wrote {count} declarations to proof_graph.json"

def main : IO Unit := pure ()
