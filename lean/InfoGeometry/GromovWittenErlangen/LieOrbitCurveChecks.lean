import InfoGeometry.GromovWittenErlangen.LieOrbitCurve

/-!
# InfoGeometry.GromovWittenErlangen.LieOrbitCurveChecks

Smoke-test `#check` file for the Klein–Gromov orbit-curve lane.

Verifies that all public identifiers exported by `LieOrbitCurve` are
accessible and have the expected types.
-/

noncomputable section

-- §1  Root shadow and GKM orbit-curve skeleton
#check @InfoGeometry.GromovWittenErlangen.HomogeneousRootShadow
#check @InfoGeometry.GromovWittenErlangen.HomogeneousRootShadow.FixedLabel
#check @InfoGeometry.GromovWittenErlangen.HomogeneousRootShadow.RootLabel
#check @InfoGeometry.GromovWittenErlangen.HomogeneousRootShadow.CurveDegree
#check @InfoGeometry.GromovWittenErlangen.HomogeneousRootShadow.rootDegree
#check @InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness
#check @InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness.rootShadow
#check @InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness.fixedSector
#check @InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness.OrbitCurve
#check @InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness.orbitRoot
#check @InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness.orbitDegree
#check @InfoGeometry.GromovWittenErlangen.LieOrbitCurveWitness.orbitDegree_eq_rootDegree
#check @InfoGeometry.GromovWittenErlangen.GKMOrbitCurveWitness

-- §2  Localization graph skeleton
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness.orbitWitness
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness.Vertex
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness.Edge
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness.vertexLabel
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness.source
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness.edgeCurve
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness.edgeDegree
#check @InfoGeometry.GromovWittenErlangen.LocalizationGraphWitness.edgeDegree_eq

-- §3  Langlands-dual transport
#check @InfoGeometry.GromovWittenErlangen.LanglandsDualCurveDegreeTransport
#check @InfoGeometry.GromovWittenErlangen.LanglandsDualCurveDegreeTransport.degreeToDualRoot
#check @InfoGeometry.GromovWittenErlangen.LanglandsDualCurveDegreeTransport.rootToDualDegree
#check @InfoGeometry.GromovWittenErlangen.LanglandsDualOrbitCurveWitness
#check @InfoGeometry.GromovWittenErlangen.LanglandsDualOrbitCurveWitness.DualGroup
#check @InfoGeometry.GromovWittenErlangen.LanglandsDualOrbitCurveWitness.dualShadow
#check @InfoGeometry.GromovWittenErlangen.LanglandsDualOrbitCurveWitness.dualTransport
#check @InfoGeometry.GromovWittenErlangen.LanglandsKleinGromovPacket

-- §4  Virtual localization payload
#check @InfoGeometry.GromovWittenErlangen.VirtualLocalizationOrbitPacket
#check @InfoGeometry.GromovWittenErlangen.VirtualLocalizationOrbitPacket.graph
#check @InfoGeometry.GromovWittenErlangen.VirtualLocalizationOrbitPacket.vertexContribution
#check @InfoGeometry.GromovWittenErlangen.VirtualLocalizationOrbitPacket.edgeContribution

-- §5  Owner packet
#check @InfoGeometry.GromovWittenErlangen.KleinGromovPacket
#check @InfoGeometry.GromovWittenErlangen.KleinGromovPacket.orbitCurves
#check @InfoGeometry.GromovWittenErlangen.KleinGromovPacket.localizationGraph
#check @InfoGeometry.GromovWittenErlangen.KleinGromovPacket.dualTransport
#check @InfoGeometry.GromovWittenErlangen.KleinGromovPacket.virtualLocalization

-- §6  Owner constructors
#check @InfoGeometry.GromovWittenErlangen.constructKleinGromovPacket
