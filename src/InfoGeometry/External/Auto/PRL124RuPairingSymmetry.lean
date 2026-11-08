import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace PRL124RuPairingSymmetry

abbrev Q := ℚ

def doi : String := "10.1103/PhysRevLett.124.062501"
def nucleusA : ℕ := 88
def protonNumberZ : ℕ := 44
def neutronNumberN : ℕ := 44
def isSelfConjugate : Bool := neutronNumberN == protonNumberZ
def twoTz : Int := (neutronNumberN : Int) - (protonNumberZ : Int)
def groundBandParityPlus : Bool := true

def su2GeneratorCount : ℕ := 3
def su2Rank : ℕ := 1
def spinIsospinGeneratorCount : ℕ := su2GeneratorCount + su2GeneratorCount
def spinIsospinRank : ℕ := su2Rank + su2Rank
def cartanGeneratorCount : ℕ := 2

inductive Cartan where
  | Jz
  | Tz
  deriving DecidableEq, Repr

inductive RaisingLowering where
  | Jplus | Jminus | Tplus | Tminus
  deriving DecidableEq, Repr

def su2RootPlus : Int := 2
def su2RootMinus : Int := -2
def commutatorJJzEigen (root : Int) : Int := root
def commutatorTTzEigen (root : Int) : Int := root

def casimirSU2FromTwoJ (twoJ : ℕ) : Q := (twoJ * (twoJ + 2) : Q) / 4
def spinCasimir (I : ℕ) : Q := casimirSU2FromTwoJ (2*I)
def isospinCasimir (T : ℕ) : Q := casimirSU2FromTwoJ (2*T)

structure PairingState where
  T : ℕ
  I : ℕ
  deriving DecidableEq, Repr

def isovectorPair : PairingState := ⟨1, 0⟩
def isoscalarPair : PairingState := ⟨0, 1⟩

def isovectorPairT : ℕ := isovectorPair.T
def isovectorPairI : ℕ := isovectorPair.I
def isoscalarPairT : ℕ := isoscalarPair.T
def isoscalarPairMinimalI : ℕ := isoscalarPair.I
def isovectorPairMultiplicity : ℕ := 3
def isoscalarSpinAlignedMultiplicity : ℕ := 3
def npIsovectorComponentCount : ℕ := 1
def likeParticlePairComponentCount : ℕ := 2

def observedBandSpins : List ℕ := [0,2,4,6,8,10,12,14]
def observedBandLength : ℕ := observedBandSpins.length
def newGamma1063_keV : ℕ := 1063
def newGamma1153_keV : ℕ := 1153
def newGamma1253_keV : ℕ := 1253
def newTransitionCount : ℕ := 3

def omegaNormal_c : Q := 47/100
def omegaRu88_c : Q := 54/100
def omegaDelay : Q := omegaRu88_c - omegaNormal_c
def omegaRatio : Q := omegaRu88_c / omegaNormal_c

def modelSpaceOrbitCount : ℕ := 5
def twoJ_p1_2 : ℕ := 1
def twoJ_p3_2 : ℕ := 3
def twoJ_f5_2 : ℕ := 5
def twoJ_g9_2 : ℕ := 9
def twoJ_d5_2 : ℕ := 5
def degeneracyFromTwoJ (twoJ : ℕ) : ℕ := twoJ + 1
def fpgdDegeneracyPerSpecies : ℕ :=
  degeneracyFromTwoJ twoJ_p1_2 + degeneracyFromTwoJ twoJ_p3_2 + degeneracyFromTwoJ twoJ_f5_2 +
  degeneracyFromTwoJ twoJ_g9_2 + degeneracyFromTwoJ twoJ_d5_2
def fpgdProtonNeutronDegeneracy : ℕ := 2 * fpgdDegeneracyPerSpecies

def reactionProjectileA : ℕ := 36
def reactionProjectileZ : ℕ := 18
def reactionTargetA : ℕ := 54
def reactionTargetZ : ℕ := 26
def evaporatedNeutrons : ℕ := 2
def reactionProductA : ℕ := reactionProjectileA + reactionTargetA - evaporatedNeutrons
def reactionProductZ : ℕ := reactionProjectileZ + reactionTargetZ

def pairingHamiltonianTermCount : ℕ := 4
def isospinConservingHamiltonian : Bool := true

theorem nucleusA_eq : nucleusA = 88 := by
  norm_num [nucleusA]

theorem protonNumberZ_eq : protonNumberZ = 44 := by
  norm_num [protonNumberZ]

theorem neutronNumberN_eq : neutronNumberN = 44 := by
  norm_num [neutronNumberN]

theorem neutronNumberN_eq_protonNumberZ : neutronNumberN = protonNumberZ := by
  norm_num [neutronNumberN, protonNumberZ]

theorem isSelfConjugate_eq_true : isSelfConjugate = true := by
  simp [isSelfConjugate, neutronNumberN, protonNumberZ]

theorem twoTz_eq_zero : twoTz = 0 := by
  norm_num [twoTz, neutronNumberN, protonNumberZ]

theorem reactionProductA_eq : reactionProductA = 88 := by
  norm_num [reactionProductA, reactionProjectileA, reactionTargetA, evaporatedNeutrons]

theorem reactionProductZ_eq : reactionProductZ = 44 := by
  norm_num [reactionProductZ, reactionProjectileZ, reactionTargetZ]

theorem su2GeneratorCount_eq : su2GeneratorCount = 3 := by
  norm_num [su2GeneratorCount]

theorem su2Rank_eq : su2Rank = 1 := by
  norm_num [su2Rank]

theorem spinIsospinGeneratorCount_eq : spinIsospinGeneratorCount = 6 := by
  norm_num [spinIsospinGeneratorCount, su2GeneratorCount]

theorem spinIsospinRank_eq : spinIsospinRank = 2 := by
  norm_num [spinIsospinRank, su2Rank]

theorem cartanGeneratorCount_eq : cartanGeneratorCount = 2 := by
  norm_num [cartanGeneratorCount]

theorem commutatorJJzEigen_su2RootPlus_eq : commutatorJJzEigen su2RootPlus = 2 := by
  norm_num [commutatorJJzEigen, su2RootPlus]

theorem commutatorJJzEigen_su2RootMinus_eq : commutatorJJzEigen su2RootMinus = -2 := by
  norm_num [commutatorJJzEigen, su2RootMinus]

theorem commutatorTTzEigen_su2RootPlus_eq : commutatorTTzEigen su2RootPlus = 2 := by
  norm_num [commutatorTTzEigen, su2RootPlus]

theorem commutatorTTzEigen_su2RootMinus_eq : commutatorTTzEigen su2RootMinus = -2 := by
  norm_num [commutatorTTzEigen, su2RootMinus]

theorem isovectorPairT_eq : isovectorPairT = 1 := by
  simp [isovectorPairT, isovectorPair]

theorem isovectorPairI_eq : isovectorPairI = 0 := by
  simp [isovectorPairI, isovectorPair]

theorem isoscalarPairT_eq : isoscalarPairT = 0 := by
  simp [isoscalarPairT, isoscalarPair]

theorem isoscalarPairMinimalI_eq : isoscalarPairMinimalI = 1 := by
  simp [isoscalarPairMinimalI, isoscalarPair]

theorem isovectorPairMultiplicity_eq : isovectorPairMultiplicity = 3 := by
  norm_num [isovectorPairMultiplicity]

theorem isoscalarSpinAlignedMultiplicity_eq : isoscalarSpinAlignedMultiplicity = 3 := by
  norm_num [isoscalarSpinAlignedMultiplicity]

theorem npIsovectorComponentCount_eq : npIsovectorComponentCount = 1 := by
  norm_num [npIsovectorComponentCount]

theorem likeParticlePairComponentCount_eq : likeParticlePairComponentCount = 2 := by
  norm_num [likeParticlePairComponentCount]

theorem spinCasimir_zero_eq : spinCasimir 0 = 0 := by
  norm_num [spinCasimir, casimirSU2FromTwoJ]

theorem spinCasimir_two_eq : spinCasimir 2 = 6 := by
  norm_num [spinCasimir, casimirSU2FromTwoJ]

theorem spinCasimir_fourteen_eq : spinCasimir 14 = 210 := by
  norm_num [spinCasimir, casimirSU2FromTwoJ]

theorem isospinCasimir_zero_eq : isospinCasimir 0 = 0 := by
  norm_num [isospinCasimir, casimirSU2FromTwoJ]

theorem isospinCasimir_one_eq : isospinCasimir 1 = 2 := by
  norm_num [isospinCasimir, casimirSU2FromTwoJ]

theorem observedBandLength_eq : observedBandLength = 8 := by
  norm_num [observedBandLength, observedBandSpins]

theorem newTransitionCount_eq : newTransitionCount = 3 := by
  norm_num [newTransitionCount]

theorem gammaEnergySum_eq :
    newGamma1063_keV + newGamma1153_keV + newGamma1253_keV = 3469 := by
  norm_num [newGamma1063_keV, newGamma1153_keV, newGamma1253_keV]

theorem omegaNormal_c_eq : omegaNormal_c = 47/100 := by
  norm_num [omegaNormal_c]

theorem omegaRu88_c_eq : omegaRu88_c = 54/100 := by
  norm_num [omegaRu88_c]

theorem omegaDelay_eq : omegaDelay = 7/100 := by
  norm_num [omegaDelay, omegaRu88_c, omegaNormal_c]

theorem omegaRatio_eq : omegaRatio = 54/47 := by
  norm_num [omegaRatio, omegaRu88_c, omegaNormal_c]

theorem omegaNormal_c_lt_omegaRu88_c : omegaNormal_c < omegaRu88_c := by
  norm_num [omegaNormal_c, omegaRu88_c]

theorem modelSpaceOrbitCount_eq : modelSpaceOrbitCount = 5 := by
  norm_num [modelSpaceOrbitCount]

theorem degeneracyFromTwoJ_p1_2_eq : degeneracyFromTwoJ twoJ_p1_2 = 2 := by
  norm_num [degeneracyFromTwoJ, twoJ_p1_2]

theorem degeneracyFromTwoJ_p3_2_eq : degeneracyFromTwoJ twoJ_p3_2 = 4 := by
  norm_num [degeneracyFromTwoJ, twoJ_p3_2]

theorem degeneracyFromTwoJ_f5_2_eq : degeneracyFromTwoJ twoJ_f5_2 = 6 := by
  norm_num [degeneracyFromTwoJ, twoJ_f5_2]

theorem degeneracyFromTwoJ_g9_2_eq : degeneracyFromTwoJ twoJ_g9_2 = 10 := by
  norm_num [degeneracyFromTwoJ, twoJ_g9_2]

theorem degeneracyFromTwoJ_d5_2_eq : degeneracyFromTwoJ twoJ_d5_2 = 6 := by
  norm_num [degeneracyFromTwoJ, twoJ_d5_2]

theorem fpgdDegeneracyPerSpecies_eq : fpgdDegeneracyPerSpecies = 28 := by
  norm_num [fpgdDegeneracyPerSpecies, degeneracyFromTwoJ, twoJ_p1_2, twoJ_p3_2, twoJ_f5_2,
    twoJ_g9_2, twoJ_d5_2]

theorem fpgdProtonNeutronDegeneracy_eq : fpgdProtonNeutronDegeneracy = 56 := by
  norm_num [fpgdProtonNeutronDegeneracy, fpgdDegeneracyPerSpecies, degeneracyFromTwoJ, twoJ_p1_2,
    twoJ_p3_2, twoJ_f5_2, twoJ_g9_2, twoJ_d5_2]

theorem isospinConservingHamiltonian_eq_true : isospinConservingHamiltonian = true := by
  simp [isospinConservingHamiltonian]

end PRL124RuPairingSymmetry

end noncomputable section
