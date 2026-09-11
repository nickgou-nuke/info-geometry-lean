import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace StrongCPAeonTheta

abbrev Q := ℚ

def aeonCount : ℕ := 3
def thetaAeonIndex : ℕ := 3
def qDial : Q := 1/10
def thetaSedimentWeight : Q := qDial ^ thetaAeonIndex
def inverseThetaScale : Q := (10 : Q) ^ thetaAeonIndex

def su3Rank : ℕ := 2
def su3RootCount : ℕ := 6
def su3CartanCount : ℕ := 2
def su3GeneratorCount : ℕ := 8
def su3WeylGroupOrder : ℕ := 6
def colorQuadraticCasimirFund : Q := 4/3
def colorQuadraticCasimirAdj : Q := 3

def su2Rank : ℕ := 1
def su2GeneratorCount : ℕ := 3
def u1Rank : ℕ := 1
def smRank : ℕ := su3Rank + su2Rank + u1Rank
def smGeneratorCount : ℕ := su3GeneratorCount + su2GeneratorCount + u1Rank

inductive ColorCartan where
  | T3_color | T8_color
  deriving DecidableEq, Repr

inductive ColorRoot where
  | alpha1 | alpha2 | alpha12 | neg_alpha1 | neg_alpha2 | neg_alpha12
  deriving DecidableEq, Repr

inductive ThetaSector where
  | thetaVacuum | instanton | antiInstanton | axionCounterterm | cpEvenClosure
  deriving DecidableEq, Repr

def rootHeight : ColorRoot → Int
  | ColorRoot.alpha1 => 1
  | ColorRoot.alpha2 => 1
  | ColorRoot.alpha12 => 2
  | ColorRoot.neg_alpha1 => -1
  | ColorRoot.neg_alpha2 => -1
  | ColorRoot.neg_alpha12 => -2

def cpTheta (θ : Q) : Q := -θ
def cpTwiceTheta (θ : Q) : Q := cpTheta (cpTheta θ)
def axionCounterterm (θ : Q) : Q := -θ
def effectiveTheta (θ a : Q) : Q := θ + a
def thetaCancelled (θ : Q) : Q := effectiveTheta θ (axionCounterterm θ)

def instantonNumber : Int := 1
def antiInstantonNumber : Int := -1
def topologicalChargePair : Int := instantonNumber + antiInstantonNumber

def pontryaginDensityGeneratorCount : ℕ := 1
def thetaIdealGeneratorCount : ℕ := 2
def dmoduleCCRGeneratorCount : ℕ := 1

class GaugeBundle (B : Type*) where
  rank : ℕ

class CharacteristicClasses (B : Type*) [GaugeBundle B] where
  c1 : Q
  c2 : Q
  c3 : Q
  p1 : Q

class TriangleAnomaly (B : Type*) [GaugeBundle B] where
  anomaly : Q

inductive SU3Bundle where
  | carrier
  deriving DecidableEq, Repr

inductive SU2Bundle where
  | carrier
  deriving DecidableEq, Repr

inductive U1Bundle where
  | carrier
  deriving DecidableEq, Repr

inductive SMFermionBundle where
  | carrier
  deriving DecidableEq, Repr

instance : GaugeBundle SU3Bundle where rank := 3
instance : GaugeBundle SU2Bundle where rank := 2
instance : GaugeBundle U1Bundle where rank := 1
instance : GaugeBundle SMFermionBundle where rank := 1

instance : CharacteristicClasses SU3Bundle where
  c1 := 0
  c2 := 1
  c3 := 0
  p1 := 0

instance : TriangleAnomaly SU3Bundle where anomaly := 0
instance : TriangleAnomaly SU2Bundle where anomaly := 0
instance : TriangleAnomaly SMFermionBundle where anomaly := 0

def u1AxialAnomalyCoeff [CharacteristicClasses SU3Bundle] : Q :=
  (su3GeneratorCount : Q) * CharacteristicClasses.c2 (B := SU3Bundle)

def colorAnomaly [TriangleAnomaly SU3Bundle] : Q :=
  TriangleAnomaly.anomaly (B := SU3Bundle)

def weakAnomaly [TriangleAnomaly SU2Bundle] : Q :=
  TriangleAnomaly.anomaly (B := SU2Bundle)

def generationAnomalyTotal [TriangleAnomaly SMFermionBundle] : Q :=
  TriangleAnomaly.anomaly (B := SMFermionBundle)

def d2Bidegree (p q : ℕ) : ℕ × Int := (p+2, (q : Int)-1)

lemma aeonCount_eq : aeonCount = 3 := by
  norm_num [aeonCount]

lemma thetaAeonIndex_eq : thetaAeonIndex = 3 := by
  norm_num [thetaAeonIndex]

lemma qDial_eq : qDial = 1 / 10 := by
  norm_num [qDial]

lemma thetaSedimentWeight_eq : thetaSedimentWeight = 1 / 1000 := by
  norm_num [thetaSedimentWeight, qDial, thetaAeonIndex]

lemma inverseThetaScale_eq : inverseThetaScale = 1000 := by
  norm_num [inverseThetaScale, thetaAeonIndex]

lemma su3Rank_eq : su3Rank = 2 := by
  norm_num [su3Rank]

lemma su3RootCount_eq : su3RootCount = 6 := by
  norm_num [su3RootCount]

lemma su3CartanCount_eq : su3CartanCount = 2 := by
  norm_num [su3CartanCount]

lemma su3GeneratorCount_eq : su3GeneratorCount = 8 := by
  norm_num [su3GeneratorCount]

lemma su3WeylGroupOrder_eq : su3WeylGroupOrder = 6 := by
  norm_num [su3WeylGroupOrder]

lemma smRank_eq : smRank = 4 := by
  norm_num [smRank, su3Rank, su2Rank, u1Rank]

lemma smGeneratorCount_eq : smGeneratorCount = 12 := by
  norm_num [smGeneratorCount, su3GeneratorCount, su2GeneratorCount, u1Rank]

lemma colorQuadraticCasimirFund_eq : colorQuadraticCasimirFund = 4 / 3 := by
  norm_num [colorQuadraticCasimirFund]

lemma colorQuadraticCasimirAdj_eq : colorQuadraticCasimirAdj = 3 := by
  norm_num [colorQuadraticCasimirAdj]

lemma rootHeight_alpha1_eq : rootHeight ColorRoot.alpha1 = 1 := by
  norm_num [rootHeight]

lemma rootHeight_alpha2_eq : rootHeight ColorRoot.alpha2 = 1 := by
  norm_num [rootHeight]

lemma rootHeight_alpha12_eq : rootHeight ColorRoot.alpha12 = 2 := by
  norm_num [rootHeight]

lemma rootHeight_neg_alpha1_eq : rootHeight ColorRoot.neg_alpha1 = -1 := by
  norm_num [rootHeight]

lemma rootHeight_neg_alpha2_eq : rootHeight ColorRoot.neg_alpha2 = -1 := by
  norm_num [rootHeight]

lemma rootHeight_neg_alpha12_eq : rootHeight ColorRoot.neg_alpha12 = -2 := by
  norm_num [rootHeight]

lemma cpTwiceTheta_eq (θ : Q) : cpTwiceTheta θ = θ := by
  simp [cpTwiceTheta, cpTheta]

lemma thetaCancelled_eq_zero (θ : Q) : thetaCancelled θ = 0 := by
  simp [thetaCancelled, effectiveTheta, axionCounterterm]

lemma instantonNumber_eq : instantonNumber = 1 := by
  norm_num [instantonNumber]

lemma antiInstantonNumber_eq : antiInstantonNumber = -1 := by
  norm_num [antiInstantonNumber]

lemma topologicalChargePair_eq_zero : topologicalChargePair = 0 := by
  norm_num [topologicalChargePair, instantonNumber, antiInstantonNumber]

lemma pontryaginDensityGeneratorCount_eq : pontryaginDensityGeneratorCount = 1 := by
  norm_num [pontryaginDensityGeneratorCount]

lemma thetaIdealGeneratorCount_eq : thetaIdealGeneratorCount = 2 := by
  norm_num [thetaIdealGeneratorCount]

lemma dmoduleCCRGeneratorCount_eq : dmoduleCCRGeneratorCount = 1 := by
  norm_num [dmoduleCCRGeneratorCount]

lemma u1AxialAnomalyCoeff_eq : u1AxialAnomalyCoeff = 8 := by
  norm_num [u1AxialAnomalyCoeff, CharacteristicClasses.c2, su3GeneratorCount]

lemma colorAnomaly_eq : colorAnomaly = 0 := by
  norm_num [colorAnomaly, TriangleAnomaly.anomaly]

lemma weakAnomaly_eq : weakAnomaly = 0 := by
  norm_num [weakAnomaly, TriangleAnomaly.anomaly]

lemma generationAnomalyTotal_eq : generationAnomalyTotal = 0 := by
  norm_num [generationAnomalyTotal, TriangleAnomaly.anomaly]

lemma d2Bidegree_zero_one_eq : d2Bidegree 0 1 = (2, 0) := by
  norm_num [d2Bidegree]

lemma d2Bidegree_two_one_eq : d2Bidegree 2 1 = (4, 0) := by
  norm_num [d2Bidegree]

inductive Concept where
  | Third_Aeon_Sediment | Theta_Vacuum | SU3_Color | CP_Twist | Axion_Counterterm | Strong_CP_Closure
  deriving DecidableEq, Repr

inductive Edge where
  | generates | carries | flips | cancels | closes
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Third_Aeon_Sediment, Edge.generates, Concept.Theta_Vacuum => true
  | Concept.Theta_Vacuum, Edge.carries, Concept.SU3_Color => true
  | Concept.CP_Twist, Edge.flips, Concept.Theta_Vacuum => true
  | Concept.Axion_Counterterm, Edge.cancels, Concept.Theta_Vacuum => true
  | Concept.Theta_Vacuum, Edge.closes, Concept.Strong_CP_Closure => true
  | _, _, _ => false

lemma thirdAeonSediment_generates_thetaVacuum :
    edgeHolds Concept.Third_Aeon_Sediment Edge.generates Concept.Theta_Vacuum = true := by
  simp [edgeHolds]

lemma thetaVacuum_carries_su3Color :
    edgeHolds Concept.Theta_Vacuum Edge.carries Concept.SU3_Color = true := by
  simp [edgeHolds]

lemma cpTwist_flips_thetaVacuum :
    edgeHolds Concept.CP_Twist Edge.flips Concept.Theta_Vacuum = true := by
  simp [edgeHolds]

lemma axionCounterterm_cancels_thetaVacuum :
    edgeHolds Concept.Axion_Counterterm Edge.cancels Concept.Theta_Vacuum = true := by
  simp [edgeHolds]

lemma thetaVacuum_closes_strongCPClosure :
    edgeHolds Concept.Theta_Vacuum Edge.closes Concept.Strong_CP_Closure = true := by
  simp [edgeHolds]

end StrongCPAeonTheta

end noncomputable section
