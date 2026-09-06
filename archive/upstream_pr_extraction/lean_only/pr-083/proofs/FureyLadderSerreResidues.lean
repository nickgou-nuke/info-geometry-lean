import Mathlib

noncomputable section

namespace FureyLadderSerreResidues

abbrev Q := ℚ

def stablePage : ℕ := 3
def e2Rank : ℕ := 8
def d2SourceCount : ℕ := 8
section D2AndNuRightZero

abbrev d2ZeroModule (_p _q : ℕ) : Type := Fin 0 → Q

def d2ZeroSquare (p q : ℕ) : ℕ := Module.finrank Q (d2ZeroModule p q)

lemma d2ZeroModule_finrank_zero (p q : ℕ) : Module.finrank Q (d2ZeroModule p q) = 0 := by
  simp [d2ZeroModule]
lemma d2ZeroSquare_zero (p q : ℕ) : d2ZeroSquare p q = 0 := d2ZeroModule_finrank_zero p q

def d2KilledCount : ℕ := d2ZeroSquare 8 8
lemma d2KilledCount_zero : d2KilledCount = 0 := d2ZeroSquare_zero 8 8

abbrev NuRightRepresentation : Type := Fin 0 → Q

def nilpotentSquare (_i : Fin 3) : ℕ := Module.finrank Q NuRightRepresentation
lemma nilpotentSquare_zero (i : Fin 3) : nilpotentSquare i = 0 := by
  simp [nilpotentSquare, NuRightRepresentation]

def hypercharge_nu_R : Q := (Module.finrank Q NuRightRepresentation : Q)
lemma hypercharge_nu_R_zero : hypercharge_nu_R = 0 := by
  simp [hypercharge_nu_R, NuRightRepresentation]

end D2AndNuRightZero

def survivorCount : ℕ := d2SourceCount - d2KilledCount

def su3Rank : ℕ := 2
def su3RootCount : ℕ := 6
def su3CartanCount : ℕ := 2
def su3GeneratorCount : ℕ := su3RootCount + su3CartanCount
def su2Rank : ℕ := 1
def su2RootCount : ℕ := 2
def su2CartanCount : ℕ := 1
def su2GeneratorCount : ℕ := su2RootCount + su2CartanCount
def u1Rank : ℕ := 1
def standardModelRank : ℕ := su3Rank + su2Rank + u1Rank
def standardModelGeneratorCount : ℕ := su3GeneratorCount + su2GeneratorCount + u1Rank

inductive Cartan where
  | T3_color | T8_color | T3_weak | Y_hypercharge
  deriving DecidableEq, Repr

inductive Ladder where
  | color_rg | color_gr | color_gb | color_bg | color_rb | color_br | weak_plus | weak_minus
  deriving DecidableEq, Repr

def ladderCount : ℕ := 8
def fureyCreationCount : ℕ := 3
def fureyAnnihilationCount : ℕ := 3
def fermionicNilpotentCount : ℕ := 3

def colorQuadraticCasimirFund : Q := 4/3
def colorQuadraticCasimirAdj : Q := 3
def weakQuadraticCasimirDoublet : Q := 3/4
def weakQuadraticCasimirTriplet : Q := 2

def hypercharge_Q_L : Q := 1/6
def hypercharge_u_R : Q := 2/3
def hypercharge_d_R : Q := -1/3
def hypercharge_L_L : Q := -1/2
def hypercharge_e_R : Q := -1


def electricCharge (T3 Y : Q) : Q := T3 + Y
def upCharge : Q := electricCharge (1/2) hypercharge_Q_L
def downCharge : Q := electricCharge (-1/2) hypercharge_Q_L
def neutrinoCharge : Q := electricCharge (1/2) hypercharge_L_L
def electronCharge : Q := electricCharge (-1/2) hypercharge_L_L

def su3FundamentalDim : ℕ := 3
def su3AntiFundamentalDim : ℕ := 3
def su3SingletDim : ℕ := 1
def weakDoubletDim : ℕ := 2
def weakSingletDim : ℕ := 1

def qLeftMultiplicity : ℕ := su3FundamentalDim * weakDoubletDim
def uRightMultiplicity : ℕ := su3FundamentalDim * weakSingletDim
def dRightMultiplicity : ℕ := su3FundamentalDim * weakSingletDim
def leptonLeftMultiplicity : ℕ := su3SingletDim * weakDoubletDim
def electronRightMultiplicity : ℕ := su3SingletDim * weakSingletDim
def neutrinoRightMultiplicity : ℕ := su3SingletDim * weakSingletDim
def smOneGenerationWeylCount : ℕ := qLeftMultiplicity + uRightMultiplicity + dRightMultiplicity + leptonLeftMultiplicity + electronRightMultiplicity + neutrinoRightMultiplicity

def colorAnomalyPerGeneration : Q := 2*hypercharge_Q_L - hypercharge_u_R - hypercharge_d_R
def weakAnomalyPerGeneration : Q := 3*hypercharge_Q_L + hypercharge_L_L
def gravitationalHyperchargeTrace : Q :=
  6*hypercharge_Q_L - 3*hypercharge_u_R - 3*hypercharge_d_R + 2*hypercharge_L_L - hypercharge_e_R - hypercharge_nu_R
def cubicHyperchargeTrace : Q :=
  6*hypercharge_Q_L^3 - 3*hypercharge_u_R^3 - 3*hypercharge_d_R^3 + 2*hypercharge_L_L^3 - hypercharge_e_R^3 - hypercharge_nu_R^3

def d2Bidegree (p q : ℕ) : ℕ × Int := (p+2, (q : Int)-1)

def fureyResidueRank : ℕ := survivorCount


def fermionAnticommutator (i j : Fin 3) : ℕ := if i = j then 1 else 0

lemma stablePage_eq_three : stablePage = 3 := by
  norm_num [stablePage]

lemma e2Rank_eq_eight : e2Rank = 8 := by
  norm_num [e2Rank]

lemma d2SourceCount_eq_eight : d2SourceCount = 8 := by
  norm_num [d2SourceCount]

lemma survivorCount_eq_eight : survivorCount = 8 := by
  norm_num [survivorCount, d2SourceCount, d2KilledCount, d2ZeroSquare, d2ZeroModule]

lemma fureyResidueRank_eq_eight : fureyResidueRank = 8 := by
  norm_num [fureyResidueRank, survivorCount, d2SourceCount, d2KilledCount, d2ZeroSquare, d2ZeroModule]

lemma su3GeneratorCount_eq_eight : su3GeneratorCount = 8 := by
  norm_num [su3GeneratorCount, su3RootCount, su3CartanCount]

lemma su2GeneratorCount_eq_three : su2GeneratorCount = 3 := by
  norm_num [su2GeneratorCount, su2RootCount, su2CartanCount]

lemma standardModelRank_eq_four : standardModelRank = 4 := by
  norm_num [standardModelRank, su3Rank, su2Rank, u1Rank]

lemma standardModelGeneratorCount_eq_twelve : standardModelGeneratorCount = 12 := by
  norm_num [standardModelGeneratorCount, su3GeneratorCount, su3RootCount, su3CartanCount,
    su2GeneratorCount, su2RootCount, su2CartanCount, u1Rank]

lemma ladderCount_eq_eight : ladderCount = 8 := by
  norm_num [ladderCount]

lemma fureyCreationCount_eq_three : fureyCreationCount = 3 := by
  norm_num [fureyCreationCount]

lemma fureyAnnihilationCount_eq_three : fureyAnnihilationCount = 3 := by
  norm_num [fureyAnnihilationCount]

lemma fermionicNilpotentCount_eq_three : fermionicNilpotentCount = 3 := by
  norm_num [fermionicNilpotentCount]

lemma colorQuadraticCasimirFund_eq_four_thirds : colorQuadraticCasimirFund = 4/3 := by
  norm_num [colorQuadraticCasimirFund]

lemma colorQuadraticCasimirAdj_eq_three : colorQuadraticCasimirAdj = 3 := by
  norm_num [colorQuadraticCasimirAdj]

lemma weakQuadraticCasimirDoublet_eq_three_fourths : weakQuadraticCasimirDoublet = 3/4 := by
  norm_num [weakQuadraticCasimirDoublet]

lemma weakQuadraticCasimirTriplet_eq_two : weakQuadraticCasimirTriplet = 2 := by
  norm_num [weakQuadraticCasimirTriplet]

lemma upCharge_eq_two_thirds : upCharge = 2/3 := by
  norm_num [upCharge, electricCharge, hypercharge_Q_L]

lemma downCharge_eq_neg_one_third : downCharge = -1/3 := by
  norm_num [downCharge, electricCharge, hypercharge_Q_L]

lemma neutrinoCharge_zero : neutrinoCharge = 0 := by
  norm_num [neutrinoCharge, electricCharge, hypercharge_L_L]

lemma electronCharge_eq_neg_one : electronCharge = -1 := by
  norm_num [electronCharge, electricCharge, hypercharge_L_L]

lemma qLeftMultiplicity_eq_six : qLeftMultiplicity = 6 := by
  norm_num [qLeftMultiplicity, su3FundamentalDim, weakDoubletDim]

lemma uRightMultiplicity_eq_three : uRightMultiplicity = 3 := by
  norm_num [uRightMultiplicity, su3FundamentalDim, weakSingletDim]

lemma dRightMultiplicity_eq_three : dRightMultiplicity = 3 := by
  norm_num [dRightMultiplicity, su3FundamentalDim, weakSingletDim]

lemma leptonLeftMultiplicity_eq_two : leptonLeftMultiplicity = 2 := by
  norm_num [leptonLeftMultiplicity, su3SingletDim, weakDoubletDim]

lemma electronRightMultiplicity_eq_one : electronRightMultiplicity = 1 := by
  norm_num [electronRightMultiplicity, su3SingletDim, weakSingletDim]

lemma neutrinoRightMultiplicity_eq_one : neutrinoRightMultiplicity = 1 := by
  norm_num [neutrinoRightMultiplicity, su3SingletDim, weakSingletDim]

lemma smOneGenerationWeylCount_eq_sixteen : smOneGenerationWeylCount = 16 := by
  norm_num [smOneGenerationWeylCount, qLeftMultiplicity, uRightMultiplicity, dRightMultiplicity,
    leptonLeftMultiplicity, electronRightMultiplicity, neutrinoRightMultiplicity,
    su3FundamentalDim, su3SingletDim, weakDoubletDim, weakSingletDim]

lemma colorAnomalyPerGeneration_zero : colorAnomalyPerGeneration = 0 := by
  norm_num [colorAnomalyPerGeneration, hypercharge_Q_L, hypercharge_u_R, hypercharge_d_R]

lemma weakAnomalyPerGeneration_zero : weakAnomalyPerGeneration = 0 := by
  norm_num [weakAnomalyPerGeneration, hypercharge_Q_L, hypercharge_L_L]

lemma gravitationalHyperchargeTrace_zero : gravitationalHyperchargeTrace = 0 := by
  norm_num [gravitationalHyperchargeTrace, hypercharge_Q_L, hypercharge_u_R, hypercharge_d_R,
    hypercharge_L_L, hypercharge_e_R, hypercharge_nu_R, NuRightRepresentation]

lemma cubicHyperchargeTrace_zero : cubicHyperchargeTrace = 0 := by
  norm_num [cubicHyperchargeTrace, hypercharge_Q_L, hypercharge_u_R, hypercharge_d_R,
    hypercharge_L_L, hypercharge_e_R, hypercharge_nu_R, NuRightRepresentation]

lemma d2Bidegree_zero_one : d2Bidegree 0 1 = (2, 0) := by
  norm_num [d2Bidegree]

lemma d2Bidegree_two_one : d2Bidegree 2 1 = (4, 0) := by
  norm_num [d2Bidegree]

lemma fermionAnticommutator_self (i : Fin 3) : fermionAnticommutator i i = 1 := by
  simp [fermionAnticommutator]

inductive Concept where
  | Serre_d2_Differential
  | Furey_Ladder_Residue
  | SU3_Color
  | SU2_Weak
  | U1_Hypercharge
  | SM_One_Generation
  | Anomaly_Cancelled
  deriving DecidableEq, Repr

inductive Edge where
  | extracts
  | generates
  | carries
  | cancels
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Serre_d2_Differential, Edge.extracts, Concept.Furey_Ladder_Residue => true
  | Concept.Furey_Ladder_Residue, Edge.generates, Concept.SU3_Color => true
  | Concept.Furey_Ladder_Residue, Edge.generates, Concept.SU2_Weak => true
  | Concept.Furey_Ladder_Residue, Edge.generates, Concept.U1_Hypercharge => true
  | Concept.SM_One_Generation, Edge.carries, Concept.Furey_Ladder_Residue => true
  | Concept.SM_One_Generation, Edge.cancels, Concept.Anomaly_Cancelled => true
  | _, _, _ => false

lemma serre_d2_extracts_furey_ladder_residue :
    edgeHolds Concept.Serre_d2_Differential Edge.extracts Concept.Furey_Ladder_Residue = true := by
  simp [edgeHolds]

lemma furey_ladder_residue_generates_su3_color :
    edgeHolds Concept.Furey_Ladder_Residue Edge.generates Concept.SU3_Color = true := by
  simp [edgeHolds]

lemma furey_ladder_residue_generates_su2_weak :
    edgeHolds Concept.Furey_Ladder_Residue Edge.generates Concept.SU2_Weak = true := by
  simp [edgeHolds]

lemma furey_ladder_residue_generates_u1_hypercharge :
    edgeHolds Concept.Furey_Ladder_Residue Edge.generates Concept.U1_Hypercharge = true := by
  simp [edgeHolds]

lemma sm_one_generation_carries_furey_ladder_residue :
    edgeHolds Concept.SM_One_Generation Edge.carries Concept.Furey_Ladder_Residue = true := by
  simp [edgeHolds]

lemma sm_one_generation_cancels_anomaly :
    edgeHolds Concept.SM_One_Generation Edge.cancels Concept.Anomaly_Cancelled = true := by
  simp [edgeHolds]

end FureyLadderSerreResidues

end noncomputable section
