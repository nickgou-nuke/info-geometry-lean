import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

noncomputable section

namespace HoTTInfinityBridge

abbrev Q := ℚ

def hottLeanHead : String := "31133dd5b25226ea897f8aa5e2e43b61392459eb"
def groundZeroHead : String := "2cbca29485c2e6f420c120365e00fe3b70db3acf"
def leanFibredCategoriesHead : String := "a58604a389544523aa171daf890386fb8317568b"
def mathlibHomotopyEquivModule : String := "Mathlib.Topology.Homotopy.Equiv"
def hott3Head : String := "7ead7a8a2503049eacd45cbff6587802bae2add2"
def spectralHead : String := "3b078f5f1de251637decf04bd3fc8aa01930a6b3"
def infinityCosmosHead : String := "21a877847c8121f3ecd63fa9fdf3fd9ed2272823"
def quasicategoryHead : String := "5222748cad6a66335e03449ea0b3de6b44c53b05"
def topcatModelCategoryHead : String := "6c0c356fea469689fe76baeb47ba773460dfacee"

def repositorySourceCount : ℕ := 8
def mathlibSourceCount : ℕ := 1
def totalSourceCount : ℕ := repositorySourceCount + mathlibSourceCount

def hottLayerCount : ℕ := 3
def categoryLayerCount : ℕ := 4
def spectralLayerCount : ℕ := 1
def modelLayerCount : ℕ := 1
def bridgeLayerCount : ℕ := hottLayerCount + categoryLayerCount + spectralLayerCount + modelLayerCount

inductive SourceNode where
  | HoTTLean | GroundZero | LeanFibredCategories | MathlibHomotopyEquiv | Hott3 | Spectral | InfinityCosmos | Quasicategory | TopcatModelCategory
  deriving DecidableEq, Repr

inductive StructureNode where
  | TypeTheory | HomotopyEquivalence | FibredCategory | ExactCouple | SerreSpectralSequence | InfinityCosmos | Quasicategory | ModelCategory | TopologicalCategory
  deriving DecidableEq, Repr

inductive BridgeEdge where
  | presents | imports | refines | supports | compares | localizes
  deriving DecidableEq, Repr

def sourceOrdinal : SourceNode → ℕ
  | SourceNode.HoTTLean => 1
  | SourceNode.GroundZero => 2
  | SourceNode.LeanFibredCategories => 3
  | SourceNode.MathlibHomotopyEquiv => 4
  | SourceNode.Hott3 => 5
  | SourceNode.Spectral => 6
  | SourceNode.InfinityCosmos => 7
  | SourceNode.Quasicategory => 8
  | SourceNode.TopcatModelCategory => 9

def structureOrdinal : StructureNode → ℕ
  | StructureNode.TypeTheory => 1
  | StructureNode.HomotopyEquivalence => 2
  | StructureNode.FibredCategory => 3
  | StructureNode.ExactCouple => 4
  | StructureNode.SerreSpectralSequence => 5
  | StructureNode.InfinityCosmos => 6
  | StructureNode.Quasicategory => 7
  | StructureNode.ModelCategory => 8
  | StructureNode.TopologicalCategory => 9

def edgeHolds : SourceNode → BridgeEdge → StructureNode → Bool
  | SourceNode.HoTTLean, BridgeEdge.presents, StructureNode.TypeTheory => true
  | SourceNode.GroundZero, BridgeEdge.presents, StructureNode.TypeTheory => true
  | SourceNode.LeanFibredCategories, BridgeEdge.presents, StructureNode.FibredCategory => true
  | SourceNode.MathlibHomotopyEquiv, BridgeEdge.presents, StructureNode.HomotopyEquivalence => true
  | SourceNode.Hott3, BridgeEdge.refines, StructureNode.TypeTheory => true
  | SourceNode.Spectral, BridgeEdge.presents, StructureNode.ExactCouple => true
  | SourceNode.Spectral, BridgeEdge.presents, StructureNode.SerreSpectralSequence => true
  | SourceNode.InfinityCosmos, BridgeEdge.presents, StructureNode.InfinityCosmos => true
  | SourceNode.Quasicategory, BridgeEdge.presents, StructureNode.Quasicategory => true
  | SourceNode.TopcatModelCategory, BridgeEdge.presents, StructureNode.ModelCategory => true
  | SourceNode.TopcatModelCategory, BridgeEdge.supports, StructureNode.TopologicalCategory => true
  | _, _, _ => false

def compatibilityEdgeCount : ℕ := 11

def homotopyEquivDataFields : ℕ := 4
def exactCoupleMapCount : ℕ := 3
def serrePageStart : ℕ := 2
def serreStablePage : ℕ := 3
def quasicategorySimplexArity : ℕ := 2
def modelCategoryClassCount : ℕ := 3
def fibredCategoryProjectionCount : ℕ := 1

def hottBridgeRank : ℕ := totalSourceCount + bridgeLayerCount + compatibilityEdgeCount
def infinityBridgeSignature : ℕ := homotopyEquivDataFields + exactCoupleMapCount + serrePageStart + serreStablePage + quasicategorySimplexArity + modelCategoryClassCount + fibredCategoryProjectionCount

open CategoryTheory
open CategoryTheory.Limits

section SerreSpectralSequence

-- We assume a higher category V with zero morphisms (e.g. Abelian groups, R-modules, or a stable infinity category)
variable {V : Type*} [Category V] [HasZeroMorphisms V]

-- The E2 page is a bi-indexed family of objects in V
variable (E2 : ℕ → ℤ → V)

-- The d2 differential is a family of morphisms
variable (d2 : ∀ p q, E2 p q ⟶ E2 (p+2) (q-1))

-- A rigorous structure enforcing that d2 acts as a homological differential (d² = 0)
class IsSpectralDifferential2 : Prop where
  d2Square (p : ℕ) (q : ℤ) : d2 p q ≫ d2 (p+2) (q-1) = 0

end SerreSpectralSequence

def d2Bidegree (p q : ℕ) : ℕ × Int := (p+2, (q : Int)-1)

@[simp] theorem repositorySourceCount_eq : repositorySourceCount = 8 := rfl

@[simp] theorem mathlibSourceCount_eq : mathlibSourceCount = 1 := rfl

@[simp] theorem totalSourceCount_eq : totalSourceCount = 9 := by
  norm_num [totalSourceCount, repositorySourceCount, mathlibSourceCount]

@[simp] theorem bridgeLayerCount_eq : bridgeLayerCount = 9 := by
  norm_num [bridgeLayerCount, hottLayerCount, categoryLayerCount, spectralLayerCount, modelLayerCount]

@[simp] theorem compatibilityEdgeCount_eq : compatibilityEdgeCount = 11 := rfl

@[simp] theorem hottBridgeRank_eq : hottBridgeRank = 29 := by
  norm_num [hottBridgeRank, totalSourceCount, repositorySourceCount, mathlibSourceCount,
    bridgeLayerCount, hottLayerCount, categoryLayerCount, spectralLayerCount, modelLayerCount,
    compatibilityEdgeCount]

@[simp] theorem hottLeanHead_eq :
    hottLeanHead = "31133dd5b25226ea897f8aa5e2e43b61392459eb" := rfl

@[simp] theorem groundZeroHead_eq :
    groundZeroHead = "2cbca29485c2e6f420c120365e00fe3b70db3acf" := rfl

@[simp] theorem leanFibredCategoriesHead_eq :
    leanFibredCategoriesHead = "a58604a389544523aa171daf890386fb8317568b" := rfl

@[simp] theorem mathlibHomotopyEquivModule_eq :
    mathlibHomotopyEquivModule = "Mathlib.Topology.Homotopy.Equiv" := rfl

@[simp] theorem hott3Head_eq :
    hott3Head = "7ead7a8a2503049eacd45cbff6587802bae2add2" := rfl

@[simp] theorem spectralHead_eq :
    spectralHead = "3b078f5f1de251637decf04bd3fc8aa01930a6b3" := rfl

@[simp] theorem infinityCosmosHead_eq :
    infinityCosmosHead = "21a877847c8121f3ecd63fa9fdf3fd9ed2272823" := rfl

@[simp] theorem quasicategoryHead_eq :
    quasicategoryHead = "5222748cad6a66335e03449ea0b3de6b44c53b05" := rfl

@[simp] theorem topcatModelCategoryHead_eq :
    topcatModelCategoryHead = "6c0c356fea469689fe76baeb47ba773460dfacee" := rfl

@[simp] theorem sourceOrdinal_HoTTLean :
    sourceOrdinal SourceNode.HoTTLean = 1 := rfl

@[simp] theorem sourceOrdinal_TopcatModelCategory :
    sourceOrdinal SourceNode.TopcatModelCategory = 9 := rfl

@[simp] theorem structureOrdinal_TypeTheory :
    structureOrdinal StructureNode.TypeTheory = 1 := rfl

@[simp] theorem structureOrdinal_TopologicalCategory :
    structureOrdinal StructureNode.TopologicalCategory = 9 := rfl

@[simp] theorem edgeHolds_HoTTLean_presents_TypeTheory :
    edgeHolds SourceNode.HoTTLean BridgeEdge.presents StructureNode.TypeTheory = true := rfl

@[simp] theorem edgeHolds_LeanFibredCategories_presents_FibredCategory :
    edgeHolds SourceNode.LeanFibredCategories BridgeEdge.presents StructureNode.FibredCategory = true := rfl

@[simp] theorem edgeHolds_MathlibHomotopyEquiv_presents_HomotopyEquivalence :
    edgeHolds SourceNode.MathlibHomotopyEquiv BridgeEdge.presents StructureNode.HomotopyEquivalence = true := rfl

@[simp] theorem edgeHolds_Spectral_presents_ExactCouple :
    edgeHolds SourceNode.Spectral BridgeEdge.presents StructureNode.ExactCouple = true := rfl

@[simp] theorem edgeHolds_Spectral_presents_SerreSpectralSequence :
    edgeHolds SourceNode.Spectral BridgeEdge.presents StructureNode.SerreSpectralSequence = true := rfl

@[simp] theorem edgeHolds_InfinityCosmos_presents_InfinityCosmos :
    edgeHolds SourceNode.InfinityCosmos BridgeEdge.presents StructureNode.InfinityCosmos = true := rfl

@[simp] theorem edgeHolds_Quasicategory_presents_Quasicategory :
    edgeHolds SourceNode.Quasicategory BridgeEdge.presents StructureNode.Quasicategory = true := rfl

@[simp] theorem edgeHolds_TopcatModelCategory_presents_ModelCategory :
    edgeHolds SourceNode.TopcatModelCategory BridgeEdge.presents StructureNode.ModelCategory = true := rfl

@[simp] theorem homotopyEquivDataFields_eq : homotopyEquivDataFields = 4 := rfl

@[simp] theorem exactCoupleMapCount_eq : exactCoupleMapCount = 3 := rfl

@[simp] theorem serrePageStart_eq : serrePageStart = 2 := rfl

@[simp] theorem serreStablePage_eq : serreStablePage = 3 := rfl

@[simp] theorem quasicategorySimplexArity_eq : quasicategorySimplexArity = 2 := rfl

@[simp] theorem modelCategoryClassCount_eq : modelCategoryClassCount = 3 := rfl

@[simp] theorem fibredCategoryProjectionCount_eq : fibredCategoryProjectionCount = 1 := rfl

@[simp] theorem infinityBridgeSignature_eq : infinityBridgeSignature = 18 := by
  norm_num [infinityBridgeSignature, homotopyEquivDataFields, exactCoupleMapCount,
    serrePageStart, serreStablePage, quasicategorySimplexArity, modelCategoryClassCount,
    fibredCategoryProjectionCount]

@[simp] theorem d2Bidegree_zero_one :
    d2Bidegree 0 1 = (2, 0) := rfl

@[simp] theorem d2Bidegree_two_one :
    d2Bidegree 2 1 = (4, 0) := rfl

end HoTTInfinityBridge

end noncomputable section
