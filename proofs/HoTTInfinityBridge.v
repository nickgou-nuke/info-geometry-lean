Definition repositorySourceCount := 8.
Definition mathlibSourceCount := 1.
Definition totalSourceCount := 9.
Definition bridgeLayerCount := 9.
Definition compatibilityEdgeCount := 11.
Definition hottBridgeRank := 29.
Definition homotopyEquivFields := 4.
Definition exactCoupleMaps := 3.
Definition serrePageStart := 2.
Definition serreStablePage := 3.
Definition quasicategorySimplexArity := 2.
Definition modelCategoryClasses := 3.
Definition fibredProjectionCount := 1.
Definition infinityBridgeSignature := 18.
Definition d2TargetP := 2.
Definition d2TargetQ := 0.
Definition d2Square := 0.

Theorem hott_infinity_bridge_kernel :
  repositorySourceCount = 8 /\ mathlibSourceCount = 1 /\ totalSourceCount = 9 /\ bridgeLayerCount = 9 /\
  compatibilityEdgeCount = 11 /\ hottBridgeRank = 29 /\ homotopyEquivFields = 4 /\ exactCoupleMaps = 3 /\
  serrePageStart = 2 /\ serreStablePage = 3 /\ quasicategorySimplexArity = 2 /\ modelCategoryClasses = 3 /\
  fibredProjectionCount = 1 /\ infinityBridgeSignature = 18 /\ d2TargetP = 2 /\ d2TargetQ = 0 /\ d2Square = 0.
Proof. repeat split; reflexivity. Qed.

Inductive SourceNode := HoTTLean | GroundZero | LeanFibredCategories | MathlibHomotopyEquiv | Hott3 | Spectral | InfinityCosmos | Quasicategory | TopcatModelCategory.
Inductive StructureNode := TypeTheory | HomotopyEquivalence | FibredCategory | ExactCouple | SerreSpectralSequence | InfinityCosmosS | QuasicategoryS | ModelCategory | TopologicalCategory.
Inductive BridgeEdge := presents | imports | refines | supports | compares | localizes.
Definition edgeHolds a e b :=
  match a,e,b with
  | HoTTLean, presents, TypeTheory => true
  | GroundZero, presents, TypeTheory => true
  | LeanFibredCategories, presents, FibredCategory => true
  | MathlibHomotopyEquiv, presents, HomotopyEquivalence => true
  | Hott3, refines, TypeTheory => true
  | Spectral, presents, ExactCouple => true
  | Spectral, presents, SerreSpectralSequence => true
  | InfinityCosmos, presents, InfinityCosmosS => true
  | Quasicategory, presents, QuasicategoryS => true
  | TopcatModelCategory, presents, ModelCategory => true
  | TopcatModelCategory, supports, TopologicalCategory => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds HoTTLean presents TypeTheory = true /\
  edgeHolds LeanFibredCategories presents FibredCategory = true /\
  edgeHolds MathlibHomotopyEquiv presents HomotopyEquivalence = true /\
  edgeHolds Spectral presents SerreSpectralSequence = true /\
  edgeHolds Quasicategory presents QuasicategoryS = true /\
  edgeHolds TopcatModelCategory presents ModelCategory = true.
Proof. repeat split; reflexivity. Qed.
