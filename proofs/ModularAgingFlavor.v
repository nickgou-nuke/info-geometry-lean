Definition aeonCount := 3.
Definition generationCount := 3.
Definition vintageCount := 3.
Definition stablePage := 3.
Definition serreResidueRank := 8.
Definition aeonColimitRank := 24.
Definition threeGenerationWeylCount := 48.
Definition su3Generators := 8.
Definition su2Generators := 3.
Definition smRank := 4.
Definition smGenerators := 12.
Definition cartanGenerators := 4.
Definition C2su3Fund_num := 4.
Definition C2su3Fund_den := 3.
Definition C2su2Doublet_num := 3.
Definition C2su2Doublet_den := 4.
Definition aging1_den := 10.
Definition aging2_den := 100.
Definition aging3_den := 1000.
Definition massRatioG2G1 := 10.
Definition massRatioG3G2 := 10.
Definition massRatioG3G1 := 100.
Definition ckmParameters := 4.
Definition ckmEntries := 9.
Definition colorAnomaly := 0.
Definition weakAnomaly := 0.
Definition generationAnomaly := 0.
Definition d2TargetP := 2.
Definition d2TargetQ := 0.
Definition d2Square := 0.
Definition graphEdges := 5.

Theorem modular_aging_flavor_kernel :
  aeonCount = 3 /\ generationCount = 3 /\ vintageCount = 3 /\ stablePage = 3 /\ serreResidueRank = 8 /\ aeonColimitRank = 24 /\ threeGenerationWeylCount = 48 /\
  su3Generators = 8 /\ su2Generators = 3 /\ smRank = 4 /\ smGenerators = 12 /\ cartanGenerators = 4 /\
  C2su3Fund_num = 4 /\ C2su3Fund_den = 3 /\ C2su2Doublet_num = 3 /\ C2su2Doublet_den = 4 /\
  aging1_den = 10 /\ aging2_den = 100 /\ aging3_den = 1000 /\ massRatioG2G1 = 10 /\ massRatioG3G2 = 10 /\ massRatioG3G1 = 100 /\
  ckmParameters = 4 /\ ckmEntries = 9 /\ colorAnomaly = 0 /\ weakAnomaly = 0 /\ generationAnomaly = 0 /\
  d2TargetP = 2 /\ d2TargetQ = 0 /\ d2Square = 0 /\ graphEdges = 5.
Proof. repeat split; reflexivity. Qed.

Inductive Concept := Modular_Aging_Operator | Aeon_Colimit | Generation_Flavor | CKM_Matrix | SM_Symmetry | Anomaly_Cancelled.
Inductive Edge := iterates | refines | generates | carries | cancels.
Definition edgeHolds a e b :=
  match a,e,b with
  | Modular_Aging_Operator, iterates, Aeon_Colimit => true
  | Aeon_Colimit, refines, Generation_Flavor => true
  | Generation_Flavor, generates, CKM_Matrix => true
  | Generation_Flavor, carries, SM_Symmetry => true
  | SM_Symmetry, cancels, Anomaly_Cancelled => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Modular_Aging_Operator iterates Aeon_Colimit = true /\
  edgeHolds Aeon_Colimit refines Generation_Flavor = true /\
  edgeHolds Generation_Flavor generates CKM_Matrix = true /\
  edgeHolds Generation_Flavor carries SM_Symmetry = true /\
  edgeHolds SM_Symmetry cancels Anomaly_Cancelled = true.
Proof. repeat split; reflexivity. Qed.
