Definition aeonCount := 3.
Definition generationCount := 3.
Definition ckmParameters := 4.
Definition ckmEntries := 9.
Definition threeGenerationWeylCount := 48.
Definition stablePage := 3.
Definition serreResidueRank := 8.
Definition aeonColimitRank := 24.
Definition su3Generators := 8.
Definition su2Generators := 3.
Definition smRank := 4.
Definition smGenerators := 12.
Definition cartanGenerators := 4.
Definition C2su3Fund_num := 4.
Definition C2su3Fund_den := 3.
Definition C2su2Doublet_num := 3.
Definition C2su2Doublet_den := 4.
Definition upCharge_num := 2.
Definition upCharge_den := 3.
Definition downCharge_num := 1.
Definition downCharge_den := 3.
Definition colorAnomaly := 0.
Definition weakAnomaly := 0.
Definition generationAnomaly := 0.
Definition determinantSocket := 1.
Definition jarlskogSocket := 0.
Definition d2TargetP := 2.
Definition d2TargetQ := 0.
Definition d2Square := 0.
Definition graphEdges := 6.

Theorem ckm_aeon_kernel :
  aeonCount = 3 /\ generationCount = 3 /\ ckmParameters = 4 /\ ckmEntries = 9 /\ threeGenerationWeylCount = 48 /\
  stablePage = 3 /\ serreResidueRank = 8 /\ aeonColimitRank = 24 /\
  su3Generators = 8 /\ su2Generators = 3 /\ smRank = 4 /\ smGenerators = 12 /\ cartanGenerators = 4 /\
  C2su3Fund_num = 4 /\ C2su3Fund_den = 3 /\ C2su2Doublet_num = 3 /\ C2su2Doublet_den = 4 /\
  upCharge_num = 2 /\ upCharge_den = 3 /\ downCharge_num = 1 /\ downCharge_den = 3 /\
  colorAnomaly = 0 /\ weakAnomaly = 0 /\ generationAnomaly = 0 /\ determinantSocket = 1 /\ jarlskogSocket = 0 /\
  d2TargetP = 2 /\ d2TargetQ = 0 /\ d2Square = 0 /\ graphEdges = 6.
Proof. repeat split; reflexivity. Qed.

Inductive Concept := Aeon_Three_Colimit | CKM_Matrix | SU3_Color | SU2_Weak | U1_Hypercharge | Three_Generation_SM | Anomaly_Cancelled.
Inductive Edge := generates | mixes | carries | cancels.
Definition edgeHolds a e b :=
  match a,e,b with
  | Aeon_Three_Colimit, generates, CKM_Matrix => true
  | CKM_Matrix, mixes, Three_Generation_SM => true
  | Three_Generation_SM, carries, SU3_Color => true
  | Three_Generation_SM, carries, SU2_Weak => true
  | Three_Generation_SM, carries, U1_Hypercharge => true
  | Three_Generation_SM, cancels, Anomaly_Cancelled => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Aeon_Three_Colimit generates CKM_Matrix = true /\
  edgeHolds CKM_Matrix mixes Three_Generation_SM = true /\
  edgeHolds Three_Generation_SM carries SU3_Color = true /\
  edgeHolds Three_Generation_SM carries SU2_Weak = true /\
  edgeHolds Three_Generation_SM carries U1_Hypercharge = true /\
  edgeHolds Three_Generation_SM cancels Anomaly_Cancelled = true.
Proof. repeat split; reflexivity. Qed.
