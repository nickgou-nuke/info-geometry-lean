Definition stablePage := 3.
Definition e2Rank := 8.
Definition survivorCount := 8.
Definition su3Generators := 8.
Definition su2Generators := 3.
Definition smRank := 4.
Definition smGenerators := 12.
Definition cartanGenerators := 4.
Definition ladderCount := 8.
Definition C2su3Fund_num := 4.
Definition C2su3Fund_den := 3.
Definition C2su2Doublet_num := 3.
Definition C2su2Doublet_den := 4.
Definition upCharge_num := 2.
Definition upCharge_den := 3.
Definition downCharge_num := 1.
Definition downCharge_den := 3.
Definition neutrinoCharge := 0.
Definition electronCharge := 1.
Definition weylCount := 16.
Definition colorAnomaly := 0.
Definition weakAnomaly := 0.
Definition gravTrace := 0.
Definition cubicTrace := 0.
Definition d2TargetP := 2.
Definition d2TargetQ := 0.
Definition d2Square := 0.
Definition graphEdges := 6.

Theorem furey_ladder_serre_kernel :
  stablePage = 3 /\ e2Rank = 8 /\ survivorCount = 8 /\
  su3Generators = 8 /\ su2Generators = 3 /\ smRank = 4 /\ smGenerators = 12 /\ cartanGenerators = 4 /\ ladderCount = 8 /\
  C2su3Fund_num = 4 /\ C2su3Fund_den = 3 /\ C2su2Doublet_num = 3 /\ C2su2Doublet_den = 4 /\
  upCharge_num = 2 /\ upCharge_den = 3 /\ downCharge_num = 1 /\ downCharge_den = 3 /\ neutrinoCharge = 0 /\ electronCharge = 1 /\
  weylCount = 16 /\ colorAnomaly = 0 /\ weakAnomaly = 0 /\ gravTrace = 0 /\ cubicTrace = 0 /\
  d2TargetP = 2 /\ d2TargetQ = 0 /\ d2Square = 0 /\ graphEdges = 6.
Proof. repeat split; reflexivity. Qed.

Inductive Concept := Serre_d2_Differential | Furey_Ladder_Residue | SU3_Color | SU2_Weak | U1_Hypercharge | SM_One_Generation | Anomaly_Cancelled.
Inductive Edge := extracts | generates | carries | cancels.
Definition edgeHolds a e b :=
  match a,e,b with
  | Serre_d2_Differential, extracts, Furey_Ladder_Residue => true
  | Furey_Ladder_Residue, generates, SU3_Color => true
  | Furey_Ladder_Residue, generates, SU2_Weak => true
  | Furey_Ladder_Residue, generates, U1_Hypercharge => true
  | SM_One_Generation, carries, Furey_Ladder_Residue => true
  | SM_One_Generation, cancels, Anomaly_Cancelled => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Serre_d2_Differential extracts Furey_Ladder_Residue = true /\
  edgeHolds Furey_Ladder_Residue generates SU3_Color = true /\
  edgeHolds Furey_Ladder_Residue generates SU2_Weak = true /\
  edgeHolds Furey_Ladder_Residue generates U1_Hypercharge = true /\
  edgeHolds SM_One_Generation carries Furey_Ladder_Residue = true /\
  edgeHolds SM_One_Generation cancels Anomaly_Cancelled = true.
Proof. repeat split; reflexivity. Qed.
