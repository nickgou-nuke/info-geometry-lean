Definition aeonCount := 3.
Definition thetaAeonIndex := 3.
Definition thetaSedimentDen := 1000.
Definition inverseThetaScale := 1000.
Definition su3Rank := 2.
Definition su3Roots := 6.
Definition su3Cartan := 2.
Definition su3Generators := 8.
Definition su3WeylOrder := 6.
Definition smRank := 4.
Definition smGenerators := 12.
Definition C2su3Fund_num := 4.
Definition C2su3Fund_den := 3.
Definition C2su3Adj := 3.
Definition topologicalChargePair := 0.
Definition pontryaginGenerators := 1.
Definition thetaIdealGenerators := 2.
Definition dmoduleCCRGenerators := 1.
Definition u1AxialAnomalyCoeff := 8.
Definition generationAnomaly := 0.
Definition d2TargetP := 2.
Definition d2TargetQ := 0.
Definition d2Square := 0.
Definition graphEdges := 5.

Theorem strong_cp_kernel :
  aeonCount = 3 /\ thetaAeonIndex = 3 /\ thetaSedimentDen = 1000 /\ inverseThetaScale = 1000 /\
  su3Rank = 2 /\ su3Roots = 6 /\ su3Cartan = 2 /\ su3Generators = 8 /\ su3WeylOrder = 6 /\
  smRank = 4 /\ smGenerators = 12 /\ C2su3Fund_num = 4 /\ C2su3Fund_den = 3 /\ C2su3Adj = 3 /\
  topologicalChargePair = 0 /\ pontryaginGenerators = 1 /\ thetaIdealGenerators = 2 /\ dmoduleCCRGenerators = 1 /\
  u1AxialAnomalyCoeff = 8 /\ generationAnomaly = 0 /\ d2TargetP = 2 /\ d2TargetQ = 0 /\ d2Square = 0 /\ graphEdges = 5.
Proof. repeat split; reflexivity. Qed.

Inductive Concept := Third_Aeon_Sediment | Theta_Vacuum | SU3_Color | CP_Twist | Axion_Counterterm | Strong_CP_Closure.
Inductive Edge := generates | carries | flips | cancels | closes.
Definition edgeHolds a e b :=
  match a,e,b with
  | Third_Aeon_Sediment, generates, Theta_Vacuum => true
  | Theta_Vacuum, carries, SU3_Color => true
  | CP_Twist, flips, Theta_Vacuum => true
  | Axion_Counterterm, cancels, Theta_Vacuum => true
  | Theta_Vacuum, closes, Strong_CP_Closure => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Third_Aeon_Sediment generates Theta_Vacuum = true /\
  edgeHolds Theta_Vacuum carries SU3_Color = true /\
  edgeHolds CP_Twist flips Theta_Vacuum = true /\
  edgeHolds Axion_Counterterm cancels Theta_Vacuum = true /\
  edgeHolds Theta_Vacuum closes Strong_CP_Closure = true.
Proof. repeat split; reflexivity. Qed.
