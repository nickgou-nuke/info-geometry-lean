Definition A := 88.
Definition Z := 44.
Definition N := 44.
Definition twoTz := N - Z.
Definition su2SpinGenerators := 3.
Definition su2IsospinGenerators := 3.
Definition cartanGenerators := 2.
Definition totalGenerators := su2SpinGenerators + su2IsospinGenerators.
Definition spinC2I14 := 14*15.
Definition isospinC2T1 := 1*2.
Definition isovectorPairT := 1.
Definition isovectorPairI := 0.
Definition isoscalarPairT := 0.
Definition isoscalarPairImin := 1.
Definition isovectorMultiplicity := 3.
Definition isoscalarMultiplicity := 3.
Definition bandLength := 8.
Definition gammaSum := 1063+1153+1253.
Definition omegaNormalNum := 47.
Definition omegaRuNum := 54.
Definition omegaDelayNum := omegaRuNum - omegaNormalNum.
Definition fpgdDegeneracy := 2+4+6+10+6.
Definition fpgdPN := 2*fpgdDegeneracy.
Definition reactionA := 36+54-2.
Definition reactionZ := 18+26.
Definition hamiltonianTerms := 4.
Definition graphEdges := 6.

Theorem prl124_ru_pairing_kernel :
  A = 88 /\ Z = 44 /\ N = 44 /\ twoTz = 0 /\
  su2SpinGenerators = 3 /\ su2IsospinGenerators = 3 /\ cartanGenerators = 2 /\ totalGenerators = 6 /\
  spinC2I14 = 210 /\ isospinC2T1 = 2 /\
  isovectorPairT = 1 /\ isovectorPairI = 0 /\ isoscalarPairT = 0 /\ isoscalarPairImin = 1 /\
  isovectorMultiplicity = 3 /\ isoscalarMultiplicity = 3 /\ bandLength = 8 /\ gammaSum = 3469 /\
  omegaDelayNum = 7 /\ fpgdDegeneracy = 28 /\ fpgdPN = 56 /\ reactionA = 88 /\ reactionZ = 44 /\
  hamiltonianTerms = 4 /\ graphEdges = 6.
Proof. repeat split; reflexivity. Qed.

Inductive Concept := Ru88_NeqZ | SU2_Spin | SU2_Isospin | Isovector_T1_I0_Pair | Isoscalar_T0_Igt0_Pair | Delayed_Rotational_Alignment | FPGD_Model_Space.
Inductive Edge := has_symmetry | carries_pair | witnesses | uses_space.
Definition edgeHolds a e b :=
  match a,e,b with
  | Ru88_NeqZ, has_symmetry, SU2_Spin => true
  | Ru88_NeqZ, has_symmetry, SU2_Isospin => true
  | Ru88_NeqZ, carries_pair, Isovector_T1_I0_Pair => true
  | Ru88_NeqZ, carries_pair, Isoscalar_T0_Igt0_Pair => true
  | Isoscalar_T0_Igt0_Pair, witnesses, Delayed_Rotational_Alignment => true
  | Ru88_NeqZ, uses_space, FPGD_Model_Space => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds Ru88_NeqZ has_symmetry SU2_Spin = true /\
  edgeHolds Ru88_NeqZ has_symmetry SU2_Isospin = true /\
  edgeHolds Ru88_NeqZ carries_pair Isovector_T1_I0_Pair = true /\
  edgeHolds Ru88_NeqZ carries_pair Isoscalar_T0_Igt0_Pair = true /\
  edgeHolds Isoscalar_T0_Igt0_Pair witnesses Delayed_Rotational_Alignment = true /\
  edgeHolds Ru88_NeqZ uses_space FPGD_Model_Space = true.
Proof. repeat split; reflexivity. Qed.
