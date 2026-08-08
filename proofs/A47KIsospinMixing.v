From Stdlib Require Import QArith List String.
Import ListNotations.
Open Scope Q_scope.
Open Scope string_scope.

Definition yWeighted : Q := -12 / 125.
Definition yWeightedSigma : Q := 37 / 1000.
Definition yRecoil : Q := -51 / 500.
Definition yRecoilSigma : Q := 41 / 1000.
Definition coulombObserved : Q := 90.
Definition sigmaObserved : Q := 35.
Definition coulombWeighted : Q := 72.
Definition sigmaWeighted : Q := 26.
Definition coulombPredicted : Q := 190.
Definition branchHalfToHalf : Q := 4/5.
Definition branchThreeHalfKnown : Q := 19/100.
Definition branchThreeHalfOther : Q := 1/100.
Definition branchThreeHalfTotal : Q := branchThreeHalfKnown + branchThreeHalfOther.
Definition A_beta_GT_half_to_half : Q := -2/3.
Definition A_beta_GT_half_to_threehalf : Q := 1/3.
Definition weightedPureGTAsymmetry : Q := branchHalfToHalf*A_beta_GT_half_to_half + branchThreeHalfTotal*A_beta_GT_half_to_threehalf.
Definition qabs (x:Q) : Q := if Qlt_le_dec x 0 then -x else x.
Definition significance (x sigma:Q) : Q := qabs x / sigma.
Definition relativeToPrediction (o p:Q) : Q := o/p.
Definition deficit (o p:Q) : Q := 1-o/p.

Theorem a47k_isospin_mixing_kernel :
  yWeighted == -12/125 /\ yWeightedSigma == 37/1000 /\
  yRecoil == -51/500 /\ yRecoilSigma == 41/1000 /\
  significance yWeighted yWeightedSigma == 96/37 /\
  significance yRecoil yRecoilSigma == 102/41 /\
  coulombObserved - sigmaObserved == 55 /\ coulombObserved + sigmaObserved == 125 /\
  coulombWeighted - sigmaWeighted == 46 /\ coulombWeighted + sigmaWeighted == 98 /\
  relativeToPrediction coulombObserved coulombPredicted == 9/19 /\
  relativeToPrediction coulombWeighted coulombPredicted == 36/95 /\
  deficit coulombObserved coulombPredicted == 10/19 /\
  deficit coulombWeighted coulombPredicted == 59/95 /\
  branchHalfToHalf + branchThreeHalfKnown + branchThreeHalfOther == 1 /\
  branchThreeHalfTotal == 1/5 /\
  weightedPureGTAsymmetry == -7/15.
Proof. repeat split; vm_compute; reflexivity. Qed.

Inductive Concept := A47K_BetaDecay | A47Ca_IsospinMixedState | Fermi_GT_Interference | Analog_Antianalog_Mixing | Coulomb_Mixing_MatrixElement | TOPE_Isovector_Search_Channel.
Inductive Edge := decays_to | measures | implies | compares_with | motivates.
Definition edgeHolds a e b :=
  match a,e,b with
  | A47K_BetaDecay, decays_to, A47Ca_IsospinMixedState => true
  | A47K_BetaDecay, measures, Fermi_GT_Interference => true
  | Fermi_GT_Interference, implies, Coulomb_Mixing_MatrixElement => true
  | Coulomb_Mixing_MatrixElement, compares_with, Analog_Antianalog_Mixing => true
  | Analog_Antianalog_Mixing, motivates, TOPE_Isovector_Search_Channel => true
  | _,_,_ => false
  end.

Theorem graph_kernel :
  edgeHolds A47K_BetaDecay decays_to A47Ca_IsospinMixedState = true /\
  edgeHolds A47K_BetaDecay measures Fermi_GT_Interference = true /\
  edgeHolds Fermi_GT_Interference implies Coulomb_Mixing_MatrixElement = true /\
  edgeHolds Coulomb_Mixing_MatrixElement compares_with Analog_Antianalog_Mixing = true /\
  edgeHolds Analog_Antianalog_Mixing motivates TOPE_Isovector_Search_Channel = true.
Proof. compute; repeat split; reflexivity. Qed.
