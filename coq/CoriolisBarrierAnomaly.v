Require Import Reals.

Local Open Scope R_scope.

(* The Itakura-Saito barrier kernel *)
Definition isBarrierKernel (x : R) : R :=
  x - ln x - 1.

(* First derivative of the barrier *)
Definition isBarrierKernel_deriv (x : R) : R :=
  1 - 1 / x.

(* Second derivative of the barrier *)
Definition isBarrierKernel_deriv2 (x : R) : R :=
  1 / (x ^ 2).

(* Third derivative of the barrier *)
Definition isBarrierKernel_deriv3 (x : R) : R :=
  -2 / (x ^ 3).

(* Singular Drazin and Moore-Penrose projections structure *)
Record SingularProjections : Type := {
  PD : R; (* Drazin spectral projector *)
  PL : R; (* Moore-Penrose left projector *)
  PR : R; (* Moore-Penrose right projector *)
  D : R;  (* Dilation operator *)
  chi_L : R; (* Left chiral anomaly commutator *)
  chi_R : R; (* Right chiral anomaly commutator *)
  
  dilation_def : D = (PL - PR) / 2;
  chi_L_def : chi_L = PD * PL - PL * PD;
  chi_R_def : chi_R = PD * PR - PR * PD;
}.

(* Theorem: Dilation commutator decomposition.
   [P_D, D] = 1/2 * (chi_L - chi_R) holds algebraically by ring properties. *)
Theorem dilation_commutator_decomposition (S : SingularProjections) :
  PD S * D S - D S * PD S = (chi_L S - chi_R S) / 2.
Proof.
  destruct S.
  subst.
  ring.
Qed.
