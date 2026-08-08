Require Import Reals.

Record PhaseSpace : Type := mkPhaseSpace {
  q_pos : R;
  p_mom : R
}.

Definition WignerDistribution := PhaseSpace -> R.

Definition star_product (f g : WignerDistribution) : WignerDistribution :=
  fun ps => Rmult (f ps) (g ps).

Theorem star_product_commutative_trivial : forall f g ps,
  star_product f g ps = star_product g f ps.
Proof.
  intros.
  unfold star_product.
  apply Rmult_comm.
Qed.
