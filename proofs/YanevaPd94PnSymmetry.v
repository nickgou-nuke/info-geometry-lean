From Stdlib Require Import Arith Lia Lra QArith ZArith.

Open Scope nat_scope.
Open Scope Q_scope.

Definition ZPd94 : nat := 46.
Definition NPd94 : nat := 48.
Definition APd94 : nat := 94.
Definition protonHoles : nat := 50 - ZPd94.
Definition neutronHoles : nat := 50 - NPd94.
Definition totalHoles : nat := protonHoles + neutronHoles.
Definition Tz (N Z : Q) : Q := (N - Z) / 2.
Definition doubledTz (N Z0 : Z) : Z := (N - Z0)%Z.
Definition inIsospinMultiplet (T : nat) (twoTz : Z) : Prop :=
  (Z.abs twoTz <= Z.of_nat (2 * T))%Z.
Definition g92Degeneracy : nat := 10.
Definition singleJConfigCount : nat := 9450.
Definition isospinIrrepDim (T : nat) : nat := 2 * T + 1.
Definition yrast8B : Q := 205.
Definition yrast8BLower : Q := 205 - 25.
Definition yrast8BUpper : Q := 205 + 34.
Definition gdsNeutronCharge : Q := 84 / 100.
Definition yrast8Bgds : Q := 192.
Definition g9full8 : Q := 144.
Definition g9t0_8 : Q := 191.
Definition g9t1_8 : Q := 11.

Lemma pd94_arithmetic_kernel :
  (ZPd94 + NPd94)%nat = APd94 /\
  NPd94 = (ZPd94 + 2)%nat /\
  Tz 48 46 == 1 /\
  protonHoles = 4%nat /\
  neutronHoles = 2%nat /\
  totalHoles = 6%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma isospin_membership_kernel :
  doubledTz 48 46 = 2%Z /\
  doubledTz 47 47 = 0%Z /\
  inIsospinMultiplet 1%nat (doubledTz 48 46) /\
  inIsospinMultiplet 1%nat (doubledTz 47 47).
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split.
  - unfold inIsospinMultiplet, doubledTz. change (2 <= 2)%Z. lia.
  - unfold inIsospinMultiplet, doubledTz. change (0 <= 2)%Z. lia.
Qed.

Lemma shell_pair_kernel :
  g92Degeneracy = 10%nat /\
  singleJConfigCount = 9450%nat /\
  isospinIrrepDim 0%nat = 1%nat /\
  isospinIrrepDim 1%nat = 3%nat.
Proof.
  repeat split; vm_compute; reflexivity.
Qed.

Lemma e2_table_kernel :
  8%nat = (6 + 2)%nat /\
  6%nat = (4 + 2)%nat /\
  14%nat = (12 + 2)%nat /\
  yrast8B == 205 /\
  yrast8BLower == 180 /\
  yrast8BUpper == 239 /\
  yrast8B < 250 /\
  gdsNeutronCharge == 21 / 25.
Proof.
  repeat split; vm_compute; try reflexivity.
Qed.

Lemma table1_model_kernel :
  yrast8BLower <= yrast8Bgds /\
  yrast8Bgds <= yrast8BUpper /\
  g9t0_8 - g9full8 < g9full8 - g9t1_8.
Proof.
  split.
  - apply Qle_bool_imp_le. vm_compute. reflexivity.
  - split.
    + apply Qle_bool_imp_le. vm_compute. reflexivity.
    + apply Qlt_alt. vm_compute. reflexivity.
Qed.

Lemma yaneva_pd94_pn_symmetry_kernel :
  (ZPd94 + NPd94)%nat = APd94 /\
  Tz 48 46 == 1 /\
  protonHoles = 4%nat /\
  neutronHoles = 2%nat /\
  totalHoles = 6%nat /\
  inIsospinMultiplet 1%nat (doubledTz 48 46) /\
  g92Degeneracy = 10%nat /\
  singleJConfigCount = 9450%nat /\
  isospinIrrepDim 0%nat = 1%nat /\
  isospinIrrepDim 1%nat = 3%nat /\
  yrast8B == 205 /\
  gdsNeutronCharge == 21 / 25 /\
  yrast8BLower <= yrast8Bgds /\
  yrast8Bgds <= yrast8BUpper /\
  g9t0_8 - g9full8 < g9full8 - g9t1_8.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split.
  - unfold inIsospinMultiplet, doubledTz. change (2 <= 2)%Z. lia.
  - split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    split; [vm_compute; reflexivity|].
    exact table1_model_kernel.
Qed.
