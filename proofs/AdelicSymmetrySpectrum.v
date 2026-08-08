Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Open Scope R_scope.

Section AdelicSymmetrySpectrum.

Variable V : Type.
Variable C : Type.
Variable fst : C -> R.
Variable snd : C -> R.
Variable Cplus : C -> C -> C.
Variable Cmult : C -> C -> C.
Variable Cconj : C -> C.
Variable zeroC : C.

Axiom Cplus_fst : forall c1 c2, fst (Cplus c1 c2) = (fst c1 + fst c2)%R.
Axiom Cplus_snd : forall c1 c2, snd (Cplus c1 c2) = (snd c1 + snd c2)%R.
Axiom Cmult_fst : forall c1 c2, fst (Cmult c1 c2) = (fst c1 * fst c2 - snd c1 * snd c2)%R.
Axiom Cmult_snd : forall c1 c2, snd (Cmult c1 c2) = (fst c1 * snd c2 + snd c1 * fst c2)%R.
Axiom Cconj_fst : forall c, fst (Cconj c) = fst c.
Axiom Cconj_snd : forall c, snd (Cconj c) = (- snd c)%R.

Variable inner : V -> V -> C.
Variable add : V -> V -> V.
Variable scale : C -> V -> V.

Variable D : V -> V.
Variable D_dag : V -> V.

Axiom inner_add_right : forall u v w, inner u (add v w) = Cplus (inner u v) (inner u w).
Axiom inner_scale_right : forall c u v, inner u (scale c v) = Cmult c (inner u v).
Axiom inner_symm : forall u v, inner u v = Cconj (inner v u).
Axiom D_adj_prop : forall u v, inner (D_dag u) v = inner u (D v).
Axiom D_identity : forall v, add (D v) (D_dag v) = v.

Variable v : V.
Variable lambda : C.
Axiom inner_v_v_neq_0 : fst (inner v v) <> 0%R \/ snd (inner v v) <> 0%R.
Axiom D_eigen : D v = scale lambda v.

Lemma inner_scale_left_fst : forall c x y, fst (inner (scale c x) y) = fst (Cmult (Cconj c) (inner x y)).
Proof.
  intros. rewrite inner_symm. rewrite inner_scale_right.
  rewrite Cconj_fst. rewrite Cmult_fst. rewrite Cmult_fst. rewrite Cconj_fst. rewrite Cconj_snd.
  set (A := fst c). set (B := fst (inner y x)). set (C1 := snd c). set (D1 := snd (inner y x)).
  nra.
Qed.

Lemma inner_scale_left_snd : forall c x y, snd (inner (scale c x) y) = snd (Cmult (Cconj c) (inner x y)).
Proof.
  intros. rewrite inner_symm. rewrite inner_scale_right.
  rewrite Cconj_snd. rewrite Cmult_snd. rewrite Cmult_snd. rewrite Cconj_fst. rewrite Cconj_snd.
  set (A := fst c). set (B := fst (inner y x)). set (C1 := snd c). set (D1 := snd (inner y x)).
  nra.
Qed.

Lemma spectrum_real_part : fst lambda = (1/2)%R.
Proof.
  assert (H1: inner v v = inner v (add (D v) (D_dag v))).
  { rewrite D_identity. reflexivity. }
  assert (H1_fst: fst (inner v v) = fst (inner v (add (D v) (D_dag v)))).
  { rewrite H1. reflexivity. }
  assert (H1_snd: snd (inner v v) = snd (inner v (add (D v) (D_dag v)))).
  { rewrite H1. reflexivity. }
  rewrite inner_add_right in H1_fst.
  rewrite inner_add_right in H1_snd.
  rewrite Cplus_fst in H1_fst.
  rewrite Cplus_snd in H1_snd.
  
  assert (H2: inner v (D v) = Cmult lambda (inner v v)).
  { rewrite D_eigen. rewrite inner_scale_right. reflexivity. }
  assert (H3_fst: fst (inner v (D_dag v)) = fst (Cmult (Cconj lambda) (inner v v))).
  { rewrite D_adj_prop. rewrite D_eigen. apply inner_scale_left_fst. }
  assert (H3_snd: snd (inner v (D_dag v)) = snd (Cmult (Cconj lambda) (inner v v))).
  { rewrite D_adj_prop. rewrite D_eigen. apply inner_scale_left_snd. }
  
  assert (H2_fst: fst (inner v (D v)) = fst (Cmult lambda (inner v v))).
  { rewrite H2. reflexivity. }
  assert (H2_snd: snd (inner v (D v)) = snd (Cmult lambda (inner v v))).
  { rewrite H2. reflexivity. }
  
  rewrite H2_fst in H1_fst.
  rewrite H2_snd in H1_snd.
  rewrite H3_fst in H1_fst.
  rewrite H3_snd in H1_snd.
  
  rewrite Cmult_fst in H1_fst.
  rewrite Cmult_fst in H1_fst.
  rewrite Cconj_fst in H1_fst.
  rewrite Cconj_snd in H1_fst.
  
  rewrite Cmult_snd in H1_snd.
  rewrite Cmult_snd in H1_snd.
  rewrite Cconj_fst in H1_snd.
  rewrite Cconj_snd in H1_snd.
  
  set (L := fst lambda) in *. set (M := snd lambda) in *.
  set (X := fst (inner v v)) in *. set (Y := snd (inner v v)) in *.
  
  assert (H_fst: X = (2 * L * X)%R).
  { nra. }
  assert (H_snd: Y = (2 * L * Y)%R).
  { nra. }
  
  assert (H_fst2: ((1 - 2 * L) * X = 0)%R).
  { nra. }
  assert (H_snd2: ((1 - 2 * L) * Y = 0)%R).
  { nra. }
  
  destruct inner_v_v_neq_0.
  - apply Rmult_integral in H_fst2. destruct H_fst2.
    + nra.
    + contradiction.
  - apply Rmult_integral in H_snd2. destruct H_snd2.
    + nra.
    + contradiction.
Qed.

End AdelicSymmetrySpectrum.
