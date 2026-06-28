Require Import Reals. Require Import Ring. Open Scope R_scope. Lemma test : True -> True. Proof. intro h. have h2 : True by tauto. exact h2. Qed.
