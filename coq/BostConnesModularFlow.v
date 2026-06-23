From Coq Require Import Reals.

Open Scope R_scope.

Section BostConnes.

Variable Op : Type.
Variable smul : R -> Op -> Op.
Variable generator : Op.

Variable t_flow : R.
Variable grading : R.

Variable σ_t : Op -> Op.
Variable Γ : Op -> Op.

Hypothesis σ_t_smul : forall r x, σ_t (smul r x) = smul r (σ_t x).
Hypothesis Γ_smul : forall r x, Γ (smul r x) = smul r (Γ x).

Hypothesis σ_t_gen : σ_t generator = smul t_flow generator.
Hypothesis Γ_gen : Γ generator = smul grading generator.

Hypothesis smul_assoc : forall a b x, smul a (smul b x) = smul (a * b) x.

Theorem witten_index_conserved :
  Γ (σ_t generator) = σ_t (Γ generator).
Proof.
  rewrite σ_t_gen.
  rewrite Γ_smul.
  rewrite Γ_gen.
  rewrite smul_assoc.
  rewrite (Rmult_comm t_flow grading).
  rewrite <- smul_assoc.
  rewrite <- σ_t_gen.
  rewrite <- σ_t_smul.
  rewrite <- Γ_gen.
  reflexivity.
Qed.

End BostConnes.
