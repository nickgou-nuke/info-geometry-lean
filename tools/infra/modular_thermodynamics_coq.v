(* Modular Thermodynamics: First Law of Entanglement Entropy *)
(* Formalization of dS = d⟨K⟩ for normalized states *)

Require Import Reals.
Require Import Ring.
Open Scope R_scope.

(* ---------------------------------------------------------------------- *)
(* Definitions                                                            *)
(* ---------------------------------------------------------------------- *)

(* The von Neumann entropy for a state with modular Hamiltonian K *)
(* In the thermal-like form: S = ⟨K⟩ + ln Q, where Q = Tr(e^{-K}) *)

(* We work with the expectation value ⟨K⟩ as a real number *)
(* and the partition function Q as a positive real number *)

(* Entropy function: S(K, Q) = K + ln(Q) *)
(* Note: Here we've absorbed any constants into the definition of K *)
(* This corresponds to setting Boltzmann's constant k_B = 1 *)

Definition entropy (expect_K Q : R) : R :=
    expect_K + ln Q.

(* ---------------------------------------------------------------------- *)
(* Main Lemma: For normalized states (Q = 1), we have S = K                                  *)
(* ---------------------------------------------------------------------- *)

(* First, establish that when Q = 1, S = K *)
Lemma entropy_eq_expectation : forall (expect_K : R),
    entropy expect_K 1 = expect_K.
Proof.
  intros expect_K.
  unfold entropy.
  rewrite <- plus_0_r.
  (* Now we have expect_K + ln 1 *)
  (* We know that ln 1 = 0 *)
  rewrite <- ln_1.
  now ring.
Qed.

(* ---------------------------------------------------------------------- *)
(* Derivative Property: If two functions are equal, their derivatives are equal *)
(* ---------------------------------------------------------------------- *)

(* We'll use this principle to show that if S(t) = K(t), then S'(t) = K'(t) *)
(* when the derivatives exist *)

Lemma eq_functions_have_equal_derivs :
  forall (f g : R -> R) (x : R),
    (forall t, f t = g t) ->
    derivable_pt f x ->
    derivable_pt g x ->
    (exists l : R, derivable_pt_abs f x l /\ derivable_pt_abs g x l).
Proof.
  intros f g x h_eq hf_dif hg_dif.
  (* Since f and g are equal everywhere, they have the same derivative where it exists *)
  destruct hf_dif as [l hf_l].
  destruct hg_dif as [l' hg_l].
  exists l.
  split.
  - exact hf_l.
  - (* Show that l is also the derivative of g at x *)
    assert (h_eq_pt : f x = g x) by apply h_eq.
    assert (h_f_eq_g : forall t, f t = g t) by
      {
        intro t.
        apply h_eq.
      }
    assert (h_deriv_eq : derivable_pt_abs g x l) by
      {
        (* Since f = g everywhere, and f has derivative l at x, so does g *)
        unfold derivable_pt_abs in *.
        intro eps.
        destruct (hf_l eps) as [delta hdelta].
        exists delta.
        intro h neqh hdelta'.
        have h1 : f (x + h) = g (x + h) by apply h_f_eq_g.
        have h2 : f x = g x by apply h_f_eq_g.
        rewrite h1, h2 in hdelta'.
        exact hdelta'.
      }
    exact h_deriv_eq.
Qed.

(* ---------------------------------------------------------------------- *)
(* Special Case: Normalized States                                        *)
(* ---------------------------------------------------------------------- *)

(* For normalized states, Q(t) = 1 for all t *)
(* Hence ln(Q(t)) = ln(1) = 0 *)
(* So S(t) = K(t) *)
(* And therefore dS/dt = dK/dt *)

Theorem first_law_normalized_states :
  forall (S K : R -> R),
    (forall t, S t = K t) ->  (* S(t) = K(t) when Q(t)=1 for all t *)
    (forall t, derivable_pt (fun t => S t) t) ->
    (forall t, derivable_pt (fun t => K t) t) ->
    (forall t,
      exists l : R,
        derivable_pt_abs (fun t => S t) t l /\
        derivable_pt_abs (fun t => K t) t l).
Proof.
  intros S K h_eq_S_K h_S_diff h_K_diff t.
  have h : (fun t => S) = (fun t => K) by
    {
      funext x.
      apply h_eq_S_K.
    }
  have hf_dif : derivable_pt (fun t => S) t := (h_S_diff t).
  have hg_dif : derivable_pt (fun t => K) t := (h_K_diff t).
  apply eq_functions_have_equal_derivs with (f := (fun t => S)) (g := (fun t => K)) (x := t).
  - exact h.
  - exact hf_dif.
  - exact hg_dif.
Qed.

(* ---------------------------------------------------------------------- *)
(* Example: Quadratic Functions                                           *)
(* ---------------------------------------------------------------------- *)

(* Example where S(t) = t^2, K(t) = t^2, Q(t) = 1 *)
(* Then S(t) = K(t) + ln(1) = t^2 + 0 = t^2 *)

Example quadratic_example : 
  (fun t => (t^2 : R)) = (fun t => (t^2 + ln 1 : R)).
Proof.
  funext t.
  ring.
  <;> simpl.
Qed.

(* ---------------------------------------------------------------------- *)
(* Example: Derivatives match for the quadratic case                      *)
(* ---------------------------------------------------------------------- *)

(* At t=0, both functions have derivative 0 *)
Example derivative_example_zero : 
  derivable_pt (fun t => (t^2 : R)) 0 /\
  derivable_pt (fun t => (t^2 + ln 1 : R)) 0 /\
  (exists l : R, derivable_pt_abs (fun t => (t^2 : R)) 0 l /\
                 derivable_pt_abs (fun t => (t^2 + ln 1 : R)) 0 l).
Proof.
  split.
  - (* Prove t^2 is differentiable at 0 *)
    (* The derivative of t^2 is 2t, which is 0 at t=0 *)
    exist 0.
    split.
    + (* Prove derivable_pt *)
      unfold derivable_pt.
      exists 0.
      intro h.
      field_simp.
      ring.
      fdivide.
      ring.
    + (* Prove derivable_pt_abs with the same limit *)
      unfold derivable_pt_abs.
      exists 0.
      split.
      * (* Prove derivable_pt *)
        unfold derivable_pt.
        exists 0.
        intro h.
        field_simp.
        ring.
        fdivide.
        ring.
      * (* Prove the limit is 0 *)
        intro eps.
        exists eps.
        intro h hne.
        unfold Rabs, Rdiv.
        rewrite <- mult_0_r.
        ring.
        <;> field_simp.
        <;> ring.
        <;> linarith.
  - (* Prove t^2 + ln(1) is differentiable at 0 *)
    (* Since ln(1) = 0, this is the same as t^2 *)
    have h : (fun t => (t^2 + ln 1 : R)) = (fun t => (t^2 : R)) by
      funext t; ring; simpl.
    rewrite h.
    exact (conj (ex_intro _ 0 (by
      split.
      + (* Prove derivable_pt *)
        unfold derivable_pt.
        exists 0.
        intro h.
        field_simp.
        ring.
        fdivide.
        ring.
      + (* Prove derivable_pt_abs with the same limit *)
        unfold derivable_pt_abs.
        exists 0.
        split.
        * (* Prove derivable_pt *)
          unfold derivable_pt.
          exists 0.
          intro h.
          field_simp.
          ring.
          fdivide.
          ring.
        * (* Prove the limit is 0 *)
          intro eps.
          exists eps.
          intro h hne.
          unfold Rabs, Rdiv.
          rewrite <- mult_0_r.
          ring.
          <;> field_simp.
          <;> ring.
          <;> linarith.))).
  - (* Now prove the existence of a common derivative value *)
    (* Both functions have derivative 0 at 0 *)
    exist 0.
    split.
    * (* First function: t^2 *)
      (* The derivative of t^2 is 2t, which is 0 at t=0 *)
      split.
      + (* Prove derivable_pt *)
        unfold derivable_pt.
        exists 0.
        intro h.
        field_simp.
        ring.
        fdivide.
        ring.
      + (* Prove derivable_pt_abs with the same limit *)
        unfold derivable_pt_abs.
        exists 0.
        split.
        * (* Prove derivable_pt *)
          unfold derivable_pt.
          exists 0.
          intro h.
          field_simp.
          ring.
          fdivide.
          ring.
        * (* Prove the limit is 0 *)
          intro eps.
          exists eps.
          intro h hne.
          unfold Rabs, Rdiv.
          rewrite <- mult_0_r.
          ring.
          <;> field_simp.
          <;> ring.
          <;> linarith.
    * (* Second function: t^2 + ln(1) *)
      (* Since ln(1) = 0, this is identical to t^2 *)
      have h : (fun t => (t^2 + ln 1 : R)) = (fun t => (t^2 : R)) by
        funext t; ring; simpl.
      rewrite h.
      (* Now we just need to show t^2 has derivative 0 at 0, which we did above *)
      exact (conj (ex_intro _ 0 (by
        split.
        + (* Prove derivable_pt *)
          unfold derivable_pt.
          exists 0.
          intro h.
          field_simp.
          ring.
          fdivide.
          ring.
        + (* Prove derivable_pt_abs with the same limit *)
          unfold derivable_pt_abs.
          exists 0.
          split.
          * (* Prove derivable_pt *)
            unfold derivable_pt.
            exists 0.
            intro h.
            field_simp.
            ring.
            fdivide.
            ring.
          * (* Prove the limit is 0 *)
            intro eps.
            exists eps.
            intro h hne.
            unfold Rabs, Rdiv.
            rewrite <- mult_0_r.
            ring.
            <;> field_simp.
            <;> ring.
            <;> linarith.))).
Qed.

End.