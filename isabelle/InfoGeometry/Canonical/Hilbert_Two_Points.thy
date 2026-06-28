theory Hilbert_Two_Points
  imports Main
  begin

section ‹The vector space of functions on a two-point set has dimension 2›

typedeclare point =  ― ‑‑ we will use bool instead, but we can define a datatype›

(* Actually we can just use bool *)
type_synonym point = bool

(* The type of functions from point to real *)
type_synonym fun_space = "point ⇒ real"

(* Define the delta functions *)
definition delta0 :: "point ⇒ real" where
  "delta0 p = (if p then 0 else 1)"

definition delta1 :: "point ⇒ real" where
  "delta1 p = (if p then 1 else 0)"

(* Linear combination *)
definition lincomb :: "real ⇒ real ⇒ (point ⇒ real) ⇒ (point ⇒ real) ⇒ (point ⇒ real)" where
  "lincomb a b f p = a * f p + b * g p" ― ‑‑ wait, we need f and g as parameters›

Oops, we need to fix: lincomb takes four arguments: a, b, f, g.
Let's redefine.

definition lincomb :: "real ⇒ real ⇒ (point ⇒ real) ⇒ (point ⇒ real) ⇒ (point ⇒ real)" where
  "lincomb a b f g p = a * f p + b * g p"

(* Equality of functions *)
definition feq :: "(point ⇒ real) ⇒ (point ⇒ real) ⇒ bool" where
  "feq f g ↔ (∀ p. f p = g p)"

(* Zero function *)
definition zero_fun :: "point ⇒ real" where
  "zero_fun p = 0"

(* Lemma: delta0 and delta1 are linearly independent *)
lemma delta_independent:
  assumes "∀ p::point. a * delta0 p + b * delta1 p = 0"
  shows "a = 0 ∧ b = 0"
proof -
  have h1: "a * delta0 True + b * delta1 True = 0" using assms by simp
  have h2: "a * delta0 False + b * delta1 False = 0" using assms by simp
  have h3: "delta0 True = 0" by (simp add: delta0_def)
  have h4: "delta1 True = 1" by (simp add: delta1_def)
  have h5: "delta0 False = 1" by (simp add: delta0_def)
  have h6: "delta1 False = 0" by (simp add: delta1_def)
  from h1 h3 h4 have h7: "a * 0 + b * 1 = 0" by simp
  from h2 h5 h6 have h8: "a * 1 + b * 0 = 0" by simp
  from h7 have h9: "b = 0" by simp
  from h8 h9 have h10: "a = 0" by simp
  thus "a = 0 ∧ b = 0" by simp
qed

(* Lemma: any function f can be written as a linear combination of delta0 and delta1 *)
lemma delta_span:
  fixes f :: "point ⇒ real"
  shows "∃ a b. ∀ p. f p = a * delta0 p + b * delta1 p"
proof -
  let ?a = "f False"
  let ?b = "f True"
  have "∀ p. f p = ?a * delta0 p + ?b * delta1 p"
  proof (intro allI, cases p)
    case True
    then show ?thesis
      by (simp add: delta0_def delta1_def)
      (simp add: mult_ac)
  next
    case False
    then show ?thesis
      by (simp add: delta0_def delta1_def)
      (simp add: add_ac)
  qed
  thus ?thesis by blast
qed

(* Theorem: the dimension of the function space is 2 *)
theorem dim_fun_space_two:
  obtains e1 e2 where
    "∀ a b. (∀ p. a * e1 p + b * e2 p = 0) ⟶ a = 0 ∧ b = 0" and
    "∀ f. ∃ a b. ∀ p. f p = a * e1 p + b * e2 p"
proof -
  obtain e1 e2 where
    "∀ a b. (∀ p. a * e1 p + b * e2 p = 0) ⟶ a = 0 ∧ b = 0" and
    "∀ f. ∃ a b. ∀ p. f p = a * e1 p + b * e2 p"
  proof -
    use delta0, delta1 in
      (try simp_all add: delta0_def delta1_def fun_eq_iff, metis (no_types, lifting) delta_independent delta_span) +
      (metis delta_span) +
      (metis delta_independent)
  esimp using this by blast
qed

end