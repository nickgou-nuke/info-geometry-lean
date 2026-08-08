theory CausalDiamond
  imports Main
begin

(* Axiomatization of Krein spaces and time orientation *)
typedecl KreinSpace

(* Positive and negative Krein spaces *)
consts
  K_plus :: "KreinSpace set"
  H_minus :: "KreinSpace set"

(* Time orientation operators *)
consts
  time_orient_future :: "KreinSpace \<Rightarrow> KreinSpace"
  time_orient_past :: "KreinSpace \<Rightarrow> KreinSpace"

(* Axioms for mapping to Krein spaces *)
axiomatization where
  future_maps_to_K_plus: "\<forall>x. time_orient_future x \<in> K_plus" and
  past_maps_to_H_minus: "\<forall>x. time_orient_past x \<in> H_minus"

lemma time_orientation_valid:
  shows "time_orient_future x \<in> K_plus"
  using future_maps_to_K_plus by simp

end
