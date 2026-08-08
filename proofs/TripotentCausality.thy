theory TripotentCausality
  imports Main
begin

(* Tripotent algebra T^3 = T partitioning spacetime *)
class tripotent =
  fixes T :: "'a ⇒ 'a"
  assumes tripotent_law: "T (T (T x)) = T x"

(* Causality classes based on tripotent elements *)
definition timelike_partition :: "'a::tripotent ⇒ bool" where
  "timelike_partition x ≡ (T x = x)"

definition null_partition :: "'a::tripotent ⇒ bool" where
  "null_partition x ≡ (T x = T (T x))"

end
