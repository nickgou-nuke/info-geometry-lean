theory PathIntegralFluence
  imports Main
begin

(* Abstract representation of continuous topological limits of stochastic path integrals *)
datatype PathIntegral = ContinuousLimit nat

(* Abstract representation of neutron transport adjoint bounds *)
datatype AdjointBound = Adjoint nat

(* Native isomorphism representation *)
fun is_isomorphic :: "PathIntegral \<Rightarrow> AdjointBound \<Rightarrow> bool" where
  "is_isomorphic (ContinuousLimit x) (Adjoint y) = (x = y)"

lemma native_isomorphism: "is_isomorphic (ContinuousLimit x) (Adjoint x)"
  by simp

end
