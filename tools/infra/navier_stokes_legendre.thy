(* Navier-Stokes-Legendre theorem (Isabelle/HOL) *)
(* Statement (informal):
   L.fenchelGap(theta, eta) = 0  <->  div(u) = 0
*)

theory NavierStokesLegendre
  imports Main
begin

locale navier_stokes =
  fixes theta eta :: real
begin

definition phi :: "real => real => real" where
  "phi θ η = (θ^2 + η^2)/2 - θ*η"

lemma phi_zero_iff: "phi θ η = 0 ⟷ θ = η"
proof
  assume "phi θ η = 0"
  then have "(θ - η)^2 = 0" by (simp add: phi_def algebra)
  then have "θ - η = 0" by (simp only: pow2_eq_0_iff)
  thus "θ = η" by algebra
next
  assume "θ = η"
  then show "phi θ η = 0" by (simp add: phi_def algebra)
qed

end

end