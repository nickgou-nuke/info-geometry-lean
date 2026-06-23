(* Navier-Stokes-Legendre theorem (Isabelle/HOL) *)
(* Statement (informal):
   L.fenchelGap(theta, eta) = 0  <->  div(u) = 0
*)

theory navier_stokes_legendre
  imports Main
begin

(* Placeholder statement of the theorem as a locale or just a fixed proposition. *)
axiomatization navier_stokes_lemma :: bool where
  navier_stokes_lemma_def: "navier_stokes_lemma = True"

(* Trivial lemma to confirm the theory loads. *)
lemma navier_stokes_trivial: "navier_stokes_lemma = True"
  by (simp add: navier_stokes_lemma_def)

end