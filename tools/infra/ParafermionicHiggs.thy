theory ParafermionicHiggs
  imports Complex_Main
begin

text ‹
  Isabelle/HOL Formalization of the Parafermionic BEC Phase Higgs.
›

record VolumeZeroOp =
  S :: real

locale BECHiggsPhase =
  fixes S_op :: VolumeZeroOp
  fixes global_phase :: real
  fixes n_0 :: nat
  assumes nilpotent: "(S S_op) * (S S_op) = 0"
  assumes no_fundamental_scalars: "n_0 = 0"

lemma (in BECHiggsPhase) composite_higgs:
  "n_0 = 0"
  by (rule no_fundamental_scalars)

end
