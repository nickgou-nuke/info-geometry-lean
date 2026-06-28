theory GrandIdentity
  imports Complex_Main
begin

section "Theorem-honest local Grand Identity packet"

text "
  This file records only exact definitional consequences:
  - a partition-function surface Q,
  - a Boltzmann potential ln(Q),
  - an abstract expectation observable Kexp,
  - the Legendre-style decomposition S_vN = S_B + beta * Kexp.

  It does not claim a proved de Rham/modular/time equivalence.
"

definition spinorialPartitionFunction :: "(real => real) => real => real" where
  "spinorialPartitionFunction Q = Q"

definition boltzmannEntropy :: "(real => real) => real => real" where
  "boltzmannEntropy Q beta = ln (spinorialPartitionFunction Q beta)"

definition modularEnergyExpectation :: "(real => real) => real => real" where
  "modularEnergyExpectation Kexp = Kexp"

definition vonNeumannEntropy :: "(real => real) => (real => real) => real => real" where
  "vonNeumannEntropy Q Kexp beta =
      boltzmannEntropy Q beta + beta * modularEnergyExpectation Kexp beta"

lemma spinorialPartitionFunction_apply:
  "spinorialPartitionFunction Q beta = Q beta"
  unfolding spinorialPartitionFunction_def by simp

lemma modularEnergyExpectation_apply:
  "modularEnergyExpectation Kexp beta = Kexp beta"
  unfolding modularEnergyExpectation_def by simp

lemma boltzmannEntropy_eq_ln:
  "boltzmannEntropy Q beta = ln (Q beta)"
  unfolding boltzmannEntropy_def spinorialPartitionFunction_def by simp

lemma vonNeumannEntropy_eq_boltzmann_plus_beta_expectation:
  "vonNeumannEntropy Q Kexp beta = boltzmannEntropy Q beta + beta * Kexp beta"
  unfolding vonNeumannEntropy_def modularEnergyExpectation_def by simp

end
