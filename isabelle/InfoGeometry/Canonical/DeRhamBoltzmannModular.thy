theory DeRhamBoltzmannModular
  imports Complex_Main
begin

definition partitionQ :: "real => real => real" where
  "partitionQ r beta = exp (beta * r) + exp (-(beta * r))"

definition entropyPotential :: "real => real => real" where
  "entropyPotential r beta = ln (partitionQ r beta)"

definition betaResponse :: "real => real => real" where
  "betaResponse r beta = r * (exp (beta * r) - exp (-(beta * r))) / partitionQ r beta"

lemma partitionQ_pos:
  shows "partitionQ r beta > 0"
  unfolding partitionQ_def
  using exp_gt_zero [of "beta * r"] exp_gt_zero [of "- (beta * r)"]
  by linarith

lemma entropyPotential_well_defined:
  "entropyPotential r beta = ln (exp (beta * r) + exp (-(beta * r)))"
  unfolding entropyPotential_def partitionQ_def
  by simp

lemma betaResponse_def_lemma:
  "betaResponse r beta = r * (exp (beta * r) - exp (-(beta * r))) / partitionQ r beta"
  unfolding betaResponse_def
  by simp

end
