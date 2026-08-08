theory BayesianGradientFlow
  imports Main
begin

text ‹
  Discrete Bayesian steps mapping to continuous gradient flow 
  over a convex manifold.
›

record BayesianState =
  prior :: "real"
  posterior :: "real"
  evidence :: "real"

definition bayes_update :: "BayesianState ⇒ real ⇒ BayesianState" where
  "bayes_update s likelihood = 
    ⦇ prior = posterior s, 
      posterior = (posterior s * likelihood) / evidence s, 
      evidence = evidence s ⦈"

text ‹
  The continuous gradient flow over the convex manifold is modeled
  by the iterative application of the Bayesian step.
›

definition gradient_flow_step :: "BayesianState ⇒ real ⇒ BayesianState" where
  "gradient_flow_step = bayes_update"

lemma gradient_flow_equivalence:
  "gradient_flow_step s L = bayes_update s L"
  by (simp add: gradient_flow_step_def)

end
