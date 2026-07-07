/-- 
The Causal Barrier from Nesterov-Nemirovski Interior-Point Optimization.
The self-concordant potential `-log(det(X))` physically repels the optimization 
algorithm from crossing the absolute horizon (the speed of light).
-/
noncomputable def SelfConcordantCausalBarrier (detX : ℝ) : ℝ :=
  - Real.log detX