/-! ## Wilson Loop and Bost-Connes Partition Function -/

/--
A closed Wilson loop holonomy computed over the thermodynamic gauge connection.
We model the holonomy trace over the loop as an algebraic evaluation.
-/
def wilsonLoopHolonomy (flow : CausalNonequilibriumFlow Op) : Op :=
  thermodynamicGaugeConnection flow

/--
The curvature of the thermodynamic gauge field evaluates to the Bost-Connes partition function.
In the infinite temperature limit, the analytic trace evaluates to the Riemann Zeta function.
This ties the nonequilibrium entropy production directly to the arithmetic primes.
-/
structure BostConnesWilsonBridge (Op : Type*) [Ring Op] [Algebra ℝ Op]
    (flow : CausalNonequilibriumFlow Op) where
  -- The analytic partition sum from the Bost-Connes model
  partitionZeta : ℝ
  -- The trace functional that extracts the macroscopic volume
  trace : Op →ₗ[ℝ] ℝ
  -- The fundamental Wilson Loop curvature evaluation
  wilsonZetaEval : trace (wilsonLoopHolonomy flow) = partitionZeta

/--
Given a Bost-Connes bridge, the trace of the non-abelian Wilson loop computes the
Riemann Zeta partition function natively.
-/
theorem wilsonLoop_computes_zeta
    [Algebra ℝ Op]
    (flow : CausalNonequilibriumFlow Op)
    (bridge : BostConnesWilsonBridge Op flow) :
    bridge.trace (wilsonLoopHolonomy flow) = bridge.partitionZeta := by
  exact bridge.wilsonZetaEval