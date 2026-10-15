import Experimental.Sandbox.Probability.FiniteMarkovCesaroPrerequisites

/-!
# Audit surface for the finite Markov Cesàro prerequisites

The imported owner proves only finite algebraic telescoping and a stochastic
endpoint bound. The audit deliberately makes no assertion about convergence.
-/

namespace InfoGeometry.Experimental.Probability.FiniteMarkovCesaro.Audit

#check InfoGeometry.Experimental.Probability.FiniteMarkovCesaro.telescoping_one_sub_matrix_mulVec
#check InfoGeometry.Experimental.Probability.FiniteMarkovCesaro.endpoint_error_le_two_mul_bound

#print axioms InfoGeometry.Experimental.Probability.FiniteMarkovCesaro.telescoping_one_sub_matrix_mulVec
#print axioms InfoGeometry.Experimental.Probability.FiniteMarkovCesaro.endpoint_error_le_two_mul_bound

end InfoGeometry.Experimental.Probability.FiniteMarkovCesaro.Audit
