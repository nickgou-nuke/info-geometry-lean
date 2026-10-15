import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.SuperGrassmannian.WeylBerezinianDeformation
import Experimental.Sandbox.Lie.GlobalKANCasimirReduction

/-!
# Audit: Global Iwasawa KAN, Polar Symmetric Space, and Casimir Reduction

Axiomatic audit of the global Lie-theoretic decompositions and the algebraic Casimir invariant hierarchy.
-/

open Experimental.Sandbox.Lie.GlobalKANCasimirReduction

#print axioms iwasawa_decomposition_2x2
#print axioms iwasawa_decomposition_unique
#print axioms cartan_is_abelian
#print axioms nilpotent_sq_zero
#print axioms nilpotent_lower_sq_zero
#print axioms polar_decomposition_2x2
#print axioms polar_decomposition_unique
#print axioms cartanInvolution_compactK
#print axioms cartanInvolution_polarP
#print axioms compact_compact_comm
#print axioms compact_polar_comm
#print axioms polar_polar_comm
#print axioms casimirOne_compactK
#print axioms casimirOne_cartanA
#print axioms casimirOne_polarP
#print axioms casimirOne_nilpotent
#print axioms casimirTwo_on_cartan
#print axioms casimirTwo_on_compactK
#print axioms casimirTwo_on_nilpotent_zero
#print axioms casimirTwo_weyl_invariant
#print axioms casimirTwo_gauge_invariant
#print axioms compile_global_kan_casimir_reduction
