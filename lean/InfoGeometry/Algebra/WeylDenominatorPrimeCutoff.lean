import InfoGeometry.Algebra.PrimeA1RootSystem
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Thermodynamics.SouriauTemperature
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Weyl Denominator Prime Cutoff

Implements the finite Weyl denominator $\prod_{p \in P} (1 - p^{-s})$.
This is the fermionic partition supertrace $1/\zeta_P(s)$.
-/

open InfoGeometry.Thermodynamics
open InfoGeometry.Algebra
open scoped BigOperators

namespace InfoGeometry.Algebra.WeylDenominator

/--
The finite Weyl denominator of the $A_1^P$ system, evaluated at 
the Souriau temperature $s$.
-/
noncomputable def finiteWeylDenominator (S : PrimeA1RootSystem) (s : ℂ) : ℂ :=
  S.P.prod (fun p => (1 - souriauEvaluation p s))

end InfoGeometry.Algebra.WeylDenominator
