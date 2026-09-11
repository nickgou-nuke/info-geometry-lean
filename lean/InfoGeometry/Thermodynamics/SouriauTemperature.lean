import InfoGeometry.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Basic

/-!
# Souriau Temperature Evaluation

Formalizes the Souriau thermal evaluation map for the prime gas.
Evaluates formal root weights $e^{-\alpha_p}$ to prime power rapidities $p^{-s}$.
-/

namespace InfoGeometry.Thermodynamics

/-- 
The Souriau thermal evaluation:
Maps formal root weights to the complex s-plane.
$e^{-\alpha_p} \mapsto p^{-s}$
-/
noncomputable def souriauEvaluation (p : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) ^ (-s)

/--
The Souriau Temperature Vector in the Cartan Subalgebra.
In the infinite-dimensional prime-root system, this is represented by 
 the complex parameter `s`.
-/
abbrev SouriauTemperature := ℂ

namespace SouriauTemperature

abbrev s (temperature : SouriauTemperature) : ℂ := temperature

end SouriauTemperature

end InfoGeometry.Thermodynamics
