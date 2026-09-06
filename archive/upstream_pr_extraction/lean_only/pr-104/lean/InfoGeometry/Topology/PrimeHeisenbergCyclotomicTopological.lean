import Mathlib
import InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge
import InfoGeometry.Canonical.PrimeHeisenbergOscillators

/-!
# Topological prime-mode/cyclotomic readout

The prime oscillator owner supplies the operators `J_p` and `J_{-p}`.  This
file records the compatible order-three degree readout on their mode labels.
It deliberately does not put a topology on an operator space or assert a
Heisenberg--Zorn representation: the topological statement is the genuine
locally constant arithmetic readout on the discrete prime index.
-/

namespace InfoGeometry.Topology.PrimeHeisenbergCyclotomicTopological

open InfoGeometry.Canonical
open InfoGeometry.Canonical.PrimeHeisenbergOscillators

noncomputable section

/-- Cyclotomic degree of the positive prime mode `J_p`. -/
def primeModeCyclotomicDegree (p : ℕ) : ZMod 3 :=
  heisenbergModeDegree (p : ℤ)

@[simp] theorem primeModeCyclotomicDegree_eq (p : ℕ) :
    primeModeCyclotomicDegree p = heisenbergModeDegree (p : ℤ) := by
  rfl

/-- The creation mode has the opposite cyclotomic degree. -/
@[simp] theorem primeCreationCyclotomicDegree (p : ℕ) :
    heisenbergModeDegree (-(p : ℤ)) =
      -primeModeCyclotomicDegree p := by
  exact heisenbergModeDegree_neg (p : ℤ)

/-- The annihilation/creation pair is degree-zero in the Heisenberg resonance. -/
theorem primeMode_resonance_cyclotomic_degree_zero (p : ℕ) :
    primeModeCyclotomicDegree p +
        heisenbergModeDegree (-(p : ℤ)) = 0 := by
  change heisenbergModeDegree (p : ℤ) +
      heisenbergModeDegree (-(p : ℤ)) = 0
  exact heisenberg_resonance_has_zero_cyclotomic_degree
    (p : ℤ) (-(p : ℤ)) (by simp)

/-- The prime degree readout is continuous for the discrete prime index. -/
theorem continuous_primeModeCyclotomicDegree :
    Continuous primeModeCyclotomicDegree := by
  simpa [primeModeCyclotomicDegree] using
    (continuous_of_discreteTopology :
      Continuous primeModeCyclotomicDegree)

/-- The prime degree readout is locally constant. -/
theorem isLocallyConstant_primeModeCyclotomicDegree :
    IsLocallyConstant primeModeCyclotomicDegree := by
  simpa [primeModeCyclotomicDegree] using
    (IsLocallyConstant.of_discrete (f := primeModeCyclotomicDegree))

/-- The paired annihilation/creation degree readout is continuous. -/
def primeModeCyclotomicPair (p : ℕ) : ZMod 3 × ZMod 3 :=
  (primeModeCyclotomicDegree p, heisenbergModeDegree (-(p : ℤ)))

theorem continuous_primeModeCyclotomicPair :
    Continuous primeModeCyclotomicPair := by
  simpa [primeModeCyclotomicPair] using
    (continuous_of_discreteTopology :
      Continuous primeModeCyclotomicPair)

end
end InfoGeometry.Topology.PrimeHeisenbergCyclotomicTopological
