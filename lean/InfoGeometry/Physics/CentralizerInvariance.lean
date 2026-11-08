import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Central {±I} invariance under the Pin(5,5) twisted-conjugation representation

Proves that the central element `-1` in the Clifford algebra acts trivially
on the vector representation via twisted conjugation:

    ρ(-1)(v) = α(-1)·v·(-1)⁻¹ = v

This shows that the {I, -I} kernel of the double cover Pin → O acts as the
identity on the orbit stratification of J₂(𝕆_s), so the classification
descends to O(5,5) / PSO(5,5).
-/

open CliffordAlgebra

noncomputable section

namespace InfoGeometry.Physics.CentralizerInvariance

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (Q : QuadraticForm R M)

/--
The twisted-conjugation (sandwich) action of a unit g ∈ Cl(Q)× on an
element v ∈ Cl(Q):

    ρ(g)(v) = α(g) · v · g⁻¹

where α is the grading automorphism (involute).
This is the standard Pin group action on vectors.
-/
def twistedConjugation (g : (CliffordAlgebra Q)ˣ) (v : CliffordAlgebra Q) : CliffordAlgebra Q :=
  involute (g : CliffordAlgebra Q) * v * ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)

/--
The unit -1 in the Clifford algebra.  This is the non-trivial element of
the centre {±1}.
-/
def minusOne : (CliffordAlgebra Q)ˣ :=
  -1

@[simp]
theorem inv_minusOne : (minusOne Q : (CliffordAlgebra Q)ˣ)⁻¹ = minusOne Q := by
  ext; simp [minusOne]

/--
**Theorem:** `ρ(-1)(v) = v` for all `v`.  The central element -1 acts
trivially on the vector representation.

Proof: α(-1) = -1 (since -1 is a degree-0 scalar), and (-1)·v·(-1) = v
because the central scalar `-1` commutes with every element and `(-1) * (-1) = 1`.
-/
theorem centralizer_action_trivial (v : CliffordAlgebra Q) :
    twistedConjugation Q (minusOne Q) v = v := by
  dsimp [twistedConjugation, minusOne]
  simp

/--
**Corollary/readout:** the central element `-1` fixes every Clifford carrier under
this twisted-conjugation action.  This is the exact kernel-triviality statement
available in this file; any orbit-stratum descent theorem must be proved in the
owner stratum file from this equality, not hidden here behind `True`.
-/
theorem centralizer_preserves_orbit_readout (x : CliffordAlgebra Q) :
    twistedConjugation Q (minusOne Q) x = x :=
  centralizer_action_trivial Q x

end InfoGeometry.Physics.CentralizerInvariance
