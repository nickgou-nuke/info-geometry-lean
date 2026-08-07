pairs = [(0,1), (0,2), (0,3), (2,3), (3,1), (1,2)]

def get_swap_lemma(a, b):
    # returns the rw for swapping a and b
    if a == b: return ""
    return f"  rw [ι_mul_ι_swap_of_orthogonal Q (HasSpacetimeBasis.orthogonal (Q := Q) {a} {b} (by decide))]\n"

def get_sq_lemma(a):
    return f"  rw [ι_sq]\n"

def gen_case(idx):
    a, b = pairs[idx]
    s = f"  case «{idx+1}» =>\n"
    s += f"    dsimp [basisBivector]\n"
    s += f"    rw [HasSpacetimeBasis.omega_eq (Q := Q)]\n"
    # Expression is (ι a * ι b) * (ι 0 * ι 1 * ι 2 * ι 3)
    s += f"    change (ι Q (gamma Q {a}) * ι Q (gamma Q {b})) * (ι Q (gamma Q 0) * (ι Q (gamma Q 1) * (ι Q (gamma Q 2) * ι Q (gamma Q 3)))) = _\n"
    s += f"    sorry\n"
    return s

with open("scratch_test2.lean", "w") as f:
    f.write('''import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Canonical.CliffordParityBridge
import InfoGeometry.Canonical.HestenesBivectorCarrier

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement
open InfoGeometry.Canonical.HestenesBivectorCarrier

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

''')

    f.write('''lemma hodge_basisBivector (i : Fin 6) :
    basisBivector Q i * Omega (Q := Q) ∈ Bivector13 Q := by
  revert i
  intro i
  fin_cases i
''')
    for i in range(6):
        f.write(gen_case(i))
