import Mathlib.Tactic
import InfoGeometry.Algebra.Cl11Fermions
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

/-!
# Peirce ladder operator packets

This file defines Furey-inspired ladder expressions over the existing
`Cl(1,1)` carrier and proves only the conditional algebraic square-zero facts
shown below.  It does not prove CAR for a full split-octonion embedding, does
not construct a Standard Model representation, and does not prove an Albert
algebra particle decomposition.
-/

open Cl11Fermions
open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

noncomputable section

namespace InfoGeometry.Algebra.PeirceLadder

/-! ## 1. The internal complex structure J = e₁ -/

/-- The Cl(1,1) complex structure. J² = -1, J anticommutes with e₀. -/
def J : CliffordAlgebra q11 := e₁

theorem J_sq_neg_one : J * J = -1 := e₁_sq

/-! ## 2. Ladder operators on split octonion basis elements -/

/-- Involution: 1/2 in the coefficient field. -/
def half : ℚ := 1/2

/--
Furey annihilation operator α = ½(x + J·x) for a split-octonion basis element x.
The J·x multiplication uses the Clifford action: x is embedded via the
canonical ℚ-algebra map into the Clifford algebra.
-/
noncomputable def alpha (x : CliffordAlgebra q11) : CliffordAlgebra q11 :=
  (algebraMap ℚ (CliffordAlgebra q11) half) * (x + J * x)

/--
Furey creation operator α† = ½(x - J·x).
-/
noncomputable def alphaDag (x : CliffordAlgebra q11) : CliffordAlgebra q11 :=
  (algebraMap ℚ (CliffordAlgebra q11) half) * (x - J * x)

/-! ## 3. CAR identities for ladder operators -/

/--
**Nilpotence** (BUCKET 3): α² = 0 for split-octonion nilpotents.
Requires proving J·x = -x·J for the Clifford action of J on the
embedded octonion via the algebra map. The diagonal STU model and
the all-512-basis verification in FreudenthalComplete.lean provide
numerical evidence. Full algebraic proof requires the Clifford
embedding of the split octonions with the metric/norm form.

Witnessed by: tools/sympy/freudenthal_identity.py (SymPy),
tools/gap/g2_twisted_braiding_roots.g (GAP).
-/
theorem alpha_core_sq_zero_of_square_zero_of_anticommute
    (x : CliffordAlgebra q11)
    (hx2 : x * x = 0)
    (hJx : J * x = - x * J) :
    (x + J * x) * (x + J * x) = 0 := by
  have hJ2 : J * J = -1 := J_sq_neg_one
  have hxJ : x * J = - J * x := by
    have h' := congrArg Neg.neg hJx
    simpa using h'.symm
  have h1 : x * (J * x) = 0 := by
    calc
      x * (J * x) = (x * J) * x := by rw [mul_assoc]
      _ = (-J * x) * x := by rw [hxJ]
      _ = - ((J * x) * x) := by noncomm_ring
      _ = 0 := by simp [mul_assoc, hx2]
  have h2 : (J * x) * x = 0 := by simp [mul_assoc, hx2]
  have h3 : (J * x) * (J * x) = 0 := by
    calc
      (J * x) * (J * x) = J * ((x * J) * x) := by noncomm_ring
      _ = J * ((-J * x) * x) := by rw [hxJ]
      _ = J * (-(J * x * x)) := by noncomm_ring
      _ = 0 := by simp [mul_assoc, hx2]
  calc
    (x + J * x) * (x + J * x)
        = x * x + x * (J * x) + (J * x) * x + (J * x) * (J * x) := by
          noncomm_ring
    _ = 0 := by simp [hx2, h1, h2, h3]

/-- The two cross terms in the unscaled Furey ladder square vanish under the
square-zero and anticommutation hypotheses. -/
theorem alpha_core_cross_terms_vanish
    (x : CliffordAlgebra q11)
    (hx2 : x * x = 0)
    (hJx : J * x = - x * J) :
    x * (J * x) = 0 ∧ (J * x) * x = 0 := by
  have hxJ : x * J = - J * x := by
    have h' := congrArg Neg.neg hJx
    simpa using h'.symm
  constructor
  · calc
      x * (J * x) = (x * J) * x := by rw [mul_assoc]
      _ = (-J * x) * x := by rw [hxJ]
      _ = - ((J * x) * x) := by noncomm_ring
      _ = 0 := by simp [mul_assoc, hx2]
  · simp [mul_assoc, hx2]

/-! ## 4. Color triplet construction -/

/-- The 6 quark ladder operators as a structured packet. -/
structure QuarkLadderPacket where
  alpha : Fin 3 → CliffordAlgebra q11
  alphaDag : Fin 3 → CliffordAlgebra q11
  beta : Fin 3 → CliffordAlgebra q11
  betaDag : Fin 3 → CliffordAlgebra q11

/-- The lepton ladder operator (uses the idempotent ePlus direction). -/
structure LeptonLadderPacket where
  nu : CliffordAlgebra q11
  nuDag : CliffordAlgebra q11
  electron : CliffordAlgebra q11
  electronDag : CliffordAlgebra q11

/-! ## 5. Arithmetic count readout -/

/-- Elementary arithmetic count used by downstream Furey-inspired naming.  This
is not an Albert-algebra or Standard-Model decomposition theorem. -/
theorem generation_dimension_count :
    1 + 1 + 12 + 12 + 1 = (27 : ℕ) := by
  norm_num

end InfoGeometry.Algebra.PeirceLadder
