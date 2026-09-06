import Mathlib.Tactic
import InfoGeometry.Canonical.CantorCuntzBasis
import InfoGeometry.Meta.Architecture

noncomputable section

namespace InfoGeometry.Canonical.CantorKMSCylinderState

open InfoGeometry.Canonical.CantorCuntzBasis

/-!
# Cantor KMS Cylinder State

This module isolates the finite-cylinder substrate for the Cuntz/KMS boundary
state.  It does not construct a GNS Hilbert space.  It proves the exact
finite-word scaling and cross-branch orthogonality laws that a later GNS
construction should consume.

For a binary cylinder word `w`, the uniform KMS cylinder weight is `2^-|w|`.
For matrix-unit-style word pairs, the diagonal coefficient is this weight and
off-diagonal coefficients are zero.

#### BUCKET 1: CLOSED FINITE THEOREMS

[Fully verified lemmas with zero remaining dependencies or open goals. Fully
checked by the kernel.]

* `cylinderKMSWeight_nonneg`
* `cylinderKMSWeight_cons`
* `cylinderKMSWeight_cons_false`
* `cylinderKMSWeight_cons_true`
* `cylinderKMSCoeff_self`
* `cylinderKMSCoeff_ne`
* `cylinderKMSCoeff_self_nonneg`
* `cylinderKMSCoeff_cons_same`
* `cylinderKMSCoeff_cons_false_false`
* `cylinderKMSCoeff_cons_true_true`
* `cylinderKMSCoeff_cons_false_true`
* `cylinderKMSCoeff_cons_true_false`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES

[Theorems that compile from explicitly named theorem parameters or imported
verified premises.]

* None.

#### BUCKET 3: OPEN CLOSURE DEBT

[Exact theorem statements that remain unproved. No wrappers, sockets, fields,
witnesses, certificates, or renamed placeholders.]

* Construct the GNS quotient and completion from these finite-cylinder
  coefficients.
* Identify that completion with the concrete `PiLp`/`lp` Cantor-boundary
  Hilbert carrier.
* Transport the Cuntz generators and phase-axis commutation through that GNS
  representation.
-/

/-- The uniform binary KMS weight of a finite cylinder word: `2^-|w|`. -/
@[rep_depth operator]
def cylinderKMSWeight (w : BinaryWord) : ℝ :=
  ((1 / 2 : ℝ) ^ w.length)

@[rep_depth operator]
theorem cylinderKMSWeight_nonneg (w : BinaryWord) :
    0 ≤ cylinderKMSWeight w := by
  unfold cylinderKMSWeight
  exact pow_nonneg (by norm_num) w.length

/-- Prefixing either binary branch halves the cylinder KMS weight. -/
@[rep_depth operator]
theorem cylinderKMSWeight_cons (b : Bool) (w : BinaryWord) :
    cylinderKMSWeight (b :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w := by
  simp [cylinderKMSWeight, pow_succ, mul_comm]

@[rep_depth operator]
theorem cylinderKMSWeight_cons_false (w : BinaryWord) :
    cylinderKMSWeight (false :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w :=
  cylinderKMSWeight_cons false w

@[rep_depth operator]
theorem cylinderKMSWeight_cons_true (w : BinaryWord) :
    cylinderKMSWeight (true :: w) = (1 / 2 : ℝ) * cylinderKMSWeight w :=
  cylinderKMSWeight_cons true w

/--
The two depth-one children of a cylinder split the parent weight evenly.

This is the finite algebraic version of the shard/whole readout: each branch
contains exactly half of the cylinder mass, and the two children sum back to the
parent.
-/
@[rep_depth operator]
theorem cylinderKMSWeight_children_sum (w : BinaryWord) :
    cylinderKMSWeight (false :: w) + cylinderKMSWeight (true :: w) =
      cylinderKMSWeight w := by
  rw [cylinderKMSWeight_cons_false, cylinderKMSWeight_cons_true]
  ring

/--
Diagonal finite-cylinder coefficient for the uniform KMS state.

This is the matrix-unit shadow of `φ(S_u S_v*)`: diagonal pairs receive the
cylinder weight, off-diagonal pairs vanish.
-/
@[rep_depth operator]
def cylinderKMSCoeff (u v : BinaryWord) : ℝ :=
  if u = v then cylinderKMSWeight u else 0

@[simp, rep_depth operator]
theorem cylinderKMSCoeff_self (w : BinaryWord) :
    cylinderKMSCoeff w w = cylinderKMSWeight w := by
  simp [cylinderKMSCoeff]

@[rep_depth operator]
theorem cylinderKMSCoeff_ne {u v : BinaryWord} (h : u ≠ v) :
    cylinderKMSCoeff u v = 0 := by
  simp [cylinderKMSCoeff, h]

@[rep_depth operator]
theorem cylinderKMSCoeff_self_nonneg (w : BinaryWord) :
    0 ≤ cylinderKMSCoeff w w := by
  simp [cylinderKMSCoeff_self, cylinderKMSWeight_nonneg]

/-- Same-branch prefixing halves the finite-cylinder KMS coefficient. -/
@[rep_depth operator]
theorem cylinderKMSCoeff_cons_same (b : Bool) (u v : BinaryWord) :
    cylinderKMSCoeff (b :: u) (b :: v) =
      (1 / 2 : ℝ) * cylinderKMSCoeff u v := by
  by_cases h : u = v
  · subst v
    simp [cylinderKMSCoeff_self, cylinderKMSWeight_cons]
  · have hcons : b :: u ≠ b :: v := by
      intro hc
      cases hc
      exact h rfl
    simp [cylinderKMSCoeff, h, hcons]

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_false_false (u v : BinaryWord) :
    cylinderKMSCoeff (false :: u) (false :: v) =
      (1 / 2 : ℝ) * cylinderKMSCoeff u v :=
  cylinderKMSCoeff_cons_same false u v

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_true_true (u v : BinaryWord) :
    cylinderKMSCoeff (true :: u) (true :: v) =
      (1 / 2 : ℝ) * cylinderKMSCoeff u v :=
  cylinderKMSCoeff_cons_same true u v

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_false_true (u v : BinaryWord) :
    cylinderKMSCoeff (false :: u) (true :: v) = 0 := by
  have h : false :: u ≠ true :: v := by
    intro hc
    cases hc
  exact cylinderKMSCoeff_ne h

@[rep_depth operator]
theorem cylinderKMSCoeff_cons_true_false (u v : BinaryWord) :
    cylinderKMSCoeff (true :: u) (false :: v) = 0 := by
  have h : true :: u ≠ false :: v := by
    intro hc
    cases hc
  exact cylinderKMSCoeff_ne h

end InfoGeometry.Canonical.CantorKMSCylinderState
