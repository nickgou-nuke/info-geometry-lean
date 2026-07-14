import InfoGeometry.Clifford.SplitCl44CausalEnvelope
import InfoGeometry.Clifford.Spacetime
import InfoGeometry.Canonical.Spin44CharacterShadow

/-!
# `Cl(4,4)` signature residue diagnostics

This module is the next theorem-safe layer after
`SplitCl44CausalEnvelope`.

It formalizes the metric-signature part of the prose:

* the ambient split carrier has count `(4,4)`;
* the Lorentz/Minkowski residue has count `(3,1)`;
* selecting `(3,1)` from `(4,4)` is explicit count-level bookkeeping, not an
  automatic theorem of split `Cl(4,4)`;
* the finite `D₄` / `Spin(4,4)` character shadow has eight even and eight odd
  half-spinor weights.

It does not prove an eta-invariant theorem, an `E₈` representation theorem, or
the uniqueness of spacetime signature.  Those claims require separate analytic
and representation-theoretic owners.
-/

namespace Cl44SignatureResidue

open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.Canonical.Spin44CharacterShadow

/-! ## Signature counts -/

/-- Purely arithmetic signature count, represented explicitly as `(positive, negative)`. -/
abbrev SignatureCount : Type :=
  Nat × Nat

/-- Positive part of an explicit signature count. -/
def signaturePositive (S : SignatureCount) : Nat :=
  S.1

/-- Negative part of an explicit signature count. -/
def signatureNegative (S : SignatureCount) : Nat :=
  S.2

/-- Total real dimension of a signature count. -/
def total (S : SignatureCount) : Nat :=
  signaturePositive S + signatureNegative S

/-- Signed index `p - q` of a signature count. -/
def index (S : SignatureCount) : Int :=
  Int.ofNat (signaturePositive S) - Int.ofNat (signatureNegative S)

/-- Split `(4,4)` signature count. -/
def split44 : SignatureCount :=
  (4, 4)

/-- Lorentzian `(3,1)` signature count in the `(+---)` convention. -/
def lorentz31 : SignatureCount :=
  (3, 1)

/-- Opposite Lorentzian `(1,3)` signature count. -/
def lorentz13 : SignatureCount :=
  (1, 3)

@[simp] theorem total_split44 : total split44 = 8 := by
  rfl

@[simp] theorem index_split44 : index split44 = 0 := by
  rfl

@[simp] theorem total_lorentz31 : total lorentz31 = 4 := by
  rfl

@[simp] theorem index_lorentz31 : index lorentz31 = 2 := by
  rfl

@[simp] theorem total_lorentz13 : total lorentz13 = 4 := by
  rfl

@[simp] theorem index_lorentz13 : index lorentz13 = -2 := by
  rfl

/-! ## Explicit count-level selection of `(3,1)` from `(4,4)` -/

/-- Explicit ambient split `(4,4)` count in the count-level selection. -/
def split44_to_lorentz31_ambient : SignatureCount :=
  split44

/-- Explicit retained Lorentz `(3,1)` count in the count-level selection. -/
def split44_to_lorentz31_residue : SignatureCount :=
  lorentz31

/-- Explicit discarded complementary `(1,3)` count in the count-level selection. -/
def split44_to_lorentz31_discarded : SignatureCount :=
  lorentz13

/-- Positive count balance for the explicit `(4,4) = (3,1) + (1,3)` selection. -/
@[simp] theorem split44_to_lorentz31_positive_balance :
    signaturePositive split44_to_lorentz31_residue
        + signaturePositive split44_to_lorentz31_discarded =
      signaturePositive split44_to_lorentz31_ambient := by
  rfl

/-- Negative count balance for the explicit `(4,4) = (3,1) + (1,3)` selection. -/
@[simp] theorem split44_to_lorentz31_negative_balance :
    signatureNegative split44_to_lorentz31_residue
        + signatureNegative split44_to_lorentz31_discarded =
      signatureNegative split44_to_lorentz31_ambient := by
  rfl

/-- The explicit `(4,4) → (3,1)` selection preserves the total count `4 + 4 = 8`. -/
@[simp] theorem split44_to_lorentz31_total_balance :
    total split44_to_lorentz31_residue + total split44_to_lorentz31_discarded =
      total split44_to_lorentz31_ambient := by
  rfl

/-! ## Explicit count-level eta shadow -/

/-- Count-level eta shadow: the signed index of the explicit selected residue. -/
def etaShadow : Int :=
  index split44_to_lorentz31_residue

/-- The canonical count-level `(4,4) → (3,1)` selection has eta shadow `2`. -/
@[simp] theorem etaShadow_split44_to_lorentz31 :
    etaShadow = 2 := by
  rfl

/--
This module proves only the count-level eta shadow.
-/
theorem no_analytic_eta_invariant_claim : etaShadow = 2 :=
  etaShadow_split44_to_lorentz31

/-! ## D4 half-spinor count shadow -/

/-- The finite `D₄` even half-spinor sector has eight sign weights. -/
@[rep_depth thermo]
theorem spin44_even_half_spinor_weight_count :
    (Finset.univ.filter fun eps : Fin 4 → Bool => EvenMinus eps).card = 8 :=
  evenMinus_card

/-- The finite `D₄` odd half-spinor sector has eight sign weights. -/
@[rep_depth thermo]
theorem spin44_odd_half_spinor_weight_count :
    (Finset.univ.filter fun eps : Fin 4 → Bool => OddMinus eps).card = 8 :=
  oddMinus_card

/-- Count-level balanced `D₄` half-spinor shadow: `8 + 8 = 16`. -/
@[rep_depth thermo]
theorem spin44_balanced_half_spinor_total_count :
    (Finset.univ.filter fun eps : Fin 4 → Bool => EvenMinus eps).card
      + (Finset.univ.filter fun eps : Fin 4 → Bool => OddMinus eps).card = 16 := by
  rw [spin44_even_half_spinor_weight_count, spin44_odd_half_spinor_weight_count]

end Cl44SignatureResidue
