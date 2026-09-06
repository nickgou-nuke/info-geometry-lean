import Mathlib
import proofs.SpectralSquashCayleyDKT

/-!
# q-deformed super-Cuntz regularization

Finite theorem-honest bridge between the already-proved chiral Krein/Cayley
spine and the proposed q-deformed supergraded Cuntz interpretation.

Proved here:
* the finite `η=N₊-N₋` operator is exactly the superparity operator;
* `η²=1` and `η†=η`;
* the finite supertrace is `Tr(ηX)=X₀₀-X₁₁`;
* the q-hyperbolic integer notation is tied definitionally to `sinh` ratios;
* the Cayley stage is unitary also for the superparity/DKT adjoint.
-/

noncomputable section

namespace QSuperCuntzRegularization

open Matrix
open scoped BigOperators

abbrev M2C := SpectralSquashCayleyDKT.M2C

/-- Two-sector supergrading. -/
inductive SuperParity where
  | bosonic
  | fermionic
  deriving DecidableEq, Repr, Inhabited

open SuperParity

/-- Sign of the two supersectors. -/
def paritySign : SuperParity → ℂ
  | bosonic => 1
  | fermionic => -1

/-- Bosonic projection. -/
def PB : M2C := SpectralSquashCayleyDKT.Nplus

/-- Fermionic projection. -/
def PF : M2C := SpectralSquashCayleyDKT.Nminus

/-- Finite superparity operator `(-1)^F`. -/
def superParityOperator : M2C := PB - PF

/-- The superparity operator is the already-proved endogenous Krein signature. -/
theorem superParity_eq_eta : superParityOperator = SpectralSquashCayleyDKT.eta := by
  rw [superParityOperator, PB, PF]
  exact SpectralSquashCayleyDKT.eta_eq_projection_difference.symm

/-- The finite superparity operator is an involution. -/
theorem superParity_sq : superParityOperator * superParityOperator = 1 := by
  rw [superParity_eq_eta]
  exact SpectralSquashCayleyDKT.eta_sq

/-- The finite superparity operator is self-adjoint. -/
theorem superParity_selfadjoint : star superParityOperator = superParityOperator := by
  rw [superParity_eq_eta]
  exact SpectralSquashCayleyDKT.eta_selfadjoint

/-- Finite supertrace: `STr(X)=Tr((-1)^F X)`. -/
def supertrace (X : M2C) : ℂ := Matrix.trace (superParityOperator * X)

/-- In `2×2`, the supertrace is the bosonic diagonal entry minus the fermionic
one. -/
theorem supertrace_apply (X : M2C) : supertrace X = X 0 0 - X 1 1 := by
  simp [supertrace, superParityOperator, PB, PF, SpectralSquashCayleyDKT.Nplus,
    SpectralSquashCayleyDKT.Nminus, Matrix.trace_fin_two, Matrix.vecMul,
    Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg]

/-- Supertrace of the identity detects the balanced `(1|1)` finite sector. -/
theorem supertrace_one : supertrace (1 : M2C) = 0 := by
  simp [supertrace_apply]

/-- Supertrace of the parity operator counts bosons plus fermions after parity
insertion. -/
theorem supertrace_superParity : supertrace superParityOperator = 2 := by
  simp [supertrace_apply, superParityOperator, PB, PF, SpectralSquashCayleyDKT.Nplus,
    SpectralSquashCayleyDKT.Nminus]
  norm_num

/-- Algebraic q-super-commutator expression.  This is a finite expression, not a
claim that the concrete `2×2` matrices faithfully realize a full q-Cuntz
superalgebra. -/
def qSuperCommutator (q : ℂ) (parity : SuperParity) (A B : M2C) : M2C :=
  match parity with
  | bosonic => A * B - q • (B * A)
  | fermionic => A * B + q • (B * A)

/-- At `q=0`, the q-super-commutator forgets the exchange correction. -/
theorem qSuperCommutator_zero (p : SuperParity) (A B : M2C) :
    qSuperCommutator 0 p A B = A * B := by
  cases p <;> simp [qSuperCommutator]

/-- Hyperbolic q-integer notation for `q=e^θ`: `[n]_q=sinh(nθ)/sinh θ`. -/
def qHyperbolicInteger (theta : ℝ) (n : ℕ) : ℝ := Real.sinh (n * theta) / Real.sinh theta

/-- The q-hyperbolic integer is definitionally the stated `sinh` ratio. -/
theorem qHyperbolicInteger_eq (theta : ℝ) (n : ℕ) :
    qHyperbolicInteger theta n = Real.sinh (n * theta) / Real.sinh theta := rfl

/-- The Cayley stage remains unitary when the DKT/Krein adjoint is read as the
finite superparity adjoint. -/
theorem cayley_superparity_unitary (lam : ℝ) :
    SpectralSquashCayleyDKT.cayleyStage lam *
      SpectralSquashCayleyDKT.dktAdjoint (SpectralSquashCayleyDKT.cayleyStage lam) = 1 :=
  SpectralSquashCayleyDKT.cayleyStage_dkt_unitary lam

end QSuperCuntzRegularization
