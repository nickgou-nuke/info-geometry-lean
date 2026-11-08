import Mathlib.Algebra.Algebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Five-graded split-weight socket

This module records a finite algebraic socket for the split-idempotent
`E`/`Ebar` weight decomposition used to refine coarse
`zero/null/generic` strata.

The proved content is deliberately local:

* two orthogonal split idempotents with normalization `E² = 2E`, `Ebar² = 2Ebar`;
* a five-element weight index;
* a lightweight record of five graded coordinates;
* extraction lemmas saying that, from a supplied decomposition
  `a = a₊ • E + a₋ • Ebar`, right multiplication by `E` or `Ebar` isolates the
  corresponding component up to the normalization factor `2`.

Boundary: this is not a proof of uniqueness of the decomposition, not a full
`J₂(O_s)` construction, not a full `Spin(5,5)`/`Pin(5,5)` orbit
classification, not a Witten-index theorem, and not a global super-TKK closure
theorem.
-/

namespace InfoGeometry.Algebra.FiveGradedTKK

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]

/-- Orthogonal split idempotents with the Fioresi-style normalization
`E² = 2E`, `Ebar² = 2Ebar`. -/
abbrev SplitIdempotents (E Ebar : A) : Prop :=
  E * Ebar = 0 ∧ Ebar * E = 0 ∧
    E * E = (2 : K) • E ∧ Ebar * Ebar = (2 : K) • Ebar

/-- Five conformal/TKK-style weight labels. -/
inductive Weight5 where
  | neg_two
  | neg_one
  | zero
  | pos_one
  | pos_two
  deriving DecidableEq, Repr

/-- Integer readout for the five weights. -/
def Weight5.toInt : Weight5 → ℤ
  | .neg_two => -2
  | .neg_one => -1
  | .zero => 0
  | .pos_one => 1
  | .pos_two => 2

@[simp] theorem Weight5.toInt_neg_two : Weight5.toInt Weight5.neg_two = -2 := rfl
@[simp] theorem Weight5.toInt_neg_one : Weight5.toInt Weight5.neg_one = -1 := rfl
@[simp] theorem Weight5.toInt_zero : Weight5.toInt Weight5.zero = 0 := rfl
@[simp] theorem Weight5.toInt_pos_one : Weight5.toInt Weight5.pos_one = 1 := rfl
@[simp] theorem Weight5.toInt_pos_two : Weight5.toInt Weight5.pos_two = 2 := rfl

/-- A lightweight five-graded coordinate packet for a split `J₂`-style element.

The diagonal scalar coordinates are represented over `K`; the `±1` slots are
coefficient coordinates for the supplied split idempotents. -/
structure FiveGradedDecomposition (K A : Type*) where
  g_neg_two : K
  g_neg_one : K
  g_zero : K
  g_pos_one : K
  g_pos_two : K

variable (K A)

/-- Reconstruct the diagonal coordinates and off-diagonal split component. -/
def reconstruct (E Ebar : A) (g : FiveGradedDecomposition K A) : K × K × A :=
  let α := g.g_pos_two
  let β := g.g_neg_two
  let Z := g.g_pos_one • E + g.g_neg_one • Ebar
  (α, β, Z)

variable {K A}

/-- Weight `+1` coefficient is zero. -/
def NoPosOneWeight (g : FiveGradedDecomposition K A) : Prop :=
  g.g_pos_one = 0

/-- Weight `-1` coefficient is zero. -/
def NoNegOneWeight (g : FiveGradedDecomposition K A) : Prop :=
  g.g_neg_one = 0

/-- The element is supported only in the `+1` split-idempotent direction among
its off-diagonal coordinates. -/
def PosOneOnly (g : FiveGradedDecomposition K A) : Prop :=
  g.g_neg_one = 0

/-- The element is supported only in the `-1` split-idempotent direction among
its off-diagonal coordinates. -/
def NegOneOnly (g : FiveGradedDecomposition K A) : Prop :=
  g.g_pos_one = 0

/-- A coarse null-sector refinement by split weight direction.  This is only a
coordinate tag, not a group orbit classification. -/
inductive NullWeightSector (g : FiveGradedDecomposition K A) : Prop where
  | posOne : PosOneOnly g → NullWeightSector g
  | negOne : NegOneOnly g → NullWeightSector g
  | mixed : g.g_pos_one ≠ 0 → g.g_neg_one ≠ 0 → NullWeightSector g

/-- Right multiplication by `Ebar` extracts the `Ebar` coefficient from a
supplied `E/Ebar` decomposition, up to the normalization factor `2`. -/
theorem right_mul_Ebar_of_split
    (E Ebar : A) (h : SplitIdempotents (K := K) E Ebar)
    (a : A) (a_plus a_minus : K)
    (h_decomp : a = a_plus • E + a_minus • Ebar) :
    a * Ebar = (2 * a_minus) • Ebar := by
  calc
    a * Ebar = (a_plus • E + a_minus • Ebar) * Ebar := by rw [h_decomp]
    _ = (a_plus • E) * Ebar + (a_minus • Ebar) * Ebar := by rw [add_mul]
    _ = a_plus • (E * Ebar) + a_minus • (Ebar * Ebar) := by
          rw [smul_mul_assoc, smul_mul_assoc]
    _ = a_plus • (0 : A) + a_minus • ((2 : K) • Ebar) := by
          rw [h.1, h.2.2.2]
    _ = (2 * a_minus) • Ebar := by
          simp [smul_smul, mul_comm]

/-- Right multiplication by `E` extracts the `E` coefficient from a supplied
`E/Ebar` decomposition, up to the normalization factor `2`. -/
theorem right_mul_E_of_split
    (E Ebar : A) (h : SplitIdempotents (K := K) E Ebar)
    (a : A) (a_plus a_minus : K)
    (h_decomp : a = a_plus • E + a_minus • Ebar) :
    a * E = (2 * a_plus) • E := by
  calc
    a * E = (a_plus • E + a_minus • Ebar) * E := by rw [h_decomp]
    _ = (a_plus • E) * E + (a_minus • Ebar) * E := by rw [add_mul]
    _ = a_plus • (E * E) + a_minus • (Ebar * E) := by
          rw [smul_mul_assoc, smul_mul_assoc]
    _ = a_plus • ((2 : K) • E) + a_minus • (0 : A) := by
          rw [h.2.2.1, h.2.1]
    _ = (2 * a_plus) • E := by
          simp [smul_smul, mul_comm]

/-- The two projection formulae packaged together. -/
theorem split_idempotent_projection_packet
    (E Ebar : A) (h : SplitIdempotents (K := K) E Ebar)
    (a : A) (a_plus a_minus : K)
    (h_decomp : a = a_plus • E + a_minus • Ebar) :
    a * E = (2 * a_plus) • E ∧ a * Ebar = (2 * a_minus) • Ebar :=
  ⟨right_mul_E_of_split E Ebar h a a_plus a_minus h_decomp,
    right_mul_Ebar_of_split E Ebar h a a_plus a_minus h_decomp⟩

end InfoGeometry.Algebra.FiveGradedTKK
