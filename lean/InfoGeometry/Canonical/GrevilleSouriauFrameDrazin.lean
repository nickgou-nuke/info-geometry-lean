import Mathlib
import InfoGeometry.Canonical.Drazin

/-!
# Greville 1973: Souriau--Frame algorithm and Drazin pseudoinverse

Source digest:

T. N. E. Greville, "The Souriau--Frame Algorithm and the Drazin
Pseudoinverse", Linear Algebra and Its Applications 6, 205--208 (1973).

The paper shows that the Souriau--Frame/Faddeev--LeVerrier coefficient
sequence does not merely produce the ordinary inverse in the nonsingular case:
for a singular square matrix it produces the Drazin pseudoinverse.  If `r` is
the first index with `B_r = 0`, `s` is the last index with `p_s ≠ 0`, and
`k = r - s`, then Greville's formula is

`X = p_s^(-k-1) A^k B_(s-1)^(k+1)`.

The Lean-native part below formalizes a strict exact packet with `s = 1`,
`r = 3`, `k = 2`.  The packet keeps the nontrivial nilpotent zero-root block,
checks the Souriau--Frame recurrence, proves the Greville formula gives the
Drazin inverse at index `2`, and checks the same formula after a concrete
`GL_3(Q)` conjugation.

The file intentionally does not formalize numerical stability or a general
rank/basis algorithm for arbitrary fields.
-/

noncomputable section

namespace InfoGeometry.Canonical.GrevilleSouriauFrameDrazin

open InfoGeometry.Canonical

abbrev Mat3 (R : Type*) := Matrix (Fin 3) (Fin 3) R

/-! ## Exact `k = 2` Souriau--Frame packet -/

/-- A matrix with a size-two zero Jordan block and a regular eigenvalue `2`. -/
def grevilleA : Mat3 ℚ :=
  !![0, 1, 0;
     0, 0, 0;
     0, 0, 2]

/-- `B₀ = I`. -/
def grevilleB0 : Mat3 ℚ :=
  1

/-- `p₁ = trace(A B₀) = 2`. -/
def grevilleP1 : ℚ :=
  2

/-- `B₁ = A B₀ - p₁ I`. -/
def grevilleB1 : Mat3 ℚ :=
  grevilleA * grevilleB0 - grevilleP1 • (1 : Mat3 ℚ)

/-- `p₂ = 1/2 trace(A B₁) = 0`. -/
def grevilleP2 : ℚ :=
  0

/-- `B₂ = A B₁ - p₂ I`. -/
def grevilleB2 : Mat3 ℚ :=
  grevilleA * grevilleB1 - grevilleP2 • (1 : Mat3 ℚ)

/-- `p₃ = 1/3 trace(A B₂) = 0`. -/
def grevilleP3 : ℚ :=
  0

/-- `B₃ = A B₂ - p₃ I = 0`; this is the first zero in the packet. -/
def grevilleB3 : Mat3 ℚ :=
  grevilleA * grevilleB2 - grevilleP3 • (1 : Mat3 ℚ)

/-- The first Souriau--Frame scalar is the trace readout. -/
theorem greville_trace_p1 :
    Matrix.trace (grevilleA * grevilleB0) = grevilleP1 := by
  native_decide

/-- The second Souriau--Frame scalar is zero in this packet. -/
theorem greville_trace_p2 :
    (1 / 2 : ℚ) * Matrix.trace (grevilleA * grevilleB1) = grevilleP2 := by
  native_decide

/-- The third Souriau--Frame scalar is zero in this packet. -/
theorem greville_trace_p3 :
    (1 / 3 : ℚ) * Matrix.trace (grevilleA * grevilleB2) = grevilleP3 := by
  native_decide

/-- The packet has `B₃ = 0`. -/
theorem greville_B3_eq_zero :
    grevilleB3 = 0 := by
  native_decide

/-- The packet has `B₂ ≠ 0`, so the first zero is not earlier than `3`. -/
theorem greville_B2_ne_zero :
    grevilleB2 ≠ 0 := by
  native_decide

/-- The characteristic-polynomial relation in the packet: `A³ = 2 A²`. -/
theorem greville_A_cube_eq_two_smul_A_sq :
    grevilleA ^ 3 = (2 : ℚ) • (grevilleA ^ 2) := by
  native_decide

/-- Greville's formula with `s = 1`, `k = 2`, `B₀ = I`, and `p₁ = 2`. -/
def grevilleFormulaCandidate : Mat3 ℚ :=
  ((grevilleP1) ^ 3)⁻¹ • (grevilleA ^ 2 * grevilleB0 ^ 3)

/-- Expected Drazin inverse: zero on the nilpotent block and `1/2` on the regular lane. -/
def grevilleExpectedDrazin : Mat3 ℚ :=
  !![0, 0, 0;
     0, 0, 0;
     0, 0, 1 / 2]

/-- Greville's formula produces the expected Drazin inverse. -/
theorem greville_formula_candidate_eq_expected :
    grevilleFormulaCandidate = grevilleExpectedDrazin := by
  native_decide

/-- Greville's formula satisfies the Drazin laws at index `2`. -/
theorem greville_formula_candidate_isDrazinInverse :
    Drazin.IsDrazinInverse grevilleA grevilleFormulaCandidate 2 := by
  refine Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide

/-- The regular Drazin projector selected by Greville's formula. -/
theorem greville_regular_projector_readout :
    Drazin.IsDrazinInverse.projection grevilleA grevilleFormulaCandidate =
      !![0, 0, 0;
         0, 0, 0;
         0, 0, 1] := by
  native_decide

/-- The nilpotent zero-root projector selected by Greville's formula. -/
theorem greville_nilpotent_projector_readout :
    Drazin.IsDrazinInverse.complementaryProjection grevilleA grevilleFormulaCandidate =
      !![1, 0, 0;
         0, 1, 0;
         0, 0, 0] := by
  native_decide

/-! ## Strict finite `GL₃(Q)` conjugation readout -/

/-- A permutation matrix used as a concrete `GL₃(Q)` representative. -/
def grevillePermutation : Mat3 ℚ :=
  !![0, 0, 1;
     0, 1, 0;
     1, 0, 0]

/-- The permutation representative is its own inverse. -/
theorem grevillePermutation_sq_eq_one :
    grevillePermutation * grevillePermutation = 1 := by
  native_decide

/-- The permutation as a strict unit of the matrix algebra. -/
def grevillePermutationUnit : (Mat3 ℚ)ˣ where
  val := grevillePermutation
  inv := grevillePermutation
  val_inv := grevillePermutation_sq_eq_one
  inv_val := grevillePermutation_sq_eq_one

/-- Unit conjugation on the matrix algebra. -/
def unitConj (u : (Mat3 ℚ)ˣ) (A : Mat3 ℚ) : Mat3 ℚ :=
  (u : Mat3 ℚ) * A * ((u⁻¹ : (Mat3 ℚ)ˣ) : Mat3 ℚ)

/-- The conjugated Greville candidate is the Drazin inverse of the conjugated matrix. -/
theorem greville_conjugated_formula_isDrazinInverse :
    Drazin.IsDrazinInverse
      (unitConj grevillePermutationUnit grevilleA)
      (unitConj grevillePermutationUnit grevilleFormulaCandidate)
      2 := by
  refine Drazin.IsDrazinInverse.mk ?_ ?_ ?_
  · native_decide
  · native_decide
  · native_decide

end InfoGeometry.Canonical.GrevilleSouriauFrameDrazin
