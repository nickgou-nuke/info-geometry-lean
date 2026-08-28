import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Exceptional.CircularSplitOctonionContactLift

namespace InfoGeometry.Exceptional.Freudenthal

/-!
# Freudenthal Heisenberg Supercharge Readback

This module connects the canonical anticommutation relations (CAR) of the circular chiral
basis with the macroscopic Lie bracket in the contact lanes $\mathfrak{g}_{-1}$ and $\mathfrak{g}_{+1}$.

Architectural Boundary:
This formalizes an ordinary Lie algebra representation where the symplectic form acts as the
bridge from the microscopic operator envelope to the macroscopic Heisenberg Lie bracket,
generating the extreme poles $E_-$ and $E_+$.
-/

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable (phi : ContactAtom → L)

/-- READBACK THEOREM: The bracket of Q_i⁺ and Q_j⁻ in 𝔤₋₁ yields 2 δ_ij E₋ -/
theorem bracket_minusOne_supercharges
    (omega_chiral : CircularChargeAtom → CircularChargeAtom → R)
    (h_omega_roots : ∀ i j : Fin 3,
      omega_chiral (.plusRoot i) (.minusRoot j) = if i = j then 1 else 0)
    (h_bracket_minus_minus : ∀ a b : CircularChargeAtom,
      ⁅phi (.minusOne a), phi (.minusOne b)⁆ =
      (2 : R) • (omega_chiral a b) • phi .eMinus)
    (i j : Fin 3) :
    ⁅phi (.minusOne (.plusRoot i)),
     phi (.minusOne (.minusRoot j))⁆ =
    if i = j then (2 : R) • phi .eMinus else 0 := by
  rw [h_bracket_minus_minus, h_omega_roots i j]
  split_ifs with h
  · simp only [one_smul]
  · simp only [zero_smul, smul_zero]

/-- READBACK THEOREM: The bracket of Q_i⁺ and Q_j⁻ in 𝔤₊₁ yields 2 δ_ij E₊ -/
theorem bracket_plusOne_supercharges
    (omega_chiral : CircularChargeAtom → CircularChargeAtom → R)
    (h_omega_roots : ∀ i j : Fin 3,
      omega_chiral (.plusRoot i) (.minusRoot j) = if i = j then 1 else 0)
    (h_bracket_plus_plus : ∀ a b : CircularChargeAtom,
      ⁅phi (.plusOne a), phi (.plusOne b)⁆ =
      (2 : R) • (omega_chiral a b) • phi .ePlus)
    (i j : Fin 3) :
    ⁅phi (.plusOne (.plusRoot i)),
     phi (.plusOne (.minusRoot j))⁆ =
    if i = j then (2 : R) • phi .ePlus else 0 := by
  rw [h_bracket_plus_plus, h_omega_roots i j]
  split_ifs with h
  · simp only [one_smul]
  · simp only [zero_smul, smul_zero]

end InfoGeometry.Exceptional.Freudenthal
