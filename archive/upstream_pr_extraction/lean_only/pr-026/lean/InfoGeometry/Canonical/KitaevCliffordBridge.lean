import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

namespace KitaevCliffordBridge

variable {A : Type*} [Ring A]

/-- 1. Uncoupled Kitaev Boundary Majorana Pair (γ_L, γ_R) -/
structure BoundaryMajoranaPair (A : Type*) [Ring A] where
  gamma_L : A
  gamma_R : A
  h_L_sq  : gamma_L * gamma_L = 1
  h_R_sq  : gamma_R * gamma_R = 1
  h_anticomm : gamma_L * gamma_R + gamma_R * gamma_L = 0

/-- 2. Embedding into Split-Quaternion Generators:
    l = γ_L        (l² = +1)
    i = γ_L * γ_R  (i² = -1) -/
def toSplitL (p : BoundaryMajoranaPair A) : A := p.gamma_L
def toSplitI (p : BoundaryMajoranaPair A) : A := p.gamma_L * p.gamma_R

/-- Split Generator Square (l² = 1) -/
theorem split_l_sq (p : BoundaryMajoranaPair A) :
    toSplitL p * toSplitL p = 1 := p.h_L_sq

/-- Complex Generator Square (i² = -1) -/
theorem split_i_sq (p : BoundaryMajoranaPair A) :
    toSplitI p * toSplitI p = -1 := by
  dsimp [toSplitI]
  have h_swap : p.gamma_R * p.gamma_L = - (p.gamma_L * p.gamma_R) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact p.h_anticomm)
  calc (p.gamma_L * p.gamma_R) * (p.gamma_L * p.gamma_R)
    _ = p.gamma_L * (p.gamma_R * p.gamma_L) * p.gamma_R := by noncomm_ring
    _ = p.gamma_L * (- (p.gamma_L * p.gamma_R)) * p.gamma_R := by rw [h_swap]
    _ = - (p.gamma_L * p.gamma_L) * (p.gamma_R * p.gamma_R) := by noncomm_ring
    _ = - (1 : A) * 1 := by rw [p.h_L_sq, p.h_R_sq]
    _ = -1 := by noncomm_ring

/-- Anticommutativity of i and l (i*l + l*i = 0) -/
theorem split_anticomm (p : BoundaryMajoranaPair A) :
    toSplitI p * toSplitL p + toSplitL p * toSplitI p = 0 := by
  dsimp [toSplitI, toSplitL]
  have h_swap : p.gamma_R * p.gamma_L = - (p.gamma_L * p.gamma_R) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact p.h_anticomm)
  calc (p.gamma_L * p.gamma_R) * p.gamma_L + p.gamma_L * (p.gamma_L * p.gamma_R)
    _ = p.gamma_L * (p.gamma_R * p.gamma_L) + (p.gamma_L * p.gamma_L) * p.gamma_R := by noncomm_ring
    _ = p.gamma_L * (- (p.gamma_L * p.gamma_R)) + 1 * p.gamma_R := by rw [h_swap, p.h_L_sq]
    _ = - (p.gamma_L * p.gamma_L) * p.gamma_R + p.gamma_R := by noncomm_ring
    _ = - 1 * p.gamma_R + p.gamma_R := by rw [p.h_L_sq]
    _ = 0 := by noncomm_ring

/-- 3. Nilpotent Parabolic Horizon Generator ε = l + i -/
def toNilpotentEps (p : BoundaryMajoranaPair A) : A :=
  toSplitL p + toSplitI p

/-- Boundary Horizon Nilpotency (ε² = 0) -/
theorem horizon_nilpotent (p : BoundaryMajoranaPair A) :
    toNilpotentEps p * toNilpotentEps p = 0 := by
  dsimp [toNilpotentEps]
  have h_l2 := split_l_sq p
  have h_i2 := split_i_sq p
  have h_anti := split_anticomm p
  calc (toSplitL p + toSplitI p) * (toSplitL p + toSplitI p)
    _ = toSplitL p * toSplitL p + (toSplitI p * toSplitL p + toSplitL p * toSplitI p) + toSplitI p * toSplitI p := by noncomm_ring
    _ = 1 + 0 + (-1) := by rw [h_l2, h_anti, h_i2]
    _ = 0 := by abel

end KitaevCliffordBridge
