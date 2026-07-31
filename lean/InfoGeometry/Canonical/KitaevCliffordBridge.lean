import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

namespace KitaevCliffordBridge

variable {A : Type*} [Ring A]

/-- 1. Uncoupled Kitaev Boundary Majorana Pair (γ_L, γ_R) -/
structure BoundaryMajoranaPair (A : Type*) [Ring A] where
  gamma_L : A
  gamma_R : A

/-- 2. Embedding into Split-Quaternion Generators:
    l = γ_L        (l² = +1)
    i = γ_L * γ_R  (i² = -1) -/
def toSplitL (p : BoundaryMajoranaPair A) : A := p.gamma_L
def toSplitI (p : BoundaryMajoranaPair A) : A := p.gamma_L * p.gamma_R

/-- Split Generator Square (l² = 1) -/
theorem split_l_sq (p : BoundaryMajoranaPair A)
    (hL : p.gamma_L * p.gamma_L = 1) :
    toSplitL p * toSplitL p = 1 := hL

/-- Complex Generator Square (i² = -1) -/
theorem split_i_sq (p : BoundaryMajoranaPair A)
    (hL : p.gamma_L * p.gamma_L = 1)
    (hR : p.gamma_R * p.gamma_R = 1)
    (hanti : p.gamma_L * p.gamma_R + p.gamma_R * p.gamma_L = 0) :
    toSplitI p * toSplitI p = -1 := by
  dsimp [toSplitI]
  have h_swap : p.gamma_R * p.gamma_L = - (p.gamma_L * p.gamma_R) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hanti)
  calc (p.gamma_L * p.gamma_R) * (p.gamma_L * p.gamma_R)
    _ = p.gamma_L * (p.gamma_R * p.gamma_L) * p.gamma_R := by noncomm_ring
    _ = p.gamma_L * (- (p.gamma_L * p.gamma_R)) * p.gamma_R := by rw [h_swap]
    _ = - (p.gamma_L * p.gamma_L) * (p.gamma_R * p.gamma_R) := by noncomm_ring
    _ = - (1 : A) * 1 := by rw [hL, hR]
    _ = -1 := by noncomm_ring

/-- Anticommutativity of i and l (i*l + l*i = 0) -/
theorem split_anticomm (p : BoundaryMajoranaPair A)
    (hL : p.gamma_L * p.gamma_L = 1)
    (hanti : p.gamma_L * p.gamma_R + p.gamma_R * p.gamma_L = 0) :
    toSplitI p * toSplitL p + toSplitL p * toSplitI p = 0 := by
  dsimp [toSplitI, toSplitL]
  have h_swap : p.gamma_R * p.gamma_L = - (p.gamma_L * p.gamma_R) :=
    eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hanti)
  calc (p.gamma_L * p.gamma_R) * p.gamma_L + p.gamma_L * (p.gamma_L * p.gamma_R)
    _ = p.gamma_L * (p.gamma_R * p.gamma_L) + (p.gamma_L * p.gamma_L) * p.gamma_R := by noncomm_ring
    _ = p.gamma_L * (- (p.gamma_L * p.gamma_R)) + 1 * p.gamma_R := by rw [h_swap, hL]
    _ = - (p.gamma_L * p.gamma_L) * p.gamma_R + p.gamma_R := by noncomm_ring
    _ = - 1 * p.gamma_R + p.gamma_R := by rw [hL]
    _ = 0 := by noncomm_ring

/-- 3. Nilpotent Parabolic Horizon Generator ε = l + i -/
def toNilpotentEps (p : BoundaryMajoranaPair A) : A :=
  toSplitL p + toSplitI p

/-- Boundary Horizon Nilpotency (ε² = 0) -/
theorem horizon_nilpotent (p : BoundaryMajoranaPair A)
    (hL : p.gamma_L * p.gamma_L = 1)
    (hR : p.gamma_R * p.gamma_R = 1)
    (hanti : p.gamma_L * p.gamma_R + p.gamma_R * p.gamma_L = 0) :
    toNilpotentEps p * toNilpotentEps p = 0 := by
  dsimp [toNilpotentEps]
  have h_l2 := split_l_sq p hL
  have h_i2 := split_i_sq p hL hR hanti
  have h_anti := split_anticomm p hL hanti
  calc (toSplitL p + toSplitI p) * (toSplitL p + toSplitI p)
    _ = toSplitL p * toSplitL p + (toSplitI p * toSplitL p + toSplitL p * toSplitI p) + toSplitI p * toSplitI p := by noncomm_ring
    _ = 1 + 0 + (-1) := by rw [h_l2, h_anti, h_i2]
    _ = 0 := by abel

end KitaevCliffordBridge
