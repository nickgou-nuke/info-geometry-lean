import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Conditional closure for a mixed bivector pair

The commuting and anticommuting contracts are intentionally separate.  The
former is the Cartan/loxodromic lane; the latter is the local split-Clifford
lane.  No concrete gamma pair is assigned to either contract here.
-/

namespace InfoGeometry.Clifford.BivectorPairConditionalClosure

variable {A : Type*} [Ring A]

theorem commuting_pair_product {B R : A} (h : B * R = R * B) :
    (B * R) * (B * R) = (B * B) * (R * R) := by
  calc
    (B * R) * (B * R) = B * (R * B) * R := by noncomm_ring
    _ = B * (B * R) * R := by rw [h]
    _ = (B * B) * (R * R) := by noncomm_ring

theorem anticommuting_pair_product {B R : A}
    (h : B * R = -(R * B)) :
    (B * R) * (B * R) = -((B * B) * (R * R)) := by
  calc
    (B * R) * (B * R) = B * (R * B) * R := by simp only [mul_assoc]
    _ = B * (-(B * R)) * R := by rw [show R * B = -(B * R) by
      have := congrArg Neg.neg h
      simpa using this.symm]
    _ = -((B * B) * (R * R)) := by noncomm_ring

end InfoGeometry.Clifford.BivectorPairConditionalClosure
