import InfoGeometry.Clifford.Cl55FiniteCommutingRotorAction
import InfoGeometry.Clifford.Cl55RoPESplitTorusBridge

/-! Native specialization of the generic rank-two rotor closure.

The statement is intentionally finite and concrete: it packages the already
proved disjoint planes `(0,1)` and `(2,3)`, without asserting maximality. -/

noncomputable section

namespace InfoGeometry.Clifford.Cl55NativeFiniteRotorAction

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.Cl55RoPESplitTorusBridge
open InfoGeometry.Clifford.FiniteCommutingRotorAction

def nativeRankTwoRotor (s t : ℝ) : Cl55 :=
  bivectorRotor55 0 1 s * bivectorRotor55 2 3 t

theorem nativeRankTwoRotor_add (s₁ s₂ t₁ t₂ : ℝ) :
    nativeRankTwoRotor (s₁ + s₂) (t₁ + t₂) =
      nativeRankTwoRotor s₁ t₁ * nativeRankTwoRotor s₂ t₂ := by
  unfold nativeRankTwoRotor
  simpa [bivectorRotor55, rankTwoRotor, rotor] using
    (rankTwoRotor_add
      (ropeBivector55 0 1) (ropeBivector55 2 3)
      (ropeBivector55_sq 0 1 (by decide))
      (ropeBivector55_sq 2 3 (by decide))
      disjoint_bivector_commute_01_23 s₁ s₂ t₁ t₂)

end InfoGeometry.Clifford.Cl55NativeFiniteRotorAction
