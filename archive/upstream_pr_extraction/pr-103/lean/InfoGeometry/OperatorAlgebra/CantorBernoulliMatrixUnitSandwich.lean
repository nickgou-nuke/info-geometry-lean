import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge

/-!
# Matrix-unit coefficient sandwich on the Bernoulli boundary

This file isolates the finite coefficient-recovery kernel.  It uses only the
already proved equal-length Cuntz cancellation and matrix-unit multiplication;
no finite enumeration or analytic completion is involved.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.CantorBernoulliMatrixUnitSandwich

open InfoGeometry.OperatorAlgebra.CantorBernoulliCuntzOperatorTreeBridge
open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.CantorBernoulliL2OperatorTransport

theorem bitWordUnit_sandwich
    (n : ℕ) (u a b v : BitWord n) :
    (operatorWordDag (List.ofFn u)).comp
        ((bitWordUnit n a b).comp (operatorWord (List.ofFn v))) =
      if u = a then
        if b = v then ContinuousLinearMap.id ℂ L2Boundary else 0
      else 0 := by
  change
    (operatorMatrixUnit [] (List.ofFn u)).comp
        ((operatorMatrixUnit (List.ofFn a) (List.ofFn b)).comp
          (operatorMatrixUnit (List.ofFn v) [])) = _
  rw [operatorMatrixUnit_mul (by simp only [List.length_ofFn])]
  by_cases hua : u = a
  · subst a
    simp only [if_true]
    by_cases hbv : b = v
    · subst v
      simp only [if_true]
      rw [operatorMatrixUnit_mul (by simp only [List.length_ofFn, List.length_nil])]
      simp [operatorMatrixUnit]
    · simp [hbv]
  · by_cases hbv : b = v
    · subst v
      have hlist : List.ofFn u ≠ List.ofFn a := by
        intro h
        exact hua (List.ofFn_injective h)
      simp only [if_true, eq_self]
      rw [operatorMatrixUnit_mul (by simp only [List.length_ofFn])]
      simp [hua, hlist]
    · simp [hbv]

end InfoGeometry.OperatorAlgebra.CantorBernoulliMatrixUnitSandwich
