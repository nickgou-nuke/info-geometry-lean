import InfoGeometry.Algebra.EulerLaurentDerivation
import InfoGeometry.Canonical.FiniteSuperchargeIndex
import InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy

/-!
# Finite unit-charge divisor / supercharge bridge

Zeros and poles are represented by two finite signed mark families.  The
resulting divisor index is compared with the index of the concrete finite
zero-supercharge complex.  This is a unit-charge finite theorem only; no
analytic order map or zeta divisor is introduced.
-/

namespace InfoGeometry.Canonical.FiniteDivisorWittenBridge

noncomputable section

open InfoGeometry.Algebra.EulerLaurentDerivation
open InfoGeometry.Canonical.FiniteSuperchargeIndex

abbrev SignedMarks (m n : ℕ) := Fin m ⊕ Fin n

def signedUnitOrder {m n : ℕ} : SignedMarks m n → ℤ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

theorem signedUnitOrder_divisorIndex (m n : ℕ) :
    divisorIndex (Finset.univ : Finset (SignedMarks m n)) signedUnitOrder =
      (m : ℤ) - n := by
  simp [divisorIndex, signedUnitOrder]
  ring

theorem signedUnitOrder_wittenIndex (m n : ℕ) :
    wittenIndex (zeroSupercharge m n) =
      divisorIndex (Finset.univ : Finset (SignedMarks m n)) signedUnitOrder := by
  rw [zeroSupercharge_wittenIndex, signedUnitOrder_divisorIndex]

/-- The finite divisor-kernel realization and the concrete zero-supercharge
    realization compute the same signed unit-charge index. -/
theorem signedUnitOrder_kernelIndex_eq_wittenIndex (m n : ℕ) :
    InfoGeometry.Arithmetic.IndexTheorem.finiteKernelIndex
        (InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy.divisorKernelComplex
          (signedUnitOrder (m := m) (n := n))) =
      wittenIndex (zeroSupercharge m n) := by
  rw [InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy.divisor_kernel_index_eq_divisor_index,
    zeroSupercharge_wittenIndex]
  change (∑ a : SignedMarks m n, signedUnitOrder a) = (m : ℤ) - n
  exact signedUnitOrder_divisorIndex m n

theorem divisorIndex_union_of_disjoint
    {ι : Type*} [DecidableEq ι]
    (A B : Finset ι) (hAB : Disjoint A B) (order : ι → ℤ) :
    divisorIndex (A ∪ B) order =
      divisorIndex A order + divisorIndex B order := by
  simp [divisorIndex, Finset.sum_union hAB]

end

end InfoGeometry.Canonical.FiniteDivisorWittenBridge
