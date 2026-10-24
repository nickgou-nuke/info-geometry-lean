/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Streaming.WeakValueMultiplication

/-! The weak functional is a character on the actual preselected-line
stabilizer subalgebra, including singular endomorphisms. -/
noncomputable section
namespace InfoGeometry.Streaming.TwoBoundaryDyadCompression
open FiniteTwoBoundaryWeakFunctional
variable {ι : Type*} [Fintype ι]

def preLineAlgebra (p : RegularBoundaryPair ι) : Subalgebra ℂ (Operator ι) where
  carrier := {A | ∀ x ∈ (ℂ ∙ p.pre), A x ∈ (ℂ ∙ p.pre)}
  zero_mem' := by simp
  one_mem' := by intro x hx; exact hx
  add_mem' := by intro A B hA hB x hx; exact Submodule.add_mem _ (hA x hx) (hB x hx)
  mul_mem' := by intro A B hA hB x hx; exact hA _ (hB x hx)
  algebraMap_mem' := by
    intro c x hx
    change c • x ∈ (ℂ ∙ p.pre)
    exact Submodule.smul_mem _ c hx

theorem mem_preLineAlgebra_iff (p : RegularBoundaryPair ι) (B : Operator ι) :
    B ∈ preLineAlgebra p ↔ B p.pre = weakValue p B • p.pre := by
  constructor
  · intro h
    have hb := h p.pre (Submodule.mem_span_singleton_self p.pre)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    have hw : weakValue p B = c := by
      unfold weakValue numerator
      rw [← hc, pairing_smul_right]
      exact mul_div_cancel_right₀ c p.overlap_ne
    rw [hw]
    exact hc.symm
  · intro h x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, h]
    exact Submodule.smul_mem _ c
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p.pre))

/-- Membership is precisely multiplicativity against every ambient left factor. -/
theorem mem_preLineAlgebra_iff_multiplicative (p : RegularBoundaryPair ι) (B : Operator ι) :
    B ∈ preLineAlgebra p ↔
      ∀ A : Operator ι, weakValue p (A * B) = weakValue p A * weakValue p B := by
  rw [mem_preLineAlgebra_iff, weakValue_mul_all_left_iff]

def weakValueCharacter (p : RegularBoundaryPair ι) : preLineAlgebra p →ₐ[ℂ] ℂ where
  toFun A := weakValue p A.val
  map_one' := weakValue_one p
  map_zero' := weakValue_zero p
  map_add' A B := weakValue_add p A.val B.val
  map_mul' A B := weakValue_mul_of_pre_eigenvector p A.val B.val
    ((mem_preLineAlgebra_iff p B.val).mp B.property)
  commutes' c := by
    change weakValue p (algebraMap ℂ (Operator ι) c) = c
    rw [Algebra.algebraMap_eq_smul_one, weakValue_smul, weakValue_one, mul_one]

@[simp] theorem weakValueCharacter_apply (p : RegularBoundaryPair ι)
    (A : preLineAlgebra p) : weakValueCharacter p A = weakValue p A.val := rfl

end InfoGeometry.Streaming.TwoBoundaryDyadCompression
