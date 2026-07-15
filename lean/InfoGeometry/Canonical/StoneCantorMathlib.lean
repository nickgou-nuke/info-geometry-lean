import Mathlib
import InfoGeometry.Canonical.StoneBridgeMathlib
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

/-!
# Mathlib-style Cantor cylinder coherence

Pure order/topology-free core for the Cantor side of Stone duality.  The file
uses only the repository's existing binary-word notation and mathlib's
`Ultrafilter`/`pure` principal ultrafilters.

Closed content:

* finite prefix cylinders in `ℕ → Bool`;
* principal-ultrafilter membership is exactly point evaluation;
* each cylinder is the disjoint union of its two successor cylinders;
* therefore the principal Stone evaluation is successor coherent.

No measure extension, martingale convergence, compactness, AF algebra, or
physics interpretation is asserted.
-/

noncomputable section

namespace StoneCantorMathlib

open Set
open UHFInductiveColimitBoundary

/-- The Cantor cylinder determined by a finite bitword. -/
def prefixCylinder (n : ℕ) (w : BitWord n) : Set CantorBoundary :=
  {x | boundaryPrefix n x = w}

@[simp] theorem mem_prefixCylinder (n : ℕ) (w : BitWord n) (x : CantorBoundary) :
    x ∈ prefixCylinder n w ↔ boundaryPrefix n x = w :=
  Iff.rfl

/-- Principal Stone evaluation of a cylinder is exactly prefix equality. -/
theorem principalUltrafilter_prefixCylinder_eval
    (x : CantorBoundary) (n : ℕ) (w : BitWord n) :
    prefixCylinder n w ∈ (pure x : Ultrafilter CantorBoundary) ↔
      boundaryPrefix n x = w := by
  simp [prefixCylinder]

/-- The depth-`n+1` prefix is the old prefix extended by the next bit. -/
theorem boundaryPrefix_succ_eq_extend
    (x : CantorBoundary) (n : ℕ) :
    boundaryPrefix (n + 1) x = extendSucc n (boundaryPrefix n x) (x n) := by
  ext i
  by_cases hi : i.1 < n
  · simp [boundaryPrefix, extendSucc, hi]
  · have heq : i.1 = n := by omega
    simp [boundaryPrefix, extendSucc, heq]

/-- A finite cylinder is exactly the union of its two successor cylinders. -/
theorem prefixCylinder_successor_union (n : ℕ) (w : BitWord n) :
    prefixCylinder n w =
      prefixCylinder (n + 1) (extendSucc n w false) ∪
        prefixCylinder (n + 1) (extendSucc n w true) := by
  ext x
  constructor
  · intro hx
    have hnext := boundaryPrefix_succ_eq_extend x n
    by_cases hb : x n = false
    · left
      rw [hx] at hnext
      simpa [prefixCylinder, hb] using hnext
    · have hbtrue : x n = true := by cases h : x n <;> simp [h] at hb ⊢
      right
      rw [hx] at hnext
      simpa [prefixCylinder, hbtrue] using hnext
  · intro hx
    rcases hx with hx | hx
    · exact prefixSucc_extendSucc n w false ▸ congrArg (prefixSucc n) hx
    · exact prefixSucc_extendSucc n w true ▸ congrArg (prefixSucc n) hx

/-- The two one-bit successor extensions of a word are distinct. -/
theorem extendSucc_false_ne_true (n : ℕ) (w : BitWord n) :
    extendSucc n w false ≠ extendSucc n w true := by
  intro h
  have hbit := congrFun h ⟨n, Nat.lt_succ_self n⟩
  simp [extendSucc] at hbit

/-- The two successor cylinders of a word are disjoint. -/
theorem prefixCylinder_successor_disjoint (n : ℕ) (w : BitWord n) :
    Disjoint
      (prefixCylinder (n + 1) (extendSucc n w false))
      (prefixCylinder (n + 1) (extendSucc n w true)) := by
  rw [Set.disjoint_left]
  intro x hfalse htrue
  change boundaryPrefix (n + 1) x = extendSucc n w false at hfalse
  change boundaryPrefix (n + 1) x = extendSucc n w true at htrue
  exact extendSucc_false_ne_true n w (hfalse.symm.trans htrue)

/-- Principal Stone evaluation is successor coherent on Cantor cylinders. -/
theorem principalUltrafilter_successor_coherence
    (x : CantorBoundary) (n : ℕ) (w : BitWord n) :
    prefixCylinder n w ∈ (pure x : Ultrafilter CantorBoundary) ↔
      prefixCylinder (n + 1) (extendSucc n w false) ∈
          (pure x : Ultrafilter CantorBoundary) ∨
        prefixCylinder (n + 1) (extendSucc n w true) ∈
          (pure x : Ultrafilter CantorBoundary) := by
  rw [principalUltrafilter_prefixCylinder_eval,
    principalUltrafilter_prefixCylinder_eval,
    principalUltrafilter_prefixCylinder_eval]
  constructor
  · intro hx
    have hnext := boundaryPrefix_succ_eq_extend x n
    by_cases hb : x n = false
    · left
      rw [hx] at hnext
      simpa [hb] using hnext
    · have hbtrue : x n = true := by cases h : x n <;> simp [h] at hb ⊢
      right
      rw [hx] at hnext
      simpa [hbtrue] using hnext
  · intro hx
    rcases hx with hx | hx
    · exact prefixSucc_extendSucc n w false ▸ congrArg (prefixSucc n) hx
    · exact prefixSucc_extendSucc n w true ▸ congrArg (prefixSucc n) hx

/-- Sharp `0/1` cylinder expectation for a principal Stone point. -/
def sharpCylinderExpectation (x : CantorBoundary) (n : ℕ) (w : BitWord n) : ℚ :=
  if boundaryPrefix n x = w then 1 else 0

/-- Sharp expectation is one exactly on the cylinder containing the point. -/
theorem sharpCylinderExpectation_eq_one_iff
    (x : CantorBoundary) (n : ℕ) (w : BitWord n) :
    sharpCylinderExpectation x n w = 1 ↔
      prefixCylinder n w ∈ (pure x : Ultrafilter CantorBoundary) := by
  rw [principalUltrafilter_prefixCylinder_eval]
  by_cases h : boundaryPrefix n x = w <;> simp [sharpCylinderExpectation, h]

/-- Sharp expectations obey successor persistence. -/
theorem sharpCylinderExpectation_successor
    (x : CantorBoundary) (n : ℕ) (w : BitWord n) :
    sharpCylinderExpectation x n w =
      sharpCylinderExpectation x (n + 1) (extendSucc n w false) +
        sharpCylinderExpectation x (n + 1) (extendSucc n w true) := by
  unfold sharpCylinderExpectation
  by_cases hw : boundaryPrefix n x = w
  · have hnext := boundaryPrefix_succ_eq_extend x n
    by_cases hb : x n = false
    · have hf : boundaryPrefix (n + 1) x = extendSucc n w false := by
        simpa [hw, hb] using hnext
      have ht : boundaryPrefix (n + 1) x ≠ extendSucc n w true := by
        intro hbad
        exact extendSucc_false_ne_true n w (hf.symm.trans hbad)
      have hne := extendSucc_false_ne_true n w
      simp [hw, hf, hne]
    · have hbtrue : x n = true := by cases h : x n <;> simp [h] at hb ⊢
      have ht : boundaryPrefix (n + 1) x = extendSucc n w true := by
        simpa [hw, hbtrue] using hnext
      have hf : boundaryPrefix (n + 1) x ≠ extendSucc n w false := by
        intro hbad
        exact extendSucc_false_ne_true n w (hbad.symm.trans ht)
      have hne := extendSucc_false_ne_true n w
      simp [hw, ht, hne.symm]
  · have hf : boundaryPrefix (n + 1) x ≠ extendSucc n w false := by
      intro hbad
      exact hw (prefixSucc_extendSucc n w false ▸ congrArg (prefixSucc n) hbad)
    have ht : boundaryPrefix (n + 1) x ≠ extendSucc n w true := by
      intro hbad
      exact hw (prefixSucc_extendSucc n w true ▸ congrArg (prefixSucc n) hbad)
    simp [hw, hf, ht]

end StoneCantorMathlib
