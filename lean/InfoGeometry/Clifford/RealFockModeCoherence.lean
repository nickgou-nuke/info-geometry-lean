/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.RealFockCoordinateTransport
import InfoGeometry.Clifford.FockSpaceCAR

/-! # Native mode shift coherence and finite cross-mode readbacks

The mode index remains Fin n. Existing finite CAR is read back on the actual
finite CLMs; no new finite action or carrier is defined.
-/
noncomputable section
namespace InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
open InfoGeometry.Clifford
open InfoGeometry.Clifford.ClNNNeutralChevalleyBridge
attribute [local instance] fockNormedAddCommGroup fockInnerProductSpace

/-- Zero-head insertions never identify distinct old coordinate modes. -/
theorem fockModeShift_injective (m n : ℕ) (h : m ≤ n) :
    Function.Injective (fockModeShift m n h) := by
  induction n, h using Nat.le_induction with
  | base => intro i j hij; simpa only [fockModeShift_refl] using hij
  | succ n h ih =>
      intro i j hij
      rw [fockModeShift_succ m n h i, fockModeShift_succ m n h j] at hij
      exact ih (Fin.succ_inj.mp hij)

/-- Iterated coordinate transport agrees with the actual composite transition. -/
theorem fockModeShift_comp (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k) (i : Fin m) :
    fockModeShift n k hnk (fockModeShift m n hmn i) =
      fockModeShift m k (hmn.trans hnk) i := by
  induction k, hnk using Nat.le_induction with
  | base => simp only [fockModeShift_refl]
  | succ k h ih =>
      rw [fockModeShift_succ n k h (fockModeShift m n hmn i),
        fockModeShift_succ m k (hmn.trans h) i]
      exact congrArg Fin.succ ih

/-- Equality of two transported modes is preserved and reflected at every later stage. -/
theorem fockModeShift_eq_iff_further (m n k l : ℕ)
    (hmk : m ≤ k) (hnk : n ≤ k) (hkl : k ≤ l) (i : Fin m) (j : Fin n) :
    fockModeShift m l (hmk.trans hkl) i = fockModeShift n l (hnk.trans hkl) j ↔
      fockModeShift m k hmk i = fockModeShift n k hnk j := by
  rw [← fockModeShift_comp m k l hmk hkl, ← fockModeShift_comp n k l hnk hkl]
  exact (fockModeShift_injective k l hkl).eq_iff

/-- Comparing modes at different common upper stages gives the same equality test. -/
theorem fockModeShift_eq_iff_common (m n k l : ℕ)
    (hmk : m ≤ k) (hnk : n ≤ k) (hml : m ≤ l) (hnl : n ≤ l)
    (i : Fin m) (j : Fin n) :
    fockModeShift m k hmk i = fockModeShift n k hnk j ↔
      fockModeShift m l hml i = fockModeShift n l hnl j := by
  exact (fockModeShift_eq_iff_further m n k (max k l) hmk hnk
    (le_max_left k l) i j).symm.trans
      (fockModeShift_eq_iff_further m n l (max k l) hml hnl (le_max_right k l) i j)

/-- Existing exterior creation CAR, on the native finite normed operator maps. -/
theorem fockExtActionCLM_cross_apply (n : ℕ) (i j : Fin n) (x : FockStage n) :
    fockExtActionCLM n i (fockExtActionCLM n j x) +
      fockExtActionCLM n j (fockExtActionCLM n i x) = 0 := by
  simpa only [fockExtActionCLM_apply, FockSpaceCAR.creation_apply,
    FockSpaceCAR.fockExteriorEquiv_zero_apply, FockSpaceCAR.fockExteriorEquiv_zero_symm_apply]
    using FockSpaceCAR.creation_anticommute
      ((Pi.basisFun ℝ (Fin n)) i) ((Pi.basisFun ℝ (Fin n)) j) x

/-- Existing contraction CAR, on the same finite normed operator maps. -/
theorem fockIntActionCLM_cross_apply (n : ℕ) (i j : Fin n) (x : FockStage n) :
    fockIntActionCLM n i (fockIntActionCLM n j x) +
      fockIntActionCLM n j (fockIntActionCLM n i x) = 0 := by
  simpa only [fockIntActionCLM_apply, FockSpaceCAR.annihilation_apply,
    FockSpaceCAR.fockExteriorEquiv_zero_apply, FockSpaceCAR.fockExteriorEquiv_zero_symm_apply]
    using FockSpaceCAR.annihilation_anticommute
      (LinearMap.proj i : Module.Dual ℝ (Vector n)) (LinearMap.proj j) x

/-- Native mixed CAR evaluates to the coordinate Kronecker test. -/
theorem fock_coordinate_cross_CAR_apply (n : ℕ) (i j : Fin n) (x : FockStage n) :
    fockIntActionCLM n i (fockExtActionCLM n j x) +
      fockExtActionCLM n j (fockIntActionCLM n i x) = if i = j then x else 0 := by
  change intAction (LinearMap.proj i) (extAction ((Pi.basisFun ℝ (Fin n)) j) x) +
    extAction ((Pi.basisFun ℝ (Fin n)) j) (intAction (LinearMap.proj i) x) = _
  have he := ext_int_anticommutator ((Pi.basisFun ℝ (Fin n)) j)
    (LinearMap.proj i : Module.Dual ℝ (Vector n)) x
  by_cases hij : i = j
  · subst j
    simpa [Pi.basisFun_apply, add_comm] using he
  · simpa [Pi.basisFun_apply, hij, Ne.symm hij, add_comm] using he

end InfoGeometry.Clifford.ClNNFockDirectLimitRepresentation
