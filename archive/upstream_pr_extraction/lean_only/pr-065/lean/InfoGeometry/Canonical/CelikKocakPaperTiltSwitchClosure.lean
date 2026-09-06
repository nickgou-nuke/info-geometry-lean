import InfoGeometry.Canonical.CelikKocakPaperGeneratorClosure

/-!
# Tilt/switch subalgebra contained in the paper-generated algebra

This file records the genuine finite-generation consequence available from the
paper-generator closure.  It does not identify either subalgebra with `⊤`.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open InfoGeometry.Canonical.CelikKocakCantorOperators
open FunctionSpace

abbrev paperTiltSwitchSubalgebra (n : ℕ) : Subalgebra ℂ (PaperOperator n) :=
  Algebra.adjoin ℂ
    (Set.range (fun i : Fin n => FunctionSpace.tilt (n := n) i) ∪
      Set.range (fun i : Fin n => FunctionSpace.switch (n := n) i))

theorem paperTilt_mem_paperTiltSwitchSubalgebra {n : ℕ} (i : Fin n) :
    FunctionSpace.tilt (n := n) i ∈ paperTiltSwitchSubalgebra n := by
  exact Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)

theorem paperSwitch_mem_paperTiltSwitchSubalgebra {n : ℕ} (i : Fin n) :
    FunctionSpace.switch (n := n) i ∈ paperTiltSwitchSubalgebra n := by
  exact Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)

theorem paperTiltSwitchSubalgebra_le_paperGeneratorSubalgebra (n : ℕ) :
    paperTiltSwitchSubalgebra n ≤ paperGeneratorSubalgebra n := by
  refine Algebra.adjoin_le ?_
  intro x hx
  rcases hx with hx | hx
  · rcases hx with ⟨i, rfl⟩
    exact paperTilt_mem_adjoin (n := n) (j := i.val) i.isLt
  · rcases hx with ⟨i, rfl⟩
    exact paperSwitch_mem_adjoin (n := n) (j := i.val) i.isLt

theorem paperPairTerm_mem_paperTiltSwitchSubalgebra {n j : ℕ} (hj : j < n) :
    FunctionSpace.pairTerm (n := n) j ∈ paperTiltSwitchSubalgebra n := by
  rw [FunctionSpace.pairTerm_of_lt (n := n) hj]
  exact (paperTiltSwitchSubalgebra n).mul_mem
    (paperTilt_mem_paperTiltSwitchSubalgebra ⟨j, hj⟩)
    (paperSwitch_mem_paperTiltSwitchSubalgebra ⟨j, hj⟩)

theorem paperPairPrefix_mem_paperTiltSwitchSubalgebra {n m : ℕ} (hm : m ≤ n) :
    FunctionSpace.pairPrefix (n := n) m ∈ paperTiltSwitchSubalgebra n := by
  induction m with
  | zero => exact (paperTiltSwitchSubalgebra n).one_mem
  | succ m ih =>
      rw [FunctionSpace.pairPrefix_succ]
      exact (paperTiltSwitchSubalgebra n).mul_mem (ih (Nat.le_of_succ_le hm))
        (paperPairTerm_mem_paperTiltSwitchSubalgebra
          (n := n) (j := m) (Nat.lt_of_succ_le hm))

private theorem paperOdd_mem_paperTiltSwitchSubalgebra {n j : ℕ} (hj : j < n) :
    paperOddGenerator (n := n) j hj ∈ paperTiltSwitchSubalgebra n := by
  let S := paperTiltSwitchSubalgebra n
  have hT : FunctionSpace.tilt (n := n) ⟨j, hj⟩ ∈ S :=
    paperTilt_mem_paperTiltSwitchSubalgebra ⟨j, hj⟩
  have hQ : FunctionSpace.pairPrefix (n := n) j ∈ S :=
    paperPairPrefix_mem_paperTiltSwitchSubalgebra (n := n) (m := j)
      (Nat.le_of_lt hj)
  exact S.smul_mem (S.mul_mem hT hQ) (paperPhase j)

private theorem paperEven_mem_paperTiltSwitchSubalgebra {n j : ℕ} (hj : j < n) :
    paperEvenGenerator (n := n) j hj ∈ paperTiltSwitchSubalgebra n := by
  let S := paperTiltSwitchSubalgebra n
  have hS : FunctionSpace.switch (n := n) ⟨j, hj⟩ ∈ S :=
    paperSwitch_mem_paperTiltSwitchSubalgebra ⟨j, hj⟩
  have hQ : FunctionSpace.pairPrefix (n := n) j ∈ S :=
    paperPairPrefix_mem_paperTiltSwitchSubalgebra (n := n) (m := j)
      (Nat.le_of_lt hj)
  exact S.smul_mem (S.mul_mem hS hQ) (paperPhase j)

theorem paperGeneratorSubalgebra_le_paperTiltSwitchSubalgebra (n : ℕ) :
    paperGeneratorSubalgebra n ≤ paperTiltSwitchSubalgebra n := by
  refine Algebra.adjoin_le ?_
  intro x hx
  rcases hx with ⟨i, rfl⟩
  rcases i with i | i
  · exact paperOdd_mem_paperTiltSwitchSubalgebra i.isLt
  · exact paperEven_mem_paperTiltSwitchSubalgebra i.isLt

theorem paperGeneratorSubalgebra_eq_paperTiltSwitchSubalgebra (n : ℕ) :
    paperGeneratorSubalgebra n = paperTiltSwitchSubalgebra n := by
  exact le_antisymm
    (paperGeneratorSubalgebra_le_paperTiltSwitchSubalgebra n)
    (paperTiltSwitchSubalgebra_le_paperGeneratorSubalgebra n)

theorem paperTilt_mem_paperGeneratorSubalgebra {n : ℕ} (i : Fin n) :
    FunctionSpace.tilt (n := n) i ∈ paperGeneratorSubalgebra n := by
  exact paperTilt_mem_adjoin (n := n) (j := i.val) i.isLt

theorem paperSwitch_mem_paperGeneratorSubalgebra {n : ℕ} (i : Fin n) :
    FunctionSpace.switch (n := n) i ∈ paperGeneratorSubalgebra n := by
  exact paperSwitch_mem_adjoin (n := n) (j := i.val) i.isLt

end InfoGeometry.Canonical.CelikKocakPaperFormalism
