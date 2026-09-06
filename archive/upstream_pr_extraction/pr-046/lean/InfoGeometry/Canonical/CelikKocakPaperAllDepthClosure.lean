import InfoGeometry.Canonical.CelikKocakPairTermClosure

/-!
# All-depth paper-generator closure

This owner derives the first arbitrary-depth paper Clifford relation from the
native prefix algebra.  The proof keeps the retained operator words and uses
only associativity, pair-term commutation, and the prefix sign lemmas.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open InfoGeometry.Canonical.CelikKocakCantorOperators
open FunctionSpace

theorem paperOddGenerator_anticommute_of_lt {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i < j) :
    paperOddGenerator (n := n) i hi * paperOddGenerator (n := n) j hj +
        paperOddGenerator (n := n) j hj * paperOddGenerator (n := n) i hi = 0 := by
  let Ti := FunctionSpace.tilt (n := n) ⟨i, hi⟩
  let Tj := FunctionSpace.tilt (n := n) ⟨j, hj⟩
  let Qi := FunctionSpace.pairPrefix (n := n) i
  let Qj := FunctionSpace.pairPrefix (n := n) j
  have hTiTj : Commute Ti Tj := by
    exact FunctionSpace.tilt_comm (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
  have hQiTj : Commute Qi Tj := by
    exact (FunctionSpace.tilt_comm_pairPrefix (n := n) (m := i) (j := j)
      (Nat.le_of_lt hij) hj).symm
  have hTiQj : Ti * Qj = -(Qj * Ti) := by
    exact FunctionSpace.tilt_pairPrefix_anticomm_of_lt hi hij (Nat.le_of_lt hj)
  have hQjTi : Qj * Ti = -(Ti * Qj) := by
    simpa using (congrArg Neg.neg hTiQj).symm
  have hQiQj : Commute Qi Qj := by
    exact FunctionSpace.pairPrefix_commute_of_le (n := n) (m := i) (j := j)
      (Nat.le_of_lt hij)
  have hwords : (Ti * Qi) * (Tj * Qj) + (Tj * Qj) * (Ti * Qi) = 0 := by
    have hfirst :
        (Ti * Qi) * (Tj * Qj) = (Ti * Tj) * (Qi * Qj) := by
      simpa [mul_assoc] using hQiTj.mul_mul_mul_comm Ti Qj
    have hsecond :
        (Tj * Qj) * (Ti * Qi) = -((Ti * Tj) * (Qi * Qj)) := by
      calc
        (Tj * Qj) * (Ti * Qi) = Tj * (Qj * Ti) * Qi := by
          simp [mul_assoc]
        _ = Tj * (-(Ti * Qj)) * Qi := by rw [hQjTi]
        _ = (-(Tj * (Ti * Qj))) * Qi := by
          exact congrArg (fun x => x * Qi)
            (mul_neg Tj (Ti * Qj))
        _ = -((Tj * (Ti * Qj)) * Qi) := by
          exact neg_mul (Tj * (Ti * Qj)) Qi
        _ = -((Tj * Ti) * (Qj * Qi)) := by simp [mul_assoc]
        _ = -((Ti * Tj) * (Qi * Qj)) := by
          rw [hTiTj.eq, hQiQj.eq]
    rw [hfirst, hsecond]
    simp
  calc
    paperOddGenerator (n := n) i hi * paperOddGenerator (n := n) j hj +
        paperOddGenerator (n := n) j hj * paperOddGenerator (n := n) i hi =
      (paperPhase i * paperPhase j) •
        ((Ti * Qi) * (Tj * Qj) + (Tj * Qj) * (Ti * Qi)) := by
          simp [paperOddGenerator, Ti, Tj, Qi, Qj, mul_smul]
          rw [smul_smul, smul_smul]
          congr 1
          ring
    _ = 0 := by rw [hwords]; simp

theorem paperEvenGenerator_anticommute_of_lt {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i < j) :
    paperEvenGenerator (n := n) i hi * paperEvenGenerator (n := n) j hj +
        paperEvenGenerator (n := n) j hj * paperEvenGenerator (n := n) i hi = 0 := by
  let Si := FunctionSpace.switch (n := n) ⟨i, hi⟩
  let Sj := FunctionSpace.switch (n := n) ⟨j, hj⟩
  let Qi := FunctionSpace.pairPrefix (n := n) i
  let Qj := FunctionSpace.pairPrefix (n := n) j
  have hSiSj : Commute Si Sj := by
    exact FunctionSpace.switch_comm (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
      (by intro h; exact Nat.ne_of_lt hij (congrArg Fin.val h))
  have hQiSj : Commute Qi Sj := by
    exact (FunctionSpace.switch_comm_pairPrefix (n := n) (m := i) (j := j)
      (Nat.le_of_lt hij) hj).symm
  have hSiQj : Si * Qj = -(Qj * Si) := by
    exact FunctionSpace.switch_pairPrefix_anticomm_of_lt hi hij (Nat.le_of_lt hj)
  have hQjSi : Qj * Si = -(Si * Qj) := by
    simpa using (congrArg Neg.neg hSiQj).symm
  have hQiQj : Commute Qi Qj := by
    exact FunctionSpace.pairPrefix_commute_of_le (n := n) (m := i) (j := j)
      (Nat.le_of_lt hij)
  have hwords : (Si * Qi) * (Sj * Qj) + (Sj * Qj) * (Si * Qi) = 0 := by
    have hfirst :
        (Si * Qi) * (Sj * Qj) = (Si * Sj) * (Qi * Qj) := by
      simpa [mul_assoc] using hQiSj.mul_mul_mul_comm Si Qj
    have hsecond :
        (Sj * Qj) * (Si * Qi) = -((Si * Sj) * (Qi * Qj)) := by
      calc
        (Sj * Qj) * (Si * Qi) = Sj * (Qj * Si) * Qi := by simp [mul_assoc]
        _ = Sj * (-(Si * Qj)) * Qi := by rw [hQjSi]
        _ = (-(Sj * (Si * Qj))) * Qi := by
          exact congrArg (fun x => x * Qi) (mul_neg Sj (Si * Qj))
        _ = -((Sj * (Si * Qj)) * Qi) := by
          exact neg_mul (Sj * (Si * Qj)) Qi
        _ = -((Sj * Si) * (Qj * Qi)) := by simp [mul_assoc]
        _ = -((Si * Sj) * (Qi * Qj)) := by
          rw [hSiSj.eq, hQiQj.eq]
    rw [hfirst, hsecond]
    simp
  calc
    paperEvenGenerator (n := n) i hi * paperEvenGenerator (n := n) j hj +
        paperEvenGenerator (n := n) j hj * paperEvenGenerator (n := n) i hi =
      (paperPhase i * paperPhase j) •
        ((Si * Qi) * (Sj * Qj) + (Sj * Qj) * (Si * Qi)) := by
          simp [paperEvenGenerator, Si, Sj, Qi, Qj, mul_smul]
          rw [smul_smul, smul_smul]
          congr 1
          ring
    _ = 0 := by rw [hwords]; simp

theorem paperOdd_even_anticommute_of_lt {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i < j) :
    paperOddGenerator (n := n) i hi * paperEvenGenerator (n := n) j hj +
        paperEvenGenerator (n := n) j hj * paperOddGenerator (n := n) i hi = 0 := by
  let Ti := FunctionSpace.tilt (n := n) ⟨i, hi⟩
  let Sj := FunctionSpace.switch (n := n) ⟨j, hj⟩
  let Qi := FunctionSpace.pairPrefix (n := n) i
  let Qj := FunctionSpace.pairPrefix (n := n) j
  have hTiSj : Commute Ti Sj := by
    exact FunctionSpace.tilt_switch_comm_of_ne (n := n) (i := ⟨i, hi⟩)
      (j := ⟨j, hj⟩) (by intro h; exact Nat.ne_of_lt hij (congrArg Fin.val h))
  have hQiSj : Commute Qi Sj := by
    exact (FunctionSpace.switch_comm_pairPrefix (n := n) (m := i) (j := j)
      (Nat.le_of_lt hij) hj).symm
  have hTiQj : Ti * Qj = -(Qj * Ti) := by
    exact FunctionSpace.tilt_pairPrefix_anticomm_of_lt hi hij (Nat.le_of_lt hj)
  have hQjTi : Qj * Ti = -(Ti * Qj) := by
    simpa using (congrArg Neg.neg hTiQj).symm
  have hQiQj : Commute Qi Qj := by
    exact FunctionSpace.pairPrefix_commute_of_le (n := n) (m := i) (j := j)
      (Nat.le_of_lt hij)
  have hwords : (Ti * Qi) * (Sj * Qj) + (Sj * Qj) * (Ti * Qi) = 0 := by
    have hfirst :
        (Ti * Qi) * (Sj * Qj) = (Ti * Sj) * (Qi * Qj) := by
      simpa [mul_assoc] using hQiSj.mul_mul_mul_comm Ti Qj
    have hsecond :
        (Sj * Qj) * (Ti * Qi) = -((Ti * Sj) * (Qi * Qj)) := by
      calc
        (Sj * Qj) * (Ti * Qi) = Sj * (Qj * Ti) * Qi := by simp [mul_assoc]
        _ = Sj * (-(Ti * Qj)) * Qi := by rw [hQjTi]
        _ = (-(Sj * (Ti * Qj))) * Qi := by
          exact congrArg (fun x => x * Qi) (mul_neg Sj (Ti * Qj))
        _ = -((Sj * (Ti * Qj)) * Qi) := by
          exact neg_mul (Sj * (Ti * Qj)) Qi
        _ = -((Sj * Ti) * (Qj * Qi)) := by simp [mul_assoc]
        _ = -((Ti * Sj) * (Qi * Qj)) := by
          rw [hTiSj.eq, hQiQj.eq]
    rw [hfirst, hsecond]
    simp
  calc
    paperOddGenerator (n := n) i hi * paperEvenGenerator (n := n) j hj +
        paperEvenGenerator (n := n) j hj * paperOddGenerator (n := n) i hi =
      (paperPhase i * paperPhase j) •
        ((Ti * Qi) * (Sj * Qj) + (Sj * Qj) * (Ti * Qi)) := by
          simp [paperOddGenerator, paperEvenGenerator, Ti, Sj, Qi, Qj, mul_smul]
          rw [smul_smul, smul_smul]
          congr 1
          ring
    _ = 0 := by rw [hwords]; simp

theorem paperEven_odd_anticommute_of_lt {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i < j) :
    paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) j hj +
        paperOddGenerator (n := n) j hj * paperEvenGenerator (n := n) i hi = 0 := by
  let Si := FunctionSpace.switch (n := n) ⟨i, hi⟩
  let Tj := FunctionSpace.tilt (n := n) ⟨j, hj⟩
  let Qi := FunctionSpace.pairPrefix (n := n) i
  let Qj := FunctionSpace.pairPrefix (n := n) j
  have hSiTj : Commute Si Tj := by
    have h := FunctionSpace.tilt_switch_comm_of_ne (n := n) (i := ⟨j, hj⟩)
      (j := ⟨i, hi⟩) (by intro h; exact Nat.ne_of_lt hij (congrArg Fin.val h.symm))
    simpa [Commute] using h.symm
  have hQiTj : Commute Qi Tj := by
    exact (FunctionSpace.tilt_comm_pairPrefix (n := n) (m := i) (j := j)
      (Nat.le_of_lt hij) hj).symm
  have hSiQj : Si * Qj = -(Qj * Si) := by
    exact FunctionSpace.switch_pairPrefix_anticomm_of_lt hi hij (Nat.le_of_lt hj)
  have hQjSi : Qj * Si = -(Si * Qj) := by
    simpa using (congrArg Neg.neg hSiQj).symm
  have hQiQj : Commute Qi Qj := by
    exact FunctionSpace.pairPrefix_commute_of_le (n := n) (m := i) (j := j)
      (Nat.le_of_lt hij)
  have hwords : (Si * Qi) * (Tj * Qj) + (Tj * Qj) * (Si * Qi) = 0 := by
    have hfirst :
        (Si * Qi) * (Tj * Qj) = (Si * Tj) * (Qi * Qj) := by
      simpa [mul_assoc] using hQiTj.mul_mul_mul_comm Si Qj
    have hsecond :
        (Tj * Qj) * (Si * Qi) = -((Si * Tj) * (Qi * Qj)) := by
      calc
        (Tj * Qj) * (Si * Qi) = Tj * (Qj * Si) * Qi := by simp [mul_assoc]
        _ = Tj * (-(Si * Qj)) * Qi := by rw [hQjSi]
        _ = (-(Tj * (Si * Qj))) * Qi := by
          exact congrArg (fun x => x * Qi) (mul_neg Tj (Si * Qj))
        _ = -((Tj * (Si * Qj)) * Qi) := by
          exact neg_mul (Tj * (Si * Qj)) Qi
        _ = -((Tj * Si) * (Qj * Qi)) := by simp [mul_assoc]
        _ = -((Si * Tj) * (Qi * Qj)) := by
          rw [hSiTj.eq, hQiQj.eq]
    rw [hfirst, hsecond]
    simp
  calc
    paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) j hj +
        paperOddGenerator (n := n) j hj * paperEvenGenerator (n := n) i hi =
      (paperPhase i * paperPhase j) •
        ((Si * Qi) * (Tj * Qj) + (Tj * Qj) * (Si * Qi)) := by
          simp [paperEvenGenerator, paperOddGenerator, Si, Tj, Qi, Qj, mul_smul]
          rw [smul_smul, smul_smul]
          congr 1
          ring
    _ = 0 := by rw [hwords]; simp

/-! ### Unordered finite-family form

The ordered statements above are the calculation lemmas.  The following
results package them as pairwise relations, which is the form required by a
finite Clifford lift.  The two summands of `Fin n ⊕ Fin n` record the odd and
even paper generators without introducing a second index convention.
-/

theorem paperOddGenerator_anticommute_of_ne {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    paperOddGenerator (n := n) i hi * paperOddGenerator (n := n) j hj +
        paperOddGenerator (n := n) j hj * paperOddGenerator (n := n) i hi = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact paperOddGenerator_anticommute_of_lt hi hj h
  · have h' := paperOddGenerator_anticommute_of_lt hj hi h
    simpa [add_comm] using h'

theorem paperEvenGenerator_anticommute_of_ne {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    paperEvenGenerator (n := n) i hi * paperEvenGenerator (n := n) j hj +
        paperEvenGenerator (n := n) j hj * paperEvenGenerator (n := n) i hi = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact paperEvenGenerator_anticommute_of_lt hi hj h
  · have h' := paperEvenGenerator_anticommute_of_lt hj hi h
    simpa [add_comm] using h'

theorem paperOdd_even_anticommute_of_ne {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    paperOddGenerator (n := n) i hi * paperEvenGenerator (n := n) j hj +
        paperEvenGenerator (n := n) j hj * paperOddGenerator (n := n) i hi = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact paperOdd_even_anticommute_of_lt hi hj h
  · have h' := paperEven_odd_anticommute_of_lt hj hi h
    simpa [add_comm] using h'

theorem paperEven_odd_anticommute_of_ne {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) j hj +
        paperOddGenerator (n := n) j hj * paperEvenGenerator (n := n) i hi = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact paperEven_odd_anticommute_of_lt hi hj h
  · have h' := paperOdd_even_anticommute_of_lt hj hi h
    simpa [add_comm] using h'

theorem paperOdd_even_anticommute (n i : ℕ) (hi : i < n) (j : ℕ) (hj : j < n) :
    paperOddGenerator (n := n) i hi * paperEvenGenerator (n := n) j hj +
        paperEvenGenerator (n := n) j hj * paperOddGenerator (n := n) i hi = 0 := by
  by_cases h : i = j
  · subst h
    have hproof : hj = hi := Subsingleton.elim _ _
    rw [hproof]
    have hbase := paperOddGenerator_anticomm_paperEvenGenerator (n := n) i hi
    calc
      paperOddGenerator (n := n) i hi * paperEvenGenerator (n := n) i hi +
          paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) i hi =
          -(paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) i hi) +
            paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) i hi := by
              rw [hbase]
      _ = 0 := by abel
  · exact paperOdd_even_anticommute_of_ne hi hj h

theorem paperEven_odd_anticommute (n i : ℕ) (hi : i < n) (j : ℕ) (hj : j < n) :
    paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) j hj +
        paperOddGenerator (n := n) j hj * paperEvenGenerator (n := n) i hi = 0 := by
  by_cases h : i = j
  · subst h
    have hproof : hj = hi := Subsingleton.elim _ _
    rw [hproof]
    have hbase := paperOddGenerator_anticomm_paperEvenGenerator (n := n) i hi
    calc
      paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) i hi +
          paperOddGenerator (n := n) i hi * paperEvenGenerator (n := n) i hi =
          paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) i hi +
            -(paperEvenGenerator (n := n) i hi * paperOddGenerator (n := n) i hi) := by
              rw [hbase]
      _ = 0 := by abel
  · exact paperEven_odd_anticommute_of_ne hi hj h

def paperGamma (n : ℕ) : Fin n ⊕ Fin n → (((Fin n) → Bool) → ℂ) →ₗ[ℂ] (((Fin n) → Bool) → ℂ) :=
  Sum.elim
    (fun i => paperOddGenerator (n := n) i i.isLt)
    (fun i => paperEvenGenerator (n := n) i i.isLt)

theorem paperGamma_sq {n : ℕ} (i : Fin n ⊕ Fin n) :
    paperGamma n i * paperGamma n i = 1 := by
  cases i with
  | inl i => exact paperOddGenerator_sq i i.isLt
  | inr i => exact paperEvenGenerator_sq i i.isLt

theorem paperGamma_anticomm {n : ℕ} {i j : Fin n ⊕ Fin n} (hij : i ≠ j) :
    paperGamma n i * paperGamma n j + paperGamma n j * paperGamma n i = 0 := by
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          apply paperOddGenerator_anticommute_of_ne i.isLt j.isLt
          intro h
          exact hij (congrArg Sum.inl (Fin.ext h))
      | inr j =>
          exact paperOdd_even_anticommute n i.val i.isLt j.val j.isLt
  | inr i =>
      cases j with
      | inl j =>
          exact paperEven_odd_anticommute n i.val i.isLt j.val j.isLt
      | inr j =>
          apply paperEvenGenerator_anticommute_of_ne i.isLt j.isLt
          intro h
          exact hij (congrArg Sum.inr (Fin.ext h))

end InfoGeometry.Canonical.CelikKocakPaperFormalism
