import InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth

noncomputable section

namespace InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth

open InfoGeometry.Canonical.CelikKocakCantorOperators
open InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace

private lemma prefixSign_succ {n k : ℕ} (x : ((Fin n) → Bool)) :
    prefixSign (k + 1) x =
      prefixSign k x * (if h : k < n then
        (if x ⟨k, h⟩ then (-1 : ℂ) else 1) else 1) := by
  unfold prefixSign
  rw [Finset.prod_range_succ]

private lemma prefixSign_flipAt_later
    {n i j : ℕ} (hi : i < n) (hj : j < n) (hij : i < j)
    (x : ((Fin n) → Bool)) :
    prefixSign j (CantorAddress.flipAt ⟨i, hi⟩ x) =
      -(prefixSign j x) := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
      by_cases hEq : i = j
      · subst j
        have hs := prefixSign_flipAt_same (⟨i, hi⟩ : Fin n) x
        rw [prefixSign_succ, prefixSign_succ, hs]
        simp [hi, CantorAddress.flipAt_apply_eq]
        cases hx : x ⟨i, hi⟩ <;> simp
      · have hij' : i < j := by omega
        have ih' := ih (i := i) hi (by omega) hij'
        have hne : (⟨j, by omega⟩ : Fin n) ≠ ⟨i, hi⟩ := by
          intro h
          exact hEq (congrArg Fin.val h).symm
        have hfac :
            (if h : j < n then
                (if (CantorAddress.flipAt ⟨i, hi⟩ x) ⟨j, h⟩ then
                  (-1 : ℂ) else 1) else 1) =
              (if h : j < n then
                (if x ⟨j, h⟩ then (-1 : ℂ) else 1) else 1) := by
          have hj' : j < n := by omega
          rw [dif_pos hj', dif_pos hj']
          simp [CantorAddress.flipAt_apply_ne hne]
        rw [prefixSign_succ, prefixSign_succ, ih']
        rw [hfac]
        ring

private lemma prefixSign_flipAt_earlier
    {n i j : ℕ} (hj : j < n) (hij : i < j)
    (x : ((Fin n) → Bool)) :
    prefixSign i (CantorAddress.flipAt ⟨j, hj⟩ x) =
      prefixSign i x := by
  unfold prefixSign
  refine Finset.prod_congr rfl ?_
  intro k hk
  have hki : k < i := by simpa using hk
  by_cases hkn : k < n
  · have hne : (⟨k, hkn⟩ : Fin n) ≠ ⟨j, hj⟩ := by
      intro h
      have hkj : k = j := congrArg Fin.val h
      exact (Nat.ne_of_lt (lt_trans hki hij)) hkj
    simp only [dif_pos hkn]
    rw [CantorAddress.flipAt_apply_ne hne]
  · simp [hkn]

theorem prefixSign_flipAt_later_of_lt
    {n : ℕ} {i j : Fin n} (hij : i.val < j.val)
    (x : ((Fin n) → Bool)) :
    prefixSign j.val (CantorAddress.flipAt i x) =
      -(prefixSign j.val x) := by
  exact prefixSign_flipAt_later i.isLt j.isLt hij x

theorem prefixSign_flipAt_earlier_of_lt
    {n : ℕ} {i j : Fin n} (hij : i.val < j.val)
    (x : ((Fin n) → Bool)) :
    prefixSign i.val (CantorAddress.flipAt j x) =
      prefixSign i.val x := by
  exact prefixSign_flipAt_earlier j.isLt hij x

theorem cantorCreation_anticommute_of_lt
    {n : ℕ} {i j : Fin n} (hij : i.val < j.val) :
    cantorCreation n i * cantorCreation n j +
        cantorCreation n j * cantorCreation n i = 0 := by
  have hne : i ≠ j := by
    intro h
    exact Nat.ne_of_lt hij (congrArg Fin.val h)
  apply LinearMap.ext
  intro f
  ext x
  have hsi := prefixSign_flipAt_earlier_of_lt hij x
  have hsj := prefixSign_flipAt_later_of_lt hij x
  have hflip := CantorAddress.flipAt_comm hne x
  by_cases hxi : x i <;> by_cases hxj : x j <;>
    simp [cantorCreation_apply, hxi, hxj,
      CantorAddress.flipAt_apply_ne hne,
      CantorAddress.flipAt_apply_ne (Ne.symm hne), hsi, hsj, hflip] <;>
    ring

theorem cantorAnnihilation_anticommute_of_lt
    {n : ℕ} {i j : Fin n} (hij : i.val < j.val) :
    cantorAnnihilation n i * cantorAnnihilation n j +
        cantorAnnihilation n j * cantorAnnihilation n i = 0 := by
  have hne : i ≠ j := by
    intro h
    exact Nat.ne_of_lt hij (congrArg Fin.val h)
  apply LinearMap.ext
  intro f
  ext x
  have hsi := prefixSign_flipAt_earlier_of_lt hij x
  have hsj := prefixSign_flipAt_later_of_lt hij x
  have hflip := CantorAddress.flipAt_comm hne x
  by_cases hxi : x i <;> by_cases hxj : x j <;>
    simp [cantorAnnihilation_apply, hxi, hxj,
      CantorAddress.flipAt_apply_ne hne,
      CantorAddress.flipAt_apply_ne (Ne.symm hne), hsi, hsj, hflip] <;>
    ring

theorem cantorAnnihilation_creation_anticommute_of_lt
    {n : ℕ} {i j : Fin n} (hij : i.val < j.val) :
    cantorAnnihilation n i * cantorCreation n j +
        cantorCreation n j * cantorAnnihilation n i = 0 := by
  have hne : i ≠ j := by
    intro h
    exact Nat.ne_of_lt hij (congrArg Fin.val h)
  apply LinearMap.ext
  intro f
  ext x
  have hsi := prefixSign_flipAt_earlier_of_lt hij x
  have hsj := prefixSign_flipAt_later_of_lt hij x
  have hflip := CantorAddress.flipAt_comm hne x
  by_cases hxi : x i <;> by_cases hxj : x j <;>
    simp [cantorAnnihilation_apply, cantorCreation_apply, hxi, hxj,
      CantorAddress.flipAt_apply_ne hne,
      CantorAddress.flipAt_apply_ne (Ne.symm hne), hsi, hsj, hflip] <;>
    ring

theorem cantorCreation_annihilation_anticommute_of_lt
    {n : ℕ} {i j : Fin n} (hij : i.val < j.val) :
    cantorCreation n i * cantorAnnihilation n j +
        cantorAnnihilation n j * cantorCreation n i = 0 := by
  have hne : i ≠ j := by
    intro h
    exact Nat.ne_of_lt hij (congrArg Fin.val h)
  apply LinearMap.ext
  intro f
  ext x
  have hsi := prefixSign_flipAt_earlier_of_lt hij x
  have hsj := prefixSign_flipAt_later_of_lt hij x
  have hflip := CantorAddress.flipAt_comm hne x
  by_cases hxi : x i <;> by_cases hxj : x j <;>
    simp [cantorCreation_apply, cantorAnnihilation_apply, hxi, hxj,
      CantorAddress.flipAt_apply_ne hne,
      CantorAddress.flipAt_apply_ne (Ne.symm hne), hsi, hsj, hflip] <;>
    ring

theorem cantorCreation_anticommute
    {n : ℕ} (i j : Fin n) :
    cantorCreation n i * cantorCreation n j +
        cantorCreation n j * cantorCreation n i = 0 := by
  by_cases hij : i.val < j.val
  · exact cantorCreation_anticommute_of_lt hij
  by_cases hji : j.val < i.val
  · simpa [add_comm] using cantorCreation_anticommute_of_lt hji
  have hEq : i = j := by
    apply Fin.ext
    omega
  subst j
  rw [cantorCreation_sq_zero]
  simp

theorem cantorAnnihilation_anticommute
    {n : ℕ} (i j : Fin n) :
    cantorAnnihilation n i * cantorAnnihilation n j +
        cantorAnnihilation n j * cantorAnnihilation n i = 0 := by
  by_cases hij : i.val < j.val
  · exact cantorAnnihilation_anticommute_of_lt hij
  by_cases hji : j.val < i.val
  · simpa [add_comm] using cantorAnnihilation_anticommute_of_lt hji
  have hEq : i = j := by
    apply Fin.ext
    omega
  subst j
  rw [cantorAnnihilation_sq_zero]
  simp

theorem cantorAnnihilation_creation_anticommute
    {n : ℕ} (i j : Fin n) :
    cantorAnnihilation n i * cantorCreation n j +
        cantorCreation n j * cantorAnnihilation n i =
      if i = j then 1 else 0 := by
  by_cases hEq : i = j
  · subst j
    simp [cantorAnnihilation_creation_anticomm_self]
  by_cases hij : i.val < j.val
  · rw [if_neg hEq]
    exact cantorAnnihilation_creation_anticommute_of_lt hij
  have hji : j.val < i.val := by omega
  rw [if_neg hEq]
  simpa [add_comm] using cantorCreation_annihilation_anticommute_of_lt hji

theorem cantorCreation_annihilation_anticommute
    {n : ℕ} (i j : Fin n) :
    cantorCreation n i * cantorAnnihilation n j +
        cantorAnnihilation n j * cantorCreation n i =
      if i = j then 1 else 0 := by
  by_cases hEq : i = j
  · subst j
    simp [cantorAnnihilation_creation_anticomm_self, add_comm]
  by_cases hij : i.val < j.val
  · rw [if_neg hEq]
    exact cantorCreation_annihilation_anticommute_of_lt hij
  have hji : j.val < i.val := by omega
  rw [if_neg hEq]
  simpa [add_comm] using cantorAnnihilation_creation_anticommute_of_lt hji

theorem cantorFiniteCAR
    {n : ℕ} (i j : Fin n) :
    (cantorCreation n i * cantorCreation n j +
        cantorCreation n j * cantorCreation n i = 0) ∧
    (cantorAnnihilation n i * cantorAnnihilation n j +
        cantorAnnihilation n j * cantorAnnihilation n i = 0) ∧
    (cantorAnnihilation n i * cantorCreation n j +
        cantorCreation n j * cantorAnnihilation n i =
          if i = j then 1 else 0) := by
  exact ⟨cantorCreation_anticommute i j,
    cantorAnnihilation_anticommute i j,
    cantorAnnihilation_creation_anticommute i j⟩

end InfoGeometry.Canonical.JordanWignerCelikKocakBridgeNDepth
