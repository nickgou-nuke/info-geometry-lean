import InfoGeometry.Canonical.CelikKocakPaperFormalism

/-!
# Native pair-term closure

This owner isolates the finite-rank algebraic facts needed by the recursive
Çelik--Koçak strings.  A local pair term is `tilt * switch`.  The results are
valid at every finite depth and use only the native tilt/switch relations;
they do not identify the retained operator words with their Zorn shadow.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open InfoGeometry.Canonical.CelikKocakCantorOperators
open InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace

namespace FunctionSpace

private theorem tilt_switch_reverse_anticomm {n : ℕ} (j : Fin n) :
    switch j * tilt j = -(tilt j * switch j) := by
  have h := tilt_switch_anticomm j
  calc
    switch j * tilt j = - (-(switch j * tilt j)) := by simp
    _ = -(tilt j * switch j) := by rw [h]

theorem tilt_pairTerm_anticomm {n j : ℕ} (hj : j < n) :
    tilt (n := n) ⟨j, hj⟩ * pairTerm (n := n) j =
      -(pairTerm (n := n) j * tilt (n := n) ⟨j, hj⟩) := by
  rw [pairTerm_of_lt (n := n) hj]
  have hsum :
      tilt (n := n) ⟨j, hj⟩ *
          (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) +
        (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) *
          tilt (n := n) ⟨j, hj⟩ = 0 := by
    calc
      tilt (n := n) ⟨j, hj⟩ *
            (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) +
          (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) *
            tilt (n := n) ⟨j, hj⟩ =
          (tilt (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩) *
              switch (n := n) ⟨j, hj⟩ +
            tilt (n := n) ⟨j, hj⟩ *
              (switch (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩) := by
                noncomm_ring
      _ = (1 : (((Fin n) → Bool) → ℂ) →ₗ[ℂ] (((Fin n) → Bool) → ℂ)) * switch (n := n) ⟨j, hj⟩ +
            tilt (n := n) ⟨j, hj⟩ *
              (-(tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)) := by
                rw [tilt_sq, tilt_switch_reverse_anticomm]
      _ = switch (n := n) ⟨j, hj⟩ +
            -(tilt (n := n) ⟨j, hj⟩ *
              (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)) := by
                simp only [one_mul]
                exact congrArg (fun x => switch (n := n) ⟨j, hj⟩ + x)
                  (mul_neg
                    (tilt (n := n) ⟨j, hj⟩)
                    (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩))
      _ = switch (n := n) ⟨j, hj⟩ -
            (tilt (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩) *
              switch (n := n) ⟨j, hj⟩ := by
                rw [sub_eq_add_neg]
                congr 1
      _ = 0 := by
                rw [tilt_sq]
                simp
  exact eq_neg_of_add_eq_zero_left hsum

theorem switch_pairTerm_anticomm {n j : ℕ} (hj : j < n) :
    switch (n := n) ⟨j, hj⟩ * pairTerm (n := n) j =
      -(pairTerm (n := n) j * switch (n := n) ⟨j, hj⟩) := by
  rw [pairTerm_of_lt (n := n) hj]
  have hsum :
      switch (n := n) ⟨j, hj⟩ *
          (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) +
        (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) *
          switch (n := n) ⟨j, hj⟩ = 0 := by
    calc
      switch (n := n) ⟨j, hj⟩ *
            (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) +
          (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) *
            switch (n := n) ⟨j, hj⟩ =
          (switch (n := n) ⟨j, hj⟩ * tilt (n := n) ⟨j, hj⟩) *
              switch (n := n) ⟨j, hj⟩ +
            tilt (n := n) ⟨j, hj⟩ *
              (switch (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) := by
                noncomm_ring
      _ = (-(tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)) *
              switch (n := n) ⟨j, hj⟩ +
            tilt (n := n) ⟨j, hj⟩ *
              (switch (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) := by
                simp [tilt_switch_anticomm]
      _ = -(tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) *
              switch (n := n) ⟨j, hj⟩ + tilt (n := n) ⟨j, hj⟩ := by
                rw [switch_sq]
                simp
      _ = 0 := by
                calc
                  (-(tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)) *
                        switch (n := n) ⟨j, hj⟩ +
                      tilt (n := n) ⟨j, hj⟩ =
                    - ((tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩) *
                        switch (n := n) ⟨j, hj⟩) +
                      tilt (n := n) ⟨j, hj⟩ := by
                        exact congrArg (fun x => x + tilt (n := n) ⟨j, hj⟩)
                          (neg_mul
                            (tilt (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)
                            (switch (n := n) ⟨j, hj⟩))
                  _ = -(tilt (n := n) ⟨j, hj⟩ *
                        (switch (n := n) ⟨j, hj⟩ * switch (n := n) ⟨j, hj⟩)) +
                      tilt (n := n) ⟨j, hj⟩ := by
                        rw [mul_assoc]
                  _ = 0 := by
                        rw [switch_sq]
                        simp
  exact eq_neg_of_add_eq_zero_left hsum

theorem tilt_pairTerm_commute_of_ne {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Commute (tilt (n := n) ⟨i, hi⟩) (pairTerm (n := n) j) := by
  have htt : Commute (tilt (n := n) ⟨i, hi⟩)
      (tilt (n := n) ⟨j, hj⟩) :=
    tilt_comm (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩)
  have hts : Commute (tilt (n := n) ⟨i, hi⟩)
      (switch (n := n) ⟨j, hj⟩) :=
    tilt_switch_comm_of_ne (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by
      intro h
      exact hij (congrArg Fin.val h))
  simpa [pairTerm_of_lt (n := n) hj] using htt.mul_right hts

theorem switch_pairTerm_commute_of_ne {n i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Commute (switch (n := n) ⟨i, hi⟩) (pairTerm (n := n) j) := by
  have hst : Commute (switch (n := n) ⟨i, hi⟩)
      (tilt (n := n) ⟨j, hj⟩) := by
    have h := tilt_switch_comm_of_ne (n := n) (i := ⟨j, hj⟩)
        (j := ⟨i, hi⟩) (by
          intro h
          exact hij (congrArg Fin.val h.symm))
    simpa [Commute, mul_assoc] using h.symm
  have hss : Commute (switch (n := n) ⟨i, hi⟩)
      (switch (n := n) ⟨j, hj⟩) :=
    switch_comm (n := n) (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by
      intro h
      exact hij (congrArg Fin.val h))
  simpa [pairTerm_of_lt (n := n) hj] using hst.mul_right hss

theorem tilt_pairPrefix_anticomm_of_lt {n i j : ℕ}
    (hi : i < n) (hij : i < j) (hj : j ≤ n) :
    tilt (n := n) ⟨i, hi⟩ * pairPrefix (n := n) j =
      -(pairPrefix (n := n) j * tilt (n := n) ⟨i, hi⟩) := by
  have hbase :
      tilt (n := n) ⟨i, hi⟩ * pairPrefix (n := n) (i + 1) =
        -(pairPrefix (n := n) (i + 1) * tilt (n := n) ⟨i, hi⟩) := by
    rw [pairPrefix_succ]
    have hcomm : Commute (tilt (n := n) ⟨i, hi⟩)
        (pairPrefix (n := n) i) :=
      tilt_comm_pairPrefix (n := n) (m := i) (j := i) (Nat.le_refl i) hi
    have hanti : tilt (n := n) ⟨i, hi⟩ * pairTerm (n := n) i =
        -(pairTerm (n := n) i * tilt (n := n) ⟨i, hi⟩) :=
      tilt_pairTerm_anticomm hi
    calc
      tilt (n := n) ⟨i, hi⟩ * (pairPrefix (n := n) i * pairTerm (n := n) i)
          = (tilt (n := n) ⟨i, hi⟩ * pairPrefix (n := n) i) * pairTerm (n := n) i := by
              simp [mul_assoc]
      _ = (pairPrefix (n := n) i * tilt (n := n) ⟨i, hi⟩) * pairTerm (n := n) i := by
              rw [hcomm.eq]
      _ = pairPrefix (n := n) i *
          (tilt (n := n) ⟨i, hi⟩ * pairTerm (n := n) i) := by
              rw [mul_assoc]
      _ = pairPrefix (n := n) i *
          (-(pairTerm (n := n) i * tilt (n := n) ⟨i, hi⟩)) := by
              rw [hanti]
      _ = -((pairPrefix (n := n) i * pairTerm (n := n) i) *
          tilt (n := n) ⟨i, hi⟩) := by
              change pairPrefix (n := n) i *
                  (-(pairTerm (n := n) i * tilt (n := n) ⟨i, hi⟩)) =
                - (pairPrefix (n := n) i *
                  (pairTerm (n := n) i * tilt (n := n) ⟨i, hi⟩))
              exact mul_neg
                (a := pairPrefix (n := n) i)
                (b := pairTerm (n := n) i * tilt (n := n) ⟨i, hi⟩)
  refine Nat.le_induction (m := i + 1)
    (P := fun m _ => m ≤ n →
      tilt (n := n) ⟨i, hi⟩ * pairPrefix (n := n) m =
        -(pairPrefix (n := n) m * tilt (n := n) ⟨i, hi⟩)) ?_ ?_ j
    (Nat.succ_le_iff.mpr hij) hj
  · intro
    exact hbase
  · intro m hm hprev hbound
    have hmi : i ≠ m := by
      intro h
      subst h
      exact (Nat.not_succ_le_self i) (by simpa using hm)
    have hcomm : Commute (tilt (n := n) ⟨i, hi⟩) (pairTerm (n := n) m) :=
      tilt_pairTerm_commute_of_ne hi (Nat.lt_of_succ_le hbound) hmi
    rw [pairPrefix_succ]
    calc
      tilt (n := n) ⟨i, hi⟩ *
          (pairPrefix (n := n) m * pairTerm (n := n) m) =
          (tilt (n := n) ⟨i, hi⟩ * pairPrefix (n := n) m) *
            pairTerm (n := n) m := by simp [mul_assoc]
      _ = (-(pairPrefix (n := n) m * tilt (n := n) ⟨i, hi⟩)) *
            pairTerm (n := n) m := by
              rw [hprev (Nat.le_of_lt (Nat.lt_of_succ_le hbound))]
      _ = -(pairPrefix (n := n) m *
            (tilt (n := n) ⟨i, hi⟩ * pairTerm (n := n) m)) := by
            exact neg_mul
              (pairPrefix (n := n) m * tilt (n := n) ⟨i, hi⟩)
              (pairTerm (n := n) m)
      _ = -(pairPrefix (n := n) m *
            (pairTerm (n := n) m * tilt (n := n) ⟨i, hi⟩)) := by
            rw [hcomm.eq]
      _ = -((pairPrefix (n := n) m * pairTerm (n := n) m) *
            tilt (n := n) ⟨i, hi⟩) := by simp [mul_assoc]

theorem switch_pairPrefix_anticomm_of_lt {n i j : ℕ}
    (hi : i < n) (hij : i < j) (hj : j ≤ n) :
    switch (n := n) ⟨i, hi⟩ * pairPrefix (n := n) j =
      -(pairPrefix (n := n) j * switch (n := n) ⟨i, hi⟩) := by
  have hbase :
      switch (n := n) ⟨i, hi⟩ * pairPrefix (n := n) (i + 1) =
        -(pairPrefix (n := n) (i + 1) * switch (n := n) ⟨i, hi⟩) := by
    rw [pairPrefix_succ]
    have hcomm : Commute (switch (n := n) ⟨i, hi⟩)
        (pairPrefix (n := n) i) :=
      switch_comm_pairPrefix (n := n) (m := i) (j := i) (Nat.le_refl i) hi
    have hanti : switch (n := n) ⟨i, hi⟩ * pairTerm (n := n) i =
        -(pairTerm (n := n) i * switch (n := n) ⟨i, hi⟩) :=
      switch_pairTerm_anticomm hi
    calc
      switch (n := n) ⟨i, hi⟩ * (pairPrefix (n := n) i * pairTerm (n := n) i)
          = (switch (n := n) ⟨i, hi⟩ * pairPrefix (n := n) i) * pairTerm (n := n) i := by
              simp [mul_assoc]
      _ = (pairPrefix (n := n) i * switch (n := n) ⟨i, hi⟩) * pairTerm (n := n) i := by
              rw [hcomm.eq]
      _ = pairPrefix (n := n) i *
          (switch (n := n) ⟨i, hi⟩ * pairTerm (n := n) i) := by
              rw [mul_assoc]
      _ = pairPrefix (n := n) i *
          (-(pairTerm (n := n) i * switch (n := n) ⟨i, hi⟩)) := by
              rw [hanti]
      _ = -((pairPrefix (n := n) i * pairTerm (n := n) i) *
          switch (n := n) ⟨i, hi⟩) := by
              change pairPrefix (n := n) i *
                  (-(pairTerm (n := n) i * switch (n := n) ⟨i, hi⟩)) =
                - (pairPrefix (n := n) i *
                  (pairTerm (n := n) i * switch (n := n) ⟨i, hi⟩))
              exact mul_neg
                (a := pairPrefix (n := n) i)
                (b := pairTerm (n := n) i * switch (n := n) ⟨i, hi⟩)
  refine Nat.le_induction (m := i + 1)
    (P := fun m _ => m ≤ n →
      switch (n := n) ⟨i, hi⟩ * pairPrefix (n := n) m =
        -(pairPrefix (n := n) m * switch (n := n) ⟨i, hi⟩)) ?_ ?_ j
    (Nat.succ_le_iff.mpr hij) hj
  · intro
    exact hbase
  · intro m hm hprev hbound
    have hmi : i ≠ m := by
      intro h
      subst h
      exact (Nat.not_succ_le_self i) (by simpa using hm)
    have hcomm : Commute (switch (n := n) ⟨i, hi⟩) (pairTerm (n := n) m) :=
      switch_pairTerm_commute_of_ne hi (Nat.lt_of_succ_le hbound) hmi
    rw [pairPrefix_succ]
    calc
      switch (n := n) ⟨i, hi⟩ *
          (pairPrefix (n := n) m * pairTerm (n := n) m) =
          (switch (n := n) ⟨i, hi⟩ * pairPrefix (n := n) m) *
            pairTerm (n := n) m := by simp [mul_assoc]
      _ = (-(pairPrefix (n := n) m * switch (n := n) ⟨i, hi⟩)) *
            pairTerm (n := n) m := by
              rw [hprev (Nat.le_of_lt (Nat.lt_of_succ_le hbound))]
      _ = -(pairPrefix (n := n) m *
            (switch (n := n) ⟨i, hi⟩ * pairTerm (n := n) m)) := by
            exact neg_mul
              (pairPrefix (n := n) m * switch (n := n) ⟨i, hi⟩)
              (pairTerm (n := n) m)
      _ = -(pairPrefix (n := n) m *
            (pairTerm (n := n) m * switch (n := n) ⟨i, hi⟩)) := by
            rw [hcomm.eq]
      _ = -((pairPrefix (n := n) m * pairTerm (n := n) m) *
            switch (n := n) ⟨i, hi⟩) := by simp [mul_assoc]

theorem pairPrefix_commute_of_le {n m j : ℕ} (hmj : m ≤ j) :
    Commute (pairPrefix (n := n) m) (pairPrefix (n := n) j) := by
  refine Nat.le_induction (m := m)
    (P := fun j _ => Commute (pairPrefix (n := n) m) (pairPrefix (n := n) j)) ?_ ?_ j hmj
  · simp
  · intro j hj hcomm
    have hterm : Commute (pairPrefix (n := n) m) (pairTerm (n := n) j) :=
      (pairTerm_commute_pairPrefix (n := n) (m := m) (i := j) hj).symm
    simpa [pairPrefix_succ, mul_assoc] using hcomm.mul_right hterm

end FunctionSpace

end InfoGeometry.Canonical.CelikKocakPaperFormalism
