import InfoGeometry.Canonical.CelikKocakEndpointRankOne
import InfoGeometry.Canonical.CelikKocakPaperTiltSwitchClosure

/-!
# One-coordinate endpoint projectors

The diagonal matrix-unit factors are built natively from the tilt operators.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikKocakPaperFormalism

open FunctionSpace

noncomputable def coordinateProjector {n : ℕ}
    (i : Fin n) (b : Bool) : EndpointOperator n :=
    (1 / 2 : ℂ) •
    (1 + (if b then (-1 : ℂ) else 1) •
      InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.tilt
        (n := n) i)

theorem coordinateProjector_mem_paperTiltSwitchSubalgebra
    {n : ℕ} (i : Fin n) (b : Bool) :
    coordinateProjector i b ∈ paperTiltSwitchSubalgebra n := by
  let S := paperTiltSwitchSubalgebra n
  apply S.smul_mem
  apply S.add_mem S.one_mem
  apply S.smul_mem (paperTilt_mem_paperTiltSwitchSubalgebra i)

@[simp] theorem coordinateProjector_basis_apply
    {n : ℕ} (i : Fin n) (b : Bool) (z : CantorAddress n) :
    coordinateProjector i b
        (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z) =
      if z i = b then
        InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z
      else 0 := by
  apply funext
  intro w
  by_cases hwz : w = z
  · subst w
    cases b <;> cases hzi : z i <;>
      simp [coordinateProjector,
        InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.tilt, hzi] <;>
      norm_num
  · have hzw : z ≠ w := by
      intro h
      exact hwz h.symm
    cases b <;> cases hzi : z i <;>
      simp [coordinateProjector,
        InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.tilt,
        hwz, hzw, hzi] <;>
      norm_num

def orderedOperatorProduct {n : ℕ} :
    List (EndpointOperator n) → EndpointOperator n
  | [] => 1
  | a :: l => a * orderedOperatorProduct l

private theorem orderedOperatorProduct_mem
    {n : ℕ} (S : Subalgebra ℂ (EndpointOperator n)) :
    ∀ l : List (EndpointOperator n),
      (∀ T ∈ l, T ∈ S) → orderedOperatorProduct l ∈ S
  | [], _ => S.one_mem
  | a :: l, h => by
      exact S.mul_mem (h a (by simp))
        (orderedOperatorProduct_mem S l (by
          intro T hT
          exact h T (by simp [hT])))

private theorem orderedCoordinateProduct_basis_apply {n : ℕ}
    (l : List (Fin n)) (x z : CantorAddress n) :
    orderedOperatorProduct
        (l.map (fun i => coordinateProjector i (x i)))
        (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z) =
      if (∀ i ∈ l, z i = x i) then
        InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z
      else 0 := by
  induction l with
  | nil => simp [orderedOperatorProduct]
  | cons i l ih =>
      by_cases hzi : z i = x i
      · by_cases hl : ∀ j ∈ l, z j = x j
        · simp only [List.map_cons, orderedOperatorProduct]
          change coordinateProjector i (x i)
              (orderedOperatorProduct
                (l.map (fun j => coordinateProjector j (x j)))
                (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis
                  (n := n) z)) = _
          rw [ih]
          have hcons : ∀ j ∈ i :: l, z j = x j := by
            intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · exact hzi
            · exact hl j hj
          rw [if_pos hl, coordinateProjector_basis_apply, if_pos hcons]
          simp [hzi]
        · simp only [List.map_cons, orderedOperatorProduct]
          change coordinateProjector i (x i)
              (orderedOperatorProduct
                (l.map (fun j => coordinateProjector j (x j)))
                (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis
                  (n := n) z)) = _
          rw [ih]
          have hcons : ¬(∀ j ∈ i :: l, z j = x j) := by
            intro h
            exact hl (fun j hj => h j (by simp [hj]))
          rw [if_neg hl, if_neg hcons]
          simp
      · simp only [List.map_cons, orderedOperatorProduct]
        change coordinateProjector i (x i)
            (orderedOperatorProduct
              (l.map (fun j => coordinateProjector j (x j)))
              (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis
                (n := n) z)) = _
        rw [ih]
        have hcons : ¬(∀ j ∈ i :: l, z j = x j) := by
          intro h
          exact hzi (h i (by simp))
        rw [if_neg hcons]
        by_cases h : ∀ j ∈ l, z j = x j
        · rw [if_pos h, coordinateProjector_basis_apply]
          simp [hzi]
        · rw [if_neg h]
          simp

noncomputable def diagonalProjector {n : ℕ}
    (x : CantorAddress n) : EndpointOperator n :=
  orderedOperatorProduct
    ((Finset.univ : Finset (Fin n)).toList.map
      (fun i => coordinateProjector i (x i)))

theorem diagonalProjector_mem_paperTiltSwitchSubalgebra
    {n : ℕ} (x : CantorAddress n) :
    diagonalProjector x ∈ paperTiltSwitchSubalgebra n := by
  classical
  let S := paperTiltSwitchSubalgebra n
  apply orderedOperatorProduct_mem S
  intro T hT
  rcases List.mem_map.1 hT with ⟨i, hi, rfl⟩
  exact coordinateProjector_mem_paperTiltSwitchSubalgebra i (x i)

theorem diagonalProjector_basis_apply
    {n : ℕ} (x z : CantorAddress n) :
    diagonalProjector x
        (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z) =
      if z = x then
        InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z
      else 0 := by
  classical
  by_cases hzx : z = x
  · subst z
    simpa [diagonalProjector] using
      (orderedCoordinateProduct_basis_apply
        ((Finset.univ : Finset (Fin n)).toList) x x)
  · have hnot :
        ¬ (∀ i ∈ (Finset.univ : Finset (Fin n)).toList, z i = x i) := by
      intro hall
      apply hzx
      funext i
      exact hall i (by simp)
    have hnot' : ¬ (∀ i : Fin n, z i = x i) := by
      intro hall
      apply hzx
      funext i
      exact hall i
    simpa [diagonalProjector, hzx, hnot, hnot'] using
      (orderedCoordinateProduct_basis_apply
        ((Finset.univ : Finset (Fin n)).toList) x z)

theorem diagonalProjector_mul
    {n : ℕ} (x y : CantorAddress n) :
    diagonalProjector x * diagonalProjector y =
      if x = y then diagonalProjector x else 0 := by
  classical
  apply (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis
    (n := n)).ext
  intro z
  change diagonalProjector x (diagonalProjector y
      (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z)) =
    (if x = y then diagonalProjector x else 0)
      (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z)
  by_cases hzy : z = y
  · subst z
    rw [diagonalProjector_basis_apply]
    by_cases hxy : x = y
    · subst x
      simp [diagonalProjector_basis_apply]
    · have hy :
          (if y = y then
              InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) y
            else 0) =
            InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) y :=
        if_pos rfl
      rw [hy]
      rw [diagonalProjector_basis_apply (x := x) (z := y)]
      have hyx : ¬y = x := fun h => hxy h.symm
      simp [hxy, hyx]
  · rw [diagonalProjector_basis_apply (x := y) (z := z)]
    rw [if_neg hzy]
    by_cases hxy : x = y
    · subst x
      simp only [if_true]
      rw [diagonalProjector_basis_apply (x := y) (z := z)]
      simp [hzy]
    · rw [if_neg hxy]
      simp

theorem switch_basis_apply {n : ℕ} (i : Fin n) (z : CantorAddress n) :
    InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.switch i
        (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z) =
      InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis
        (n := n)
        (InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt i z) := by
  apply funext
  intro w
  change
    (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z)
        (InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt i w) =
      (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n)
        (InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt i z)) w
  by_cases hw : w =
      InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt i z
  · subst w
    rw [InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt_involutive]
    simp [InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis_apply]
  · have hzw :
        InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt i z ≠ w :=
      Ne.symm hw
    have hnot :
        InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt i w ≠ z := by
      intro h
      apply hw
      have h' := congrArg
        (InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt i) h
      rw [InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt_involutive] at h'
      exact h'
    simp [InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis_apply,
      hzw, hnot]

def orderedFlip {n : ℕ} : List (Fin n) → CantorAddress n → CantorAddress n
  | [], z => z
  | i :: l, z =>
      InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt i
        (orderedFlip l z)

theorem orderedSwitchProduct_basis_apply {n : ℕ}
    (l : List (Fin n)) (z : CantorAddress n) :
    orderedOperatorProduct
        (l.map (fun i =>
          InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.switch i))
        (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z) =
      InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n)
        (orderedFlip l z) := by
  induction l with
  | nil => simp [orderedOperatorProduct, orderedFlip]
  | cons i l ih =>
      simp only [List.map_cons, orderedOperatorProduct]
      change InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.switch i
          (orderedOperatorProduct
            (l.map (fun j =>
              InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.switch j))
            (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z)) = _
      rw [ih, switch_basis_apply]
      rfl

private theorem orderedFlip_apply_of_nodup {n : ℕ}
    (l : List (Fin n)) (hl : l.Nodup) (z : CantorAddress n) (k : Fin n) :
    orderedFlip l z k = if k ∈ l then ! (z k) else z k := by
  induction l with
  | nil => simp [orderedFlip]
  | cons i l ih =>
      simp only [orderedFlip]
      have hlt : l.Nodup := (List.nodup_cons.mp hl).2
      have hil : i ∉ l := (List.nodup_cons.mp hl).1
      by_cases hki : k = i
      · subst k
        rw [InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt_apply_eq]
        rw [ih hlt]
        simp [hil]
      · have hkl : k ∉ l ↔ k ∉ i :: l := by
          simp [hki]
        by_cases hkl' : k ∈ l
        · have hik : i ≠ k := Ne.symm hki
          rw [InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt_apply_ne
            hki]
          rw [ih hlt]
          simp [hkl', hki]
        · rw [InfoGeometry.Canonical.CelikKocakCantorOperators.CantorAddress.flipAt_apply_ne
            hki]
          rw [ih hlt]
          simp [hkl', hki]

noncomputable def switchWord {n : ℕ}
    (x y : CantorAddress n) : EndpointOperator n :=
  orderedOperatorProduct
    (((Finset.univ : Finset (Fin n)).filter
      (fun i => decide (x i ≠ y i))).toList.map
      (fun i => InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.switch i))

theorem switchWord_basis_apply {n : ℕ}
    (x y : CantorAddress n) :
    switchWord x y
        (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) y) =
      InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) x := by
  classical
  let s : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun i => decide (x i ≠ y i))
  have hs : s.toList.Nodup := s.nodup_toList
  have haddr : orderedFlip s.toList y = x := by
    funext i
    rw [orderedFlip_apply_of_nodup s.toList hs y i]
    have hmem : i ∈ s.toList ↔ x i ≠ y i := by
      simp [s]
    by_cases h : x i = y i
    · simp [hmem, h]
    · have hflip : x i = !(y i) := by
        cases hy : y i <;> cases hx : x i <;> simp_all
      simp [hmem, h, hflip]
  change orderedOperatorProduct
      (s.toList.map (fun i =>
        InfoGeometry.Canonical.CelikKocakCantorOperators.FunctionSpace.switch i))
      (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) y) = _
  rw [orderedSwitchProduct_basis_apply, haddr]

theorem switchWord_mem_paperTiltSwitchSubalgebra
    {n : ℕ} (x y : CantorAddress n) :
    switchWord x y ∈ paperTiltSwitchSubalgebra n := by
  classical
  apply orderedOperatorProduct_mem (paperTiltSwitchSubalgebra n)
  intro T hT
  rcases List.mem_map.1 hT with ⟨i, hi, rfl⟩
  exact paperSwitch_mem_paperTiltSwitchSubalgebra i

theorem diagonalSwitchDiagonal_eq_rankOne
    {n : ℕ} (x y : CantorAddress n) :
    diagonalProjector x * switchWord x y * diagonalProjector y =
      endpointRankOne x y := by
  apply (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis
    (n := n)).ext
  intro z
  change diagonalProjector x
      (switchWord x y
        (diagonalProjector y
          (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z))) =
    endpointRankOne x y
      (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z)
  by_cases hzy : z = y
  · subst z
    rw [diagonalProjector_basis_apply, if_pos rfl]
    rw [switchWord_basis_apply]
    rw [diagonalProjector_basis_apply, if_pos rfl]
    simpa [endpointRankOne]
  · rw [diagonalProjector_basis_apply, if_neg hzy]
    have hyz : ¬y = z := fun h => hzy h.symm
    simp only [map_zero]
    have hr : endpointRankOne x y
        (InfoGeometry.Canonical.CelikKocakCantorOperators.endpointBasis (n := n) z) = 0 := by
      simpa [hyz] using
        (endpointRankOne_basis_apply (x := x) (y := y) (z := z))
    rw [hr]

theorem paperTiltSwitchSubalgebra_eq_top (n : ℕ) :
    paperTiltSwitchSubalgebra n = ⊤ := by
  apply le_antisymm le_top
  intro A _
  rw [endpointOperator_eq_rankOne_sum A]
  apply (paperTiltSwitchSubalgebra n).sum_mem
  intro y hy
  apply (paperTiltSwitchSubalgebra n).sum_mem
  intro x hx
  apply (paperTiltSwitchSubalgebra n).smul_mem
  rw [← diagonalSwitchDiagonal_eq_rankOne x y]
  apply (paperTiltSwitchSubalgebra n).mul_mem
  · apply (paperTiltSwitchSubalgebra n).mul_mem
    · exact diagonalProjector_mem_paperTiltSwitchSubalgebra x
    · exact switchWord_mem_paperTiltSwitchSubalgebra x y
  · exact diagonalProjector_mem_paperTiltSwitchSubalgebra y

theorem paperGeneratorSubalgebra_eq_top (n : ℕ) :
    paperGeneratorSubalgebra n = ⊤ := by
  rw [paperGeneratorSubalgebra_eq_paperTiltSwitchSubalgebra]
  exact paperTiltSwitchSubalgebra_eq_top n

end InfoGeometry.Canonical.CelikKocakPaperFormalism
