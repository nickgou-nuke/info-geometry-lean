import InfoGeometry.Canonical.CantorCuntzRangeProjectionMurrayVonNeumann
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Topology

noncomputable section

open InfoGeometry.OperatorAlgebra

variable {Op : Type*} [Ring Op] [StarRing Op]

namespace CuntzO2Carrier

variable (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op)

def branchWord (C : InfoGeometry.Algebra.Cuntz.CuntzNAlgebra (N := 2) Op) : List Bool → Op
  | [] => 1
  | false :: w => InfoGeometry.Topology.CuntzO2Carrier.S_left C * branchWord C w
  | true :: w => InfoGeometry.Topology.CuntzO2Carrier.S_right C * branchWord C w

@[simp] theorem branchWord_nil : branchWord C [] = 1 := rfl

@[simp] theorem branchWord_false (w : List Bool) :
    branchWord C (false :: w) = InfoGeometry.Topology.CuntzO2Carrier.S_left C * branchWord C w := rfl

@[simp] theorem branchWord_true (w : List Bool) :
    branchWord C (true :: w) = InfoGeometry.Topology.CuntzO2Carrier.S_right C * branchWord C w := rfl

theorem branchWord_append (u v : List Bool) :
    branchWord C (u ++ v) = branchWord C u * branchWord C v := by
  induction u with
  | nil => simp
  | cons b u ih =>
      cases b <;> simp [List.cons_append, ih, mul_assoc]

theorem branchWord_isometry (w : List Bool) :
    star (branchWord C w) * branchWord C w = 1 := by
  induction w with
  | nil => simp [branchWord]
  | cons b w ih =>
      cases b with
      | false =>
          simp only [branchWord, star_mul]
          calc
            star (branchWord C w) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
                (InfoGeometry.Topology.CuntzO2Carrier.S_left C * branchWord C w) =
                star (branchWord C w) *
                  (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) * branchWord C w := by
                    noncomm_ring
            _ = star (branchWord C w) * branchWord C w := by
              rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]
              simp
            _ = 1 := ih

      | true =>
          simp only [branchWord, star_mul]
          calc
            star (branchWord C w) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
                (InfoGeometry.Topology.CuntzO2Carrier.S_right C * branchWord C w) =
                star (branchWord C w) *
                  (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) * branchWord C w := by
                    noncomm_ring
            _ = star (branchWord C w) * branchWord C w := by
              rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]
              simp
            _ = 1 := ih

theorem branchWord_ne_zero [Nontrivial Op] (w : List Bool) :
    branchWord C w ≠ 0 := by
  intro h
  have hw := branchWord_isometry C w
  rw [h, star_zero, zero_mul] at hw
  exact zero_ne_one hw

theorem branchWord_orthogonal
    (u v : List Bool)
    (hlen : u.length = v.length)
    (hne : u ≠ v) :
    star (branchWord C u) * branchWord C v = 0 := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => exact (hne rfl).elim
      | cons b v => simp at hlen
  | cons b u ih =>
      cases v with
      | nil => simp at hlen
      | cons c v =>
          have htail : u.length = v.length := by simpa using hlen
          cases b with
          | false =>
              cases c with
              | false =>
                  simp only [branchWord, star_mul]
                  calc
                    star (branchWord C u) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
                        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * branchWord C v) =
                        star (branchWord C u) *
                          (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
                            branchWord C v := by noncomm_ring
                    _ = star (branchWord C u) * branchWord C v := by
                      rw [InfoGeometry.Topology.CuntzO2Carrier.left_isometry C]
                      simp
                    _ = 0 := ih v htail (by
                      intro huv
                      apply hne
                      simp [huv])
              | true =>
                  simp only [branchWord, star_mul]
                  calc
                    star (branchWord C u) * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
                        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * branchWord C v) =
                        star (branchWord C u) *
                          (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
                            branchWord C v := by noncomm_ring
                    _ = 0 := by
                      rw [(InfoGeometry.Topology.CuntzO2Carrier.orthogonal_ranges C).1]
                      simp
          | true =>
              cases c with
              | false =>
                  simp only [branchWord, star_mul]
                  calc
                    star (branchWord C u) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
                        (InfoGeometry.Topology.CuntzO2Carrier.S_left C * branchWord C v) =
                        star (branchWord C u) *
                          (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
                            branchWord C v := by noncomm_ring
                    _ = 0 := by
                      rw [(InfoGeometry.Topology.CuntzO2Carrier.orthogonal_ranges C).2]
                      simp
              | true =>
                  simp only [branchWord, star_mul]
                  calc
                    star (branchWord C u) * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
                        (InfoGeometry.Topology.CuntzO2Carrier.S_right C * branchWord C v) =
                        star (branchWord C u) *
                          (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
                            branchWord C v := by noncomm_ring
                    _ = star (branchWord C u) * branchWord C v := by
                      rw [InfoGeometry.Topology.CuntzO2Carrier.right_isometry C]
                      simp
                    _ = 0 := ih v htail (by
                      intro huv
                      apply hne
                      simp [huv])
def branchRangeProjection (w : List Bool) : Op :=
  branchWord C w * star (branchWord C w)

@[simp] theorem branchRangeProjection_nil :
    branchRangeProjection C [] = (1 : Op) := by
  simp [branchRangeProjection]

theorem branchRangeProjection_singleton_false :
    branchRangeProjection C [false] =
      InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection C := by
  simp [branchRangeProjection,
    InfoGeometry.Topology.CuntzO2Carrier.leftRangeProjection]

theorem branchRangeProjection_singleton_true :
    branchRangeProjection C [true] =
      InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection C := by
  simp [branchRangeProjection,
    InfoGeometry.Topology.CuntzO2Carrier.rightRangeProjection]

theorem branchRangeProjection_append (u v : List Bool) :
    branchRangeProjection C (u ++ v) =
      branchWord C u * branchRangeProjection C v * star (branchWord C u) := by
  unfold branchRangeProjection
  rw [branchWord_append C, star_mul]
  noncomm_ring

theorem branchRangeProjection_idempotent (w : List Bool) :
    branchRangeProjection C w * branchRangeProjection C w =
      branchRangeProjection C w := by
  unfold branchRangeProjection
  calc
    branchWord C w * star (branchWord C w) *
        (branchWord C w * star (branchWord C w)) =
        branchWord C w *
          (star (branchWord C w) * branchWord C w) *
            star (branchWord C w) := by noncomm_ring
    _ = branchWord C w * star (branchWord C w) := by
      rw [branchWord_isometry C]
      simp

theorem branchRangeProjection_mul_append (u v : List Bool) :
    branchRangeProjection C u * branchRangeProjection C (u ++ v) =
      branchRangeProjection C (u ++ v) := by
  rw [branchRangeProjection_append C]
  unfold branchRangeProjection
  calc
    branchWord C u * star (branchWord C u) *
          (branchWord C u * (branchWord C v * star (branchWord C v)) *
            star (branchWord C u)) =
        branchWord C u *
          (star (branchWord C u) * branchWord C u) *
            (branchWord C v * star (branchWord C v)) *
              star (branchWord C u) := by
                noncomm_ring
    _ = branchWord C u * (branchWord C v * star (branchWord C v)) *
          star (branchWord C u) := by
            rw [branchWord_isometry C]
            noncomm_ring

theorem branchRangeProjection_append_mul (u v : List Bool) :
    branchRangeProjection C (u ++ v) * branchRangeProjection C u =
      branchRangeProjection C (u ++ v) := by
  rw [branchRangeProjection_append C]
  unfold branchRangeProjection
  calc
    (branchWord C u * (branchWord C v * star (branchWord C v)) *
          star (branchWord C u)) *
        (branchWord C u * star (branchWord C u)) =
      branchWord C u * (branchWord C v * star (branchWord C v)) *
        (star (branchWord C u) * branchWord C u) *
          star (branchWord C u) := by
            noncomm_ring
    _ = branchWord C u * (branchWord C v * star (branchWord C v)) *
          star (branchWord C u) := by
            rw [branchWord_isometry C]
            noncomm_ring

theorem branchRangeProjection_mul_branchWord (w : List Bool) :
    branchRangeProjection C w * branchWord C w = branchWord C w := by
  unfold branchRangeProjection
  calc
    branchWord C w * star (branchWord C w) * branchWord C w =
        branchWord C w * (star (branchWord C w) * branchWord C w) := by
      noncomm_ring
    _ = branchWord C w := by
      rw [branchWord_isometry C w]
      simp

theorem branchRangeProjection_ne_zero [Nontrivial Op] (w : List Bool) :
    branchRangeProjection C w ≠ 0 := by
  intro h
  have hw := branchRangeProjection_mul_branchWord C w
  rw [h, zero_mul] at hw
  exact branchWord_ne_zero C w hw.symm

theorem branchWord_mul_sourceProjection (w : List Bool) :
    branchWord C w * (star (branchWord C w) * branchWord C w) =
      branchWord C w := by
  rw [branchWord_isometry C w]
  simp

theorem branchRangeProjection_star (w : List Bool) :
    star (branchRangeProjection C w) = branchRangeProjection C w := by
  unfold branchRangeProjection
  rw [star_mul, star_star]

theorem branchRangeProjection_isStarProjection (w : List Bool) :
    IsStarProjection (branchRangeProjection C w) := by
  rw [isStarProjection_iff]
  exact ⟨branchRangeProjection_idempotent C w,
    branchRangeProjection_star C w⟩

theorem branchRangeProjection_orthogonal
    (u v : List Bool)
    (hlen : u.length = v.length)
    (hne : u ≠ v) :
    branchRangeProjection C u * branchRangeProjection C v = 0 := by
  unfold branchRangeProjection
  calc
    branchWord C u * star (branchWord C u) *
        (branchWord C v * star (branchWord C v)) =
        branchWord C u *
          (star (branchWord C u) * branchWord C v) *
            star (branchWord C v) := by noncomm_ring
    _ = 0 := by
      rw [branchWord_orthogonal C u v hlen hne]
      simp

theorem branchRangeProjection_append_orthogonal
    (u v w : List Bool)
    (hlen : u.length = v.length)
    (hne : u ≠ v) :
    branchRangeProjection C (u ++ w) *
        branchRangeProjection C (v ++ w) = 0 := by
  apply branchRangeProjection_orthogonal C (u ++ w) (v ++ w)
  · simp [hlen]
  · intro huv
    apply hne
    exact List.append_left_injective w huv

theorem branchRangeProjection_children_sum (w : List Bool) :
    branchRangeProjection C (w ++ [false]) +
        branchRangeProjection C (w ++ [true]) =
      branchRangeProjection C w := by
  unfold branchRangeProjection
  rw [branchWord_append C, branchWord_append C]
  simp only [branchWord, mul_one, star_mul]
  calc
    (branchWord C w * InfoGeometry.Topology.CuntzO2Carrier.S_left C) *
          (star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) * star (branchWord C w)) +
        (branchWord C w * InfoGeometry.Topology.CuntzO2Carrier.S_right C) *
          (star (InfoGeometry.Topology.CuntzO2Carrier.S_right C) * star (branchWord C w)) =
        branchWord C w *
          (InfoGeometry.Topology.CuntzO2Carrier.S_left C * star (InfoGeometry.Topology.CuntzO2Carrier.S_left C) + InfoGeometry.Topology.CuntzO2Carrier.S_right C * star (InfoGeometry.Topology.CuntzO2Carrier.S_right C)) *
            star (branchWord C w) := by
              noncomm_ring
    _ = branchWord C w * 1 * star (branchWord C w) := by
      rw [InfoGeometry.Topology.CuntzO2Carrier.range_sum C]
    _ = branchWord C w * star (branchWord C w) := by simp

def levelWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (levelWords n).flatMap (fun w => [w ++ [false], w ++ [true]])

theorem levelWords_length (n : Nat) :
    (levelWords n).length = 2 ^ n := by
  induction n with
  | zero => simp [levelWords]
  | succ n ih =>
      simp [levelWords, List.length_flatMap, ih, pow_succ]

theorem levelWords_mem_length {n : Nat} {w : List Bool}
    (hw : w ∈ levelWords n) : w.length = n := by
  induction n generalizing w with
  | zero =>
      simpa [levelWords] using hw
  | succ n ih =>
      simp only [levelWords, List.mem_flatMap] at hw
      rcases hw with ⟨u, hu, hw⟩
      have hu_length : u.length = n := ih hu
      simp only [List.mem_cons] at hw
      rcases hw with hfalse | hrest
      · subst w
        simp [hu_length]
      · rcases hrest with htrue | hnil
        · subst w
          simp [hu_length]
        · simp at hnil

theorem branchRangeProjection_level_orthogonal
    {n : Nat} {u v : List Bool}
    (hu : u ∈ levelWords n)
    (hv : v ∈ levelWords n)
    (hne : u ≠ v) :
    branchRangeProjection C u * branchRangeProjection C v = 0 := by
  apply branchRangeProjection_orthogonal C u v
  · rw [levelWords_mem_length hu, levelWords_mem_length hv]
  · exact hne

theorem branchRangeProjection_level_pairwise_orthogonal
    {n : Nat} {u v : List Bool}
    (hu : u ∈ levelWords n)
    (hv : v ∈ levelWords n)
    (hne : u ≠ v) :
    branchRangeProjection C u * branchRangeProjection C v = 0 ∧
      branchRangeProjection C v * branchRangeProjection C u = 0 := by
  constructor
  · exact branchRangeProjection_level_orthogonal C hu hv hne
  · exact branchRangeProjection_level_orthogonal C hv hu (Ne.symm hne)

theorem branchRangeProjection_level_sum (n : Nat) :
    ((levelWords n).map (branchRangeProjection C)).sum = 1 := by
  have expand : ∀ ws : List (List Bool),
      ((ws.flatMap (fun w => [w ++ [false], w ++ [true]])).map
        (branchRangeProjection C)).sum =
        (ws.map (branchRangeProjection C)).sum := by
    intro ws
    induction ws with
    | nil => simp
    | cons w ws ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
        calc
          branchRangeProjection C (w ++ [false]) +
                (branchRangeProjection C (w ++ [true]) + 0) +
                (List.map (branchRangeProjection C)
                  (List.flatMap (fun w => [w ++ [false], w ++ [true]]) ws)).sum =
              (branchRangeProjection C (w ++ [false]) +
                branchRangeProjection C (w ++ [true])) +
                (List.map (branchRangeProjection C)
                  (List.flatMap (fun w => [w ++ [false], w ++ [true]]) ws)).sum := by
                    simp [add_assoc]
          _ = branchRangeProjection C w +
                (List.map (branchRangeProjection C)
                  (List.flatMap (fun w => [w ++ [false], w ++ [true]]) ws)).sum := by
                    rw [branchRangeProjection_children_sum C w]
          _ = branchRangeProjection C w +
                (List.map (branchRangeProjection C) ws).sum := by
                    rw [ih]
  induction n with
  | zero => simp [levelWords, branchRangeProjection]
  | succ n ih =>
      rw [levelWords, expand, ih]

theorem branchRangeProjection_level_sum_mul
    (n : Nat) (w : List Bool) :
    ((levelWords n).map (branchRangeProjection C)).sum *
        branchRangeProjection C w = branchRangeProjection C w := by
  rw [branchRangeProjection_level_sum C n]
  simp

theorem branchRangeProjection_mul_level_sum
    (n : Nat) (w : List Bool) :
    branchRangeProjection C w *
        ((levelWords n).map (branchRangeProjection C)).sum =
      branchRangeProjection C w := by
  rw [branchRangeProjection_level_sum C n]
  simp

theorem branchRangeProjection_children_orthogonal (w : List Bool) :
    branchRangeProjection C (w ++ [false]) *
          branchRangeProjection C (w ++ [true]) = 0 ∧
      branchRangeProjection C (w ++ [true]) *
          branchRangeProjection C (w ++ [false]) = 0 := by
  have hlen : (w ++ [false]).length = (w ++ [true]).length := by
    simp
  constructor
  · unfold branchRangeProjection
    calc
      branchWord C (w ++ [false]) *
          star (branchWord C (w ++ [false])) *
          (branchWord C (w ++ [true]) *
            star (branchWord C (w ++ [true]))) =
          branchWord C (w ++ [false]) *
            (star (branchWord C (w ++ [false])) *
              branchWord C (w ++ [true])) *
              star (branchWord C (w ++ [true])) := by
                noncomm_ring
      _ = 0 := by
        rw [branchWord_orthogonal C (w ++ [false]) (w ++ [true]) hlen (by simp)]
        simp
  · unfold branchRangeProjection
    calc
      branchWord C (w ++ [true]) *
          star (branchWord C (w ++ [true])) *
          (branchWord C (w ++ [false]) *
            star (branchWord C (w ++ [false]))) =
          branchWord C (w ++ [true]) *
            (star (branchWord C (w ++ [true])) *
              branchWord C (w ++ [false])) *
              star (branchWord C (w ++ [false])) := by
                noncomm_ring
      _ = 0 := by
        rw [branchWord_orthogonal C (w ++ [true]) (w ++ [false]) hlen.symm (by simp)]
        simp

theorem branchRangeProjection_murrayVonNeumannEquivalent_child
    (w : List Bool) (b : Bool) :
    MurrayVonNeumannEquivalent
      (branchRangeProjection C w)
      (branchRangeProjection C (w ++ [b])) := by
  cases b with
  | false =>
      refine ⟨branchWord C w * S_left C * star (branchWord C w), ?_, ?_⟩
      · simp only [star_mul, star_star]
        calc
          branchWord C w * (star (S_left C) * star (branchWord C w)) *
                (branchWord C w * S_left C * star (branchWord C w)) =
              branchWord C w * star (S_left C) *
                (star (branchWord C w) * branchWord C w) *
                S_left C * star (branchWord C w) := by noncomm_ring
          _ = branchWord C w * (star (S_left C) * S_left C) *
                star (branchWord C w) := by
              rw [branchWord_isometry C]
              noncomm_ring
          _ = branchRangeProjection C w := by
              rw [left_isometry C]
              simp [branchRangeProjection]
      · calc
          (branchWord C w * S_left C * star (branchWord C w)) *
                (star (branchWord C w * S_left C *
                star (branchWord C w))) =
              branchWord C w * S_left C *
                (star (branchWord C w) * branchWord C w) *
                star (S_left C) * star (branchWord C w) := by
                  simp only [star_mul, star_star]
                  noncomm_ring
          _ = branchWord C w * S_left C * star (S_left C) *
                star (branchWord C w) := by
              rw [branchWord_isometry C]
              simp
          _ = branchRangeProjection C (w ++ [false]) := by
              simp only [branchRangeProjection, branchWord_append, star_mul,
                branchWord_false, branchWord_nil, mul_one, star_star]
              noncomm_ring
  | true =>
      refine ⟨branchWord C w * S_right C * star (branchWord C w), ?_, ?_⟩
      · simp only [star_mul, star_star]
        calc
          branchWord C w * (star (S_right C) * star (branchWord C w)) *
                (branchWord C w * S_right C * star (branchWord C w)) =
              branchWord C w * star (S_right C) *
                (star (branchWord C w) * branchWord C w) *
                S_right C * star (branchWord C w) := by noncomm_ring
          _ = branchWord C w * (star (S_right C) * S_right C) *
                star (branchWord C w) := by
              rw [branchWord_isometry C]
              noncomm_ring
          _ = branchRangeProjection C w := by
              rw [right_isometry C]
              simp [branchRangeProjection]
      · calc
          (branchWord C w * S_right C * star (branchWord C w)) *
                (star (branchWord C w * S_right C *
                star (branchWord C w))) =
              branchWord C w * S_right C *
                (star (branchWord C w) * branchWord C w) *
                star (S_right C) * star (branchWord C w) := by
                  simp only [star_mul, star_star]
                  noncomm_ring
          _ = branchWord C w * S_right C * star (S_right C) *
                star (branchWord C w) := by
              rw [branchWord_isometry C]
              simp
          _ = branchRangeProjection C (w ++ [true]) := by
              simp only [branchRangeProjection, branchWord_append, star_mul,
                branchWord_true, branchWord_nil, mul_one, star_star]
              noncomm_ring

theorem branchRangeProjection_murrayVonNeumannEquivalent_append
    (u v : List Bool) :
    MurrayVonNeumannEquivalent
      (branchRangeProjection C u)
      (branchRangeProjection C (u ++ v)) := by
  induction v generalizing u with
  | nil =>
      simpa using mvn_refl
        (p := branchRangeProjection C u)
        ⟨branchRangeProjection_idempotent C u,
          branchRangeProjection_star C u⟩
  | cons b v ih =>
      have hchild := branchRangeProjection_murrayVonNeumannEquivalent_child C u b
      have htail := ih (u ++ [b])
      have htrans := mvn_trans
        (hp := ⟨branchRangeProjection_idempotent C u,
          branchRangeProjection_star C u⟩)
        (hr := ⟨branchRangeProjection_idempotent C ((u ++ [b]) ++ v),
          branchRangeProjection_star C ((u ++ [b]) ++ v)⟩)
        hchild htail
      simpa [List.append_assoc] using htrans

theorem unit_murrayVonNeumannEquivalent_branchRangeProjection
    (w : List Bool) :
    MurrayVonNeumannEquivalent (1 : Op) (branchRangeProjection C w) := by
  refine ⟨branchWord C w, ?_, ?_⟩
  · exact branchWord_isometry C w
  · rfl

theorem branchRangeProjection_murrayVonNeumannEquivalent_unit
    (w : List Bool) :
    MurrayVonNeumannEquivalent (branchRangeProjection C w) (1 : Op) := by
  exact mvn_symm (unit_murrayVonNeumannEquivalent_branchRangeProjection C w)

theorem branchRangeProjection_murrayVonNeumannEquivalent
    (u v : List Bool) :
    MurrayVonNeumannEquivalent
      (branchRangeProjection C u)
      (branchRangeProjection C v) := by
  apply mvn_trans
    (hp := ⟨branchRangeProjection_idempotent C u,
      branchRangeProjection_star C u⟩)
    (hr := ⟨branchRangeProjection_idempotent C v,
      branchRangeProjection_star C v⟩)
      (branchRangeProjection_murrayVonNeumannEquivalent_unit C u)
  exact mvn_symm (branchRangeProjection_murrayVonNeumannEquivalent_unit C v)

end CuntzO2Carrier

end
end InfoGeometry.Topology
