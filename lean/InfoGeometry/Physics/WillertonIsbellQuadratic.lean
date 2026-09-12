import InfoGeometry.Physics.WillertonIsbellAmariDuality

open scoped BigOperators

namespace InfoGeometry.Physics.WillertonIsbellAmari

noncomputable section

def quadraticPotential {D : ℕ} (x : Fin D → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, (x i) ^ 2

def quadraticIsbellPair (D : ℕ) : IsbellLegendrePair D where
  f := quadraticPotential
  f_star := quadraticPotential
  fenchel_young_ineq := by
    intro x y
    have hs : 0 ≤ ∑ i : Fin D, (x i - y i) ^ 2 := by
      exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i - y i))
    have hident : (∑ i : Fin D, (x i - y i) ^ 2) =
        (∑ i : Fin D, (x i) ^ 2) + (∑ i : Fin D, (y i) ^ 2) -
          2 * (∑ i : Fin D, x i * y i) := by
      calc
        (∑ i : Fin D, (x i - y i) ^ 2) =
            ∑ i : Fin D, ((x i)^2 + (y i)^2 - 2 * (x i * y i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (∑ i : Fin D, (x i)^2) + (∑ i : Fin D, (y i)^2) -
              2 * (∑ i : Fin D, x i * y i) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    dsimp [quadraticPotential, pairing]
    nlinarith [hs, hident]
  contact_map := fun x => x
  contact_equality := by
    intro x
    dsimp [quadraticPotential, pairing]
    ring

theorem quadratic_bregman_nonneg {D : ℕ} (x y : Fin D → ℝ) :
    0 ≤ bregmanDivergence (quadraticIsbellPair D) x y :=
  bregmanDivergence_nonneg (quadraticIsbellPair D) x y

theorem quadratic_bregman_self {D : ℕ} (x : Fin D → ℝ) :
    bregmanDivergence (quadraticIsbellPair D) x x = 0 :=
  bregmanDivergence_self (quadraticIsbellPair D) x

/-- The quadratic Bregman divergence is exactly the squared Euclidean
    displacement, with the conventional factor `1/2`. -/
theorem quadratic_bregman_eq_half_sq_distance {D : ℕ} (x y : Fin D → ℝ) :
    bregmanDivergence (quadraticIsbellPair D) x y =
      (1 / 2 : ℝ) * ∑ i : Fin D, (x i - y i) ^ 2 := by
  simp only [bregmanDivergence, adjunctionSlack, quadraticIsbellPair,
    quadraticPotential, pairing, sub_sq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  simp only [← Finset.mul_sum]
  have hxy : (∑ i : Fin D, x i * y i * 2) = 2 * (∑ i : Fin D, x i * y i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hxy' : (∑ i : Fin D, 2 * x i * y i) = 2 * (∑ i : Fin D, x i * y i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hxy']
  ring

theorem quadratic_bregman_eq_zero_iff {D : ℕ} (x y : Fin D → ℝ) :
    bregmanDivergence (quadraticIsbellPair D) x y = 0 ↔ x = y := by
  rw [quadratic_bregman_eq_half_sq_distance]
  constructor
  · intro h
    funext i
    have hi : (x i - y i) ^ 2 = 0 := by
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (x j - y j))).mp (by nlinarith [h]) i (Finset.mem_univ i)
      exact hs
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    subst h
    simp

theorem quadratic_bregman_comm {D : ℕ} (x y : Fin D → ℝ) :
    bregmanDivergence (quadraticIsbellPair D) x y =
      bregmanDivergence (quadraticIsbellPair D) y x := by
  rw [quadratic_bregman_eq_half_sq_distance, quadratic_bregman_eq_half_sq_distance]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

end
end InfoGeometry.Physics.WillertonIsbellAmari
