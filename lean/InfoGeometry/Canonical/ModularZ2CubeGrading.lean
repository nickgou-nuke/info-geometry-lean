import Mathlib.Tactic

/-!
# Grand-Canonical Modular Theory and Z₂³ Operator Grading
-/

variable {A : Type*} [Ring A]
variable (Γ_R Γ_χ Γ_N : A)

class ModularZ2CubeGrading (Γ_R Γ_χ Γ_N : A) where
  inv_R : Γ_R * Γ_R = 1
  inv_χ : Γ_χ * Γ_χ = 1
  inv_N : Γ_N * Γ_N = 1
  comm_R_χ : Γ_R * Γ_χ = Γ_χ * Γ_R
  comm_R_N : Γ_R * Γ_N = Γ_N * Γ_R
  comm_χ_N : Γ_χ * Γ_N = Γ_N * Γ_χ

namespace ModularZ2CubeGrading

def hasGrading (Γ X : A) (is_odd : Bool) : Prop :=
  if is_odd then Γ * X + X * Γ = 0 else Γ * X = X * Γ

def isHomogeneous (X : A) (e_R e_χ e_N : Bool) : Prop :=
  hasGrading Γ_R X e_R ∧
  hasGrading Γ_χ X e_χ ∧
  hasGrading Γ_N X e_N

def isFullyEven (X : A) : Prop :=
  isHomogeneous Γ_R Γ_χ Γ_N X false false false

def isFullyOdd (X : A) : Prop :=
  isHomogeneous Γ_R Γ_χ Γ_N X true true true

def isTotalNumberLike (N_op : A) : Prop := isFullyEven Γ_R Γ_χ Γ_N N_op
def isChiralChargeLike (Q_χ : A) : Prop := isFullyEven Γ_R Γ_χ Γ_N Q_χ
def isWedgeHamiltonianLike (H : A) : Prop := isFullyEven Γ_R Γ_χ Γ_N H

def isChiralMassLike (M : A) : Prop :=
  isHomogeneous Γ_R Γ_χ Γ_N M false true false

def isNambuPairingLike (P : A) : Prop :=
  isHomogeneous Γ_R Γ_χ Γ_N P false false true

variable {H_R N_op Q_χ : A}
variable {β_U μ μ_χ : A}

class Central (c : A) where
  commutes (X : A) : c * X = X * c

variable [Central β_U] [Central μ] [Central μ_χ]

lemma hasGrading_add {Γ X Y : A} {b : Bool} (hx : hasGrading Γ X b) (hy : hasGrading Γ Y b) :
    hasGrading Γ (X + Y) b := by
  cases b
  · change Γ * X = X * Γ at hx
    change Γ * Y = Y * Γ at hy
    change Γ * (X + Y) = (X + Y) * Γ
    calc
      Γ * (X + Y) = Γ * X + Γ * Y := mul_add Γ X Y
      _ = X * Γ + Y * Γ := by rw [hx, hy]
      _ = (X + Y) * Γ := (add_mul X Y Γ).symm
  · change Γ * X + X * Γ = 0 at hx
    change Γ * Y + Y * Γ = 0 at hy
    change Γ * (X + Y) + (X + Y) * Γ = 0
    calc
      Γ * (X + Y) + (X + Y) * Γ = Γ * X + Γ * Y + (X * Γ + Y * Γ) := by rw [mul_add, add_mul]
      _ = (Γ * X + X * Γ) + (Γ * Y + Y * Γ) := by rw [add_add_add_comm]
      _ = 0 + 0 := by rw [hx, hy]
      _ = 0 := add_zero 0

lemma hasGrading_mul_central {Γ X c : A} {b : Bool} [Central c] (hx : hasGrading Γ X b) :
    hasGrading Γ (c * X) b := by
  have hc : c * Γ = Γ * c := Central.commutes Γ
  cases b
  · change Γ * X = X * Γ at hx
    change Γ * (c * X) = (c * X) * Γ
    calc
      Γ * (c * X) = (Γ * c) * X := by simp only [mul_assoc]
      _ = (c * Γ) * X := by rw [hc]
      _ = c * (Γ * X) := by simp only [mul_assoc]
      _ = c * (X * Γ) := by rw [hx]
      _ = (c * X) * Γ := by simp only [mul_assoc]
  · change Γ * X + X * Γ = 0 at hx
    change Γ * (c * X) + (c * X) * Γ = 0
    calc
      Γ * (c * X) + (c * X) * Γ = (Γ * c) * X + c * (X * Γ) := by simp only [mul_assoc]
      _ = (c * Γ) * X + c * (X * Γ) := by rw [hc]
      _ = c * (Γ * X) + c * (X * Γ) := by simp only [mul_assoc]
      _ = c * (Γ * X + X * Γ) := (mul_add c (Γ * X) (X * Γ)).symm
      _ = c * 0 := by rw [hx]
      _ = 0 := mul_zero c

lemma hasGrading_neg {Γ X : A} {b : Bool} (hx : hasGrading Γ X b) :
    hasGrading Γ (-X) b := by
  cases b
  · change Γ * X = X * Γ at hx
    change Γ * (-X) = (-X) * Γ
    calc
      Γ * (-X) = - (Γ * X) := mul_neg Γ X
      _ = - (X * Γ) := by rw [hx]
      _ = (-X) * Γ := (neg_mul X Γ).symm
  · change Γ * X + X * Γ = 0 at hx
    change Γ * (-X) + (-X) * Γ = 0
    calc
      Γ * (-X) + (-X) * Γ = - (Γ * X) + - (X * Γ) := by rw [mul_neg, neg_mul]
      _ = - (Γ * X + X * Γ) := (neg_add (Γ * X) (X * Γ)).symm
      _ = - 0 := by rw [hx]
      _ = 0 := neg_zero

lemma hasGrading_sub {Γ X Y : A} {b : Bool} (hx : hasGrading Γ X b) (hy : hasGrading Γ Y b) :
    hasGrading Γ (X - Y) b := by
  rw [sub_eq_add_neg]
  exact hasGrading_add hx (hasGrading_neg hy)

lemma hasGrading_anticomm_of_odd {Γ X Y : A}
    (hx : hasGrading Γ X true) (hy : hasGrading Γ Y true) :
    hasGrading Γ (X * Y + Y * X) false := by
  change Γ * X + X * Γ = 0 at hx
  change Γ * Y + Y * Γ = 0 at hy
  have hx' : Γ * X = -(X * Γ) := by
    calc
      Γ * X = (Γ * X + X * Γ) - X * Γ := by noncomm_ring
      _ = 0 - X * Γ := by rw [hx]
      _ = -(X * Γ) := by rw [zero_sub]
  have hy' : Γ * Y = -(Y * Γ) := by
    calc
      Γ * Y = (Γ * Y + Y * Γ) - Y * Γ := by noncomm_ring
      _ = 0 - Y * Γ := by rw [hy]
      _ = -(Y * Γ) := by rw [zero_sub]
  change Γ * (X * Y + Y * X) = (X * Y + Y * X) * Γ
  calc
    Γ * (X * Y + Y * X) = (Γ * X) * Y + (Γ * Y) * X := by
      simp only [mul_add, mul_assoc]
    _ = (-X * Γ) * Y + (-Y * Γ) * X := by
      rw [hx', hy']
      simp only [neg_mul]
    _ = - (X * (Γ * Y)) + - (Y * (Γ * X)) := by
      simp only [neg_mul, mul_assoc]
    _ = - (X * (-(Y * Γ))) + - (Y * (-(X * Γ))) := by
      rw [hy', hx']
    _ = X * (Y * Γ) + Y * (X * Γ) := by simp
    _ = (X * Y + Y * X) * Γ := by
      noncomm_ring

lemma hasGrading_anticomm_of_same_degree {Γ X Y : A} {b : Bool}
    (hx : hasGrading Γ X b) (hy : hasGrading Γ Y b) :
    hasGrading Γ (X * Y + Y * X) false := by
  cases b
  · change Γ * X = X * Γ at hx
    change Γ * Y = Y * Γ at hy
    change Γ * (X * Y + Y * X) = (X * Y + Y * X) * Γ
    calc
      Γ * (X * Y + Y * X) = (Γ * X) * Y + (Γ * Y) * X := by
        simp only [mul_add, mul_assoc]
      _ = (X * Γ) * Y + (Y * Γ) * X := by rw [hx, hy]
      _ = X * (Γ * Y) + Y * (Γ * X) := by simp only [mul_assoc]
      _ = X * (Y * Γ) + Y * (X * Γ) := by rw [hy, hx]
      _ = (X * Y + Y * X) * Γ := by noncomm_ring
  · exact hasGrading_anticomm_of_odd hx hy

lemma hasGrading_commutator_even_odd {Γ X Y : A}
    (hx : hasGrading Γ X false) (hy : hasGrading Γ Y true) :
    hasGrading Γ (X * Y - Y * X) true := by
  change Γ * X = X * Γ at hx
  change Γ * Y + Y * Γ = 0 at hy
  have hy' : Γ * Y = -(Y * Γ) := by
    calc
      Γ * Y = (Γ * Y + Y * Γ) - Y * Γ := by noncomm_ring
      _ = 0 - Y * Γ := by rw [hy]
      _ = -(Y * Γ) := by rw [zero_sub]
  change Γ * (X * Y - Y * X) + (X * Y - Y * X) * Γ = 0
  calc
    Γ * (X * Y - Y * X) + (X * Y - Y * X) * Γ =
        (Γ * X) * Y - (Γ * Y) * X + (X * Y - Y * X) * Γ := by
      simp only [mul_sub, mul_assoc]
    _ = (X * Γ) * Y - (-(Y * Γ)) * X + (X * Y - Y * X) * Γ := by
      rw [hx, hy']
    _ = X * (Γ * Y) + Y * (Γ * X) + (X * Y - Y * X) * Γ := by
      noncomm_ring
    _ = X * (-(Y * Γ)) + Y * (X * Γ) + (X * Y - Y * X) * Γ := by
      rw [hy', hx]
    _ = 0 := by
      noncomm_ring

theorem anticommutator_of_fully_odd_is_fully_even
    {X Y : A}
    (hX : isHomogeneous Γ_R Γ_χ Γ_N X true true true)
    (hY : isHomogeneous Γ_R Γ_χ Γ_N Y true true true) :
    isFullyEven Γ_R Γ_χ Γ_N (X * Y + Y * X) := by
  unfold isFullyEven
  rcases hX with ⟨hXR, hXχ, hXN⟩
  rcases hY with ⟨hYR, hYχ, hYN⟩
  exact ⟨hasGrading_anticomm_of_odd hXR hYR,
    hasGrading_anticomm_of_odd hXχ hYχ,
    hasGrading_anticomm_of_odd hXN hYN⟩

theorem anticommutator_of_same_homogeneous_is_fully_even
    {X Y : A} {b_R b_χ b_N : Bool}
    (hX : isHomogeneous Γ_R Γ_χ Γ_N X b_R b_χ b_N)
    (hY : isHomogeneous Γ_R Γ_χ Γ_N Y b_R b_χ b_N) :
    isFullyEven Γ_R Γ_χ Γ_N (X * Y + Y * X) := by
  unfold isFullyEven
  rcases hX with ⟨hXR, hXχ, hXN⟩
  rcases hY with ⟨hYR, hYχ, hYN⟩
  exact ⟨hasGrading_anticomm_of_same_degree hXR hYR,
    hasGrading_anticomm_of_same_degree hXχ hYχ,
    hasGrading_anticomm_of_same_degree hXN hYN⟩

theorem commutator_of_fully_even_odd_is_fully_odd
    {X Y : A}
    (hX : isFullyEven Γ_R Γ_χ Γ_N X)
    (hY : isFullyOdd Γ_R Γ_χ Γ_N Y) :
    isFullyOdd Γ_R Γ_χ Γ_N (X * Y - Y * X) := by
  unfold isFullyOdd isFullyEven isHomogeneous at *
  rcases hX with ⟨hXR, hXχ, hXN⟩
  rcases hY with ⟨hYR, hYχ, hYN⟩
  exact ⟨hasGrading_commutator_even_odd hXR hYR,
    hasGrading_commutator_even_odd hXχ hYχ,
    hasGrading_commutator_even_odd hXN hYN⟩

/--
The Grand Canonical Modular Generator K_GC rigorously preserves the ℤ₂³ grading.
-/
theorem grand_canonical_generator_is_fully_even
    (hH : isWedgeHamiltonianLike Γ_R Γ_χ Γ_N H_R)
    (hN : isTotalNumberLike Γ_R Γ_χ Γ_N N_op)
    (hQ : isChiralChargeLike Γ_R Γ_χ Γ_N Q_χ) :
    isFullyEven Γ_R Γ_χ Γ_N (β_U * (H_R - μ * N_op - μ_χ * Q_χ)) := by
  unfold isFullyEven isWedgeHamiltonianLike isTotalNumberLike isChiralChargeLike isHomogeneous at *
  rcases hH with ⟨hH_R, hH_χ, hH_N⟩
  rcases hN with ⟨hN_R, hN_χ, hN_N⟩
  rcases hQ with ⟨hQ_R, hQ_χ, hQ_N⟩
  refine ⟨?_, ?_, ?_⟩
  · apply hasGrading_mul_central
    apply hasGrading_sub
    · apply hasGrading_sub
      · exact hH_R
      · exact hasGrading_mul_central hN_R
    · exact hasGrading_mul_central hQ_R
  · apply hasGrading_mul_central
    apply hasGrading_sub
    · apply hasGrading_sub
      · exact hH_χ
      · exact hasGrading_mul_central hN_χ
    · exact hasGrading_mul_central hQ_χ
  · apply hasGrading_mul_central
    apply hasGrading_sub
    · apply hasGrading_sub
      · exact hH_N
      · exact hasGrading_mul_central hN_N
    · exact hasGrading_mul_central hQ_N

end ModularZ2CubeGrading
