import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.OperatorAlgebra.CliffordCAR

/-!
# Native quadratic CAR closure

The quadratic creation sector is closed under the ordinary commutator.  The
proof lifts the generator identity through both real spans; it does not
replace the CAR operators by scalar coordinates.
-/

namespace InfoGeometry.OperatorAlgebra.CliffordCAR

theorem wittPosTwo_commutator_mem_wittPosTwo
    (n : ℕ) {X Y : Clnn n}
    (hX : X ∈ wittPosTwo n) (hY : Y ∈ wittPosTwo n) :
    X * Y - Y * X ∈ wittPosTwo n := by
  have hsmul_right : ∀ (c : ℝ) (x y : Clnn n),
      x * (c • y) - (c • y) * x = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      x * ((algebraMap ℝ (Clnn n)) c * y) -
          ((algebraMap ℝ (Clnn n)) c * y) * x =
          ((algebraMap ℝ (Clnn n)) c * x) * y -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [← mul_assoc x (algebraMap ℝ (Clnn n) c) y,
                ← Algebra.commutes c x]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y) -
            (algebraMap ℝ (Clnn n)) c * (y * x) := by
              rw [mul_assoc, mul_assoc]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  have hsmul_left : ∀ (c : ℝ) (x y : Clnn n),
      (c • x) * y - y * (c • x) = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      ((algebraMap ℝ (Clnn n)) c * x) * y -
          y * ((algebraMap ℝ (Clnn n)) c * x) =
          (algebraMap ℝ (Clnn n)) c * (x * y) -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [← mul_assoc y (algebraMap ℝ (Clnn n) c) x,
                ← Algebra.commutes c y]
              noncomm_ring
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  refine Submodule.span_induction
    (p := fun X _ => X * Y - Y * X ∈ wittPosTwo n)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨⟨i, j⟩, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => (cre n i * cre n j) * Y -
        Y * (cre n i * cre n j) ∈ wittPosTwo n)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨⟨k, l⟩, rfl⟩
      rw [cre_cre_commutator_cre_cre]
      exact (wittPosTwo n).zero_mem
    · simpa using (Submodule.zero_mem (wittPosTwo n))
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [show (cre n i * cre n j) * (y₁ + y₂) -
          (y₁ + y₂) * (cre n i * cre n j) =
          ((cre n i * cre n j) * y₁ - y₁ * (cre n i * cre n j)) +
            ((cre n i * cre n j) * y₂ - y₂ * (cre n i * cre n j)) by
              noncomm_ring]
      exact (wittPosTwo n).add_mem hy₁ hy₂
    · intro c y _ hy
      rw [hsmul_right c (cre n i * cre n j) y]
      exact (wittPosTwo n).smul_mem c hy
  · simpa using (Submodule.zero_mem (wittPosTwo n))
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [show (x₁ + x₂) * Y - Y * (x₁ + x₂) =
        (x₁ * Y - Y * x₁) + (x₂ * Y - Y * x₂) by noncomm_ring]
    exact (wittPosTwo n).add_mem hx₁ hx₂
  · intro c x _ hx
    rw [hsmul_left c x Y]
    exact (wittPosTwo n).smul_mem c hx

theorem wittNegTwo_commutator_mem_wittNegTwo
    (n : ℕ) {X Y : Clnn n}
    (hX : X ∈ wittNegTwo n) (hY : Y ∈ wittNegTwo n) :
    X * Y - Y * X ∈ wittNegTwo n := by
  have hsmul_right : ∀ (c : ℝ) (x y : Clnn n),
      x * (c • y) - (c • y) * x = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      x * ((algebraMap ℝ (Clnn n)) c * y) -
          ((algebraMap ℝ (Clnn n)) c * y) * x =
          ((algebraMap ℝ (Clnn n)) c * x) * y -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [← mul_assoc x (algebraMap ℝ (Clnn n) c) y,
                ← Algebra.commutes c x]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y) -
            (algebraMap ℝ (Clnn n)) c * (y * x) := by
              rw [mul_assoc, mul_assoc]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  have hsmul_left : ∀ (c : ℝ) (x y : Clnn n),
      (c • x) * y - y * (c • x) = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      ((algebraMap ℝ (Clnn n)) c * x) * y -
          y * ((algebraMap ℝ (Clnn n)) c * x) =
          (algebraMap ℝ (Clnn n)) c * (x * y) -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [← mul_assoc y (algebraMap ℝ (Clnn n) c) x,
                ← Algebra.commutes c y]
              noncomm_ring
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  refine Submodule.span_induction
    (p := fun X _ => X * Y - Y * X ∈ wittNegTwo n)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨⟨i, j⟩, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => (ann n i * ann n j) * Y -
        Y * (ann n i * ann n j) ∈ wittNegTwo n)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨⟨k, l⟩, rfl⟩
      rw [ann_ann_commutator_ann_ann]
      exact (wittNegTwo n).zero_mem
    · simpa using (Submodule.zero_mem (wittNegTwo n))
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [show (ann n i * ann n j) * (y₁ + y₂) -
          (y₁ + y₂) * (ann n i * ann n j) =
          ((ann n i * ann n j) * y₁ - y₁ * (ann n i * ann n j)) +
            ((ann n i * ann n j) * y₂ - y₂ * (ann n i * ann n j)) by
              noncomm_ring]
      exact (wittNegTwo n).add_mem hy₁ hy₂
    · intro c y _ hy
      rw [hsmul_right c (ann n i * ann n j) y]
      exact (wittNegTwo n).smul_mem c hy
  · simpa using (Submodule.zero_mem (wittNegTwo n))
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [show (x₁ + x₂) * Y - Y * (x₁ + x₂) =
        (x₁ * Y - Y * x₁) + (x₂ * Y - Y * x₂) by noncomm_ring]
    exact (wittNegTwo n).add_mem hx₁ hx₂
  · intro c x _ hx
    rw [hsmul_left c x Y]
    exact (wittNegTwo n).smul_mem c hx

/-- The positive quadratic creation sector as a native Lie subalgebra. -/
def wittPosTwoLieSubalgebra (n : ℕ) : LieSubalgebra ℝ (Clnn n) where
  carrier := wittPosTwo n
  zero_mem' := (wittPosTwo n).zero_mem
  add_mem' := fun {x y} hx hy => (wittPosTwo n).add_mem hx hy
  smul_mem' := fun c x hx => (wittPosTwo n).smul_mem c hx
  lie_mem' := by
    intro x y hx hy
    change x * y - y * x ∈ wittPosTwo n
    exact wittPosTwo_commutator_mem_wittPosTwo n hx hy

/-- The negative quadratic annihilation sector as a native Lie subalgebra. -/
def wittNegTwoLieSubalgebra (n : ℕ) : LieSubalgebra ℝ (Clnn n) where
  carrier := wittNegTwo n
  zero_mem' := (wittNegTwo n).zero_mem
  add_mem' := fun {x y} hx hy => (wittNegTwo n).add_mem hx hy
  smul_mem' := fun c x hx => (wittNegTwo n).smul_mem c hx
  lie_mem' := by
    intro x y hx hy
    change x * y - y * x ∈ wittNegTwo n
    exact wittNegTwo_commutator_mem_wittNegTwo n hx hy

theorem wittZero_commutator_mem_wittZero
    (n : ℕ) {X Y : Clnn n}
    (hX : X ∈ wittZero n) (hY : Y ∈ wittZero n) :
    X * Y - Y * X ∈ wittZero n := by
  have hsmul_right : ∀ (c : ℝ) (x y : Clnn n),
      x * (c • y) - (c • y) * x = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      x * ((algebraMap ℝ (Clnn n)) c * y) -
          ((algebraMap ℝ (Clnn n)) c * y) * x =
          ((algebraMap ℝ (Clnn n)) c * x) * y -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [← mul_assoc x (algebraMap ℝ (Clnn n) c) y,
                ← Algebra.commutes c x]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y) -
            (algebraMap ℝ (Clnn n)) c * (y * x) := by
              rw [mul_assoc, mul_assoc]
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  have hsmul_left : ∀ (c : ℝ) (x y : Clnn n),
      (c • x) * y - y * (c • x) = c • (x * y - y * x) := by
    intro c x y
    simp only [Algebra.smul_def]
    calc
      ((algebraMap ℝ (Clnn n)) c * x) * y -
          y * ((algebraMap ℝ (Clnn n)) c * x) =
          (algebraMap ℝ (Clnn n)) c * (x * y) -
            ((algebraMap ℝ (Clnn n)) c * y) * x := by
              rw [Algebra.commutes c y]
              noncomm_ring
      _ = (algebraMap ℝ (Clnn n)) c * (x * y - y * x) := by
            noncomm_ring
  refine Submodule.span_induction
    (p := fun X _ => X * Y - Y * X ∈ wittZero n)
    ?_ ?_ ?_ ?_ hX
  · intro x hx
    rcases hx with ⟨⟨i, j⟩, rfl⟩
    refine Submodule.span_induction
      (p := fun Y _ => mixedGenerator n i j * Y -
        Y * mixedGenerator n i j ∈ wittZero n)
      ?_ ?_ ?_ ?_ hY
    · intro y hy
      rcases hy with ⟨⟨k, l⟩, rfl⟩
      rw [mixedGenerator_commutator_mixedGenerator]
      by_cases hjk : j = k
      · by_cases hil : i = l
        · simp only [if_pos hjk, if_pos hil]
          exact (wittZero n).sub_mem
            (Submodule.subset_span (Set.mem_range_self (i, l)))
            (Submodule.subset_span (Set.mem_range_self (k, j)))
        · simp only [if_pos hjk, if_neg hil]
          exact (wittZero n).sub_mem
            (Submodule.subset_span (Set.mem_range_self (i, l)))
            (Submodule.zero_mem _)
      · by_cases hil : i = l
        · simp only [if_neg hjk, if_pos hil]
          exact (wittZero n).sub_mem
            (Submodule.zero_mem _)
            (Submodule.subset_span (Set.mem_range_self (k, j)))
        · simp only [if_neg hjk, if_neg hil]
          simpa using (Submodule.zero_mem (wittZero n))
    · simpa using (Submodule.zero_mem (wittZero n))
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [show mixedGenerator n i j * (y₁ + y₂) -
          (y₁ + y₂) * mixedGenerator n i j =
          (mixedGenerator n i j * y₁ - y₁ * mixedGenerator n i j) +
            (mixedGenerator n i j * y₂ - y₂ * mixedGenerator n i j) by
              noncomm_ring]
      exact (wittZero n).add_mem hy₁ hy₂
    · intro c y _ hy
      rw [hsmul_right c (mixedGenerator n i j) y]
      exact (wittZero n).smul_mem c hy
  · simpa using (Submodule.zero_mem (wittZero n))
  · intro x₁ x₂ _ _ hx₁ hx₂
    rw [show (x₁ + x₂) * Y - Y * (x₁ + x₂) =
        (x₁ * Y - Y * x₁) + (x₂ * Y - Y * x₂) by noncomm_ring]
    exact (wittZero n).add_mem hx₁ hx₂
  · intro c x _ hx
    rw [hsmul_left c x Y]
    exact (wittZero n).smul_mem c hx

/-- The degree-zero mixed quadratic sector as a native Lie subalgebra. -/
def wittZeroLieSubalgebra (n : ℕ) : LieSubalgebra ℝ (Clnn n) where
  carrier := wittZero n
  zero_mem' := (wittZero n).zero_mem
  add_mem' := fun {x y} hx hy => (wittZero n).add_mem hx hy
  smul_mem' := fun c x hx => (wittZero n).smul_mem c hx
  lie_mem' := by
    intro x y hx hy
    change x * y - y * x ∈ wittZero n
    exact wittZero_commutator_mem_wittZero n hx hy

/-
theorem wittPosTwo_generator_commutator_mem_wittZero
    (n : ℕ) (i j k l : Fin n) :
    (cre n i * cre n j) * (ann n k * ann n l) -
        (ann n k * ann n l) * (cre n i * cre n j) ∈ wittZero n := by
  have hca (a b : Fin n) :
      ann n a * cre n b =
        (if a = b then (1 : Clnn n) else 0) - cre n b * ann n a := by
    have h := car_identity n a b
    by_cases hab : a = b
    · subst b
      simpa only [if_pos rfl] using (eq_sub_of_add_eq h)
    · simp only [if_neg hab] at h ⊢
      simpa [sub_eq_add_neg] using (eq_neg_of_add_eq_zero_left h)
  have hm (a b : Fin n) :
      cre n a * ann n b -
          (if a = b then (1 / 2 : ℝ) • (1 : Clnn n) else 0) ∈ wittZero n :=
    Submodule.subset_span (Set.mem_range_self (a, b))
  have hmem {p : Prop} [Decidable p] (z : Clnn n) (hz : z ∈ wittZero n) :
      (if p then z else 0) ∈ wittZero n := by
    by_cases hp : p <;> simp [hp, hz]
  have hhalf :
      (2 : Clnn n) • (algebraMap ℝ (Clnn n) (1 / 2 : ℝ)) = 1 := by
    change algebraMap ℝ (Clnn n) 2 * algebraMap ℝ (Clnn n) (1 / 2 : ℝ) = 1
    rw [← map_mul]
    norm_num
  rw [cre_cre_commutator_ann_ann]
  have hformula :
      ((if j = k then cre n i else 0) - if i = k then cre n j else 0) * ann n l +
          ann n k * ((if j = l then cre n i else 0) - if i = l then cre n j else 0) =
        (if j = k then mixedGenerator n i l else 0) -
          (if i = k then mixedGenerator n j l else 0) -
          (if j = l then mixedGenerator n i k else 0) +
          (if i = l then mixedGenerator n j k else 0) := by
    by_cases hjk : j = k <;> by_cases hik : i = k <;>
      by_cases hjl : j = l <;> by_cases hil : i = l
    all_goals simp_all [mixedGenerator, hca, eq_comm, Algebra.smul_def]
    all_goals rw [hhalf]
    all_goals noncomm_ring
  rw [hformula]
  exact (wittZero n).add_mem
    ((wittZero n).sub_mem
      ((wittZero n).sub_mem
        (hmem _ (hm i l))
        (hmem _ (hm j l)))
      (hmem _ (hm i k)))
    (hmem _ (hm j k))
-/

end InfoGeometry.OperatorAlgebra.CliffordCAR
