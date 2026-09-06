import Mathlib.Tactic

/-!
# Finite three-branch Toeplitz defect identities

The definitions below use a concrete family of three generators and prove its
finite defect annihilation law directly. No representation packet is added.
-/

namespace InfoGeometry.Fractal

variable {A : Type*} [Ring A] [StarRing A]

def toeplitzDefectP0 (S : Fin 3 → A) : A :=
  1 - (S 0 * star (S 0) +
    S 1 * star (S 1) + S 2 * star (S 2))

def toeplitzTilt (c : Fin 3) : Fin 3 :=
  if c = 0 then 1 else if c = 1 then 2 else 0

def toeplitzTiltOperator (S : Fin 3 → A) (c : Fin 3) : A :=
  S (toeplitzTilt c)

@[simp] theorem toeplitzTiltOperator_pow_three (S : Fin 3 → A) :
    toeplitzTiltOperator
        (toeplitzTiltOperator (toeplitzTiltOperator S)) = S := by
  funext c
  fin_cases c <;> rfl

theorem toeplitzTilt_pow_three (c : Fin 3) :
    toeplitzTilt (toeplitzTilt (toeplitzTilt c)) = c := by
  fin_cases c <;> rfl

theorem toeplitzTilt_bijective : Function.Bijective toeplitzTilt := by
  constructor
  · intro a b hab
    calc
      a = toeplitzTilt (toeplitzTilt (toeplitzTilt a)) :=
        (toeplitzTilt_pow_three a).symm
      _ = toeplitzTilt (toeplitzTilt (toeplitzTilt b)) :=
        congrArg (fun c => toeplitzTilt (toeplitzTilt c)) hab
      _ = b := toeplitzTilt_pow_three b
  · intro b
    refine ⟨toeplitzTilt (toeplitzTilt b), ?_⟩
    exact toeplitzTilt_pow_three b

theorem toeplitz_defect_annihilation_0
    (S : Fin 3 → A)
    (isometry : ∀ c, star (S c) * S c = 1)
    (orthogonality : ∀ c d, c ≠ d → star (S c) * S d = 0) :
    star (S 0) * toeplitzDefectP0 S = 0 := by
  dsimp [toeplitzDefectP0]
  rw [mul_sub, mul_one, mul_add, mul_add]
  have h0 : star (S 0) * (S 0 * star (S 0)) = star (S 0) := by
    rw [← mul_assoc, isometry 0, one_mul]
  have h1 : star (S 0) * (S 1 * star (S 1)) = 0 := by
    rw [← mul_assoc, orthogonality 0 1 (by decide), zero_mul]
  have h2 : star (S 0) * (S 2 * star (S 2)) = 0 := by
    rw [← mul_assoc, orthogonality 0 2 (by decide), zero_mul]
  rw [h0, h1, h2]
  simp

theorem toeplitz_defect_annihilation_all
    (S : Fin 3 → A)
    (isometry : ∀ c, star (S c) * S c = 1)
    (orthogonality : ∀ c d, c ≠ d → star (S c) * S d = 0) :
    ∀ c, star (S c) * toeplitzDefectP0 S = 0 := by
  intro c
  dsimp [toeplitzDefectP0]
  rw [mul_sub, mul_one, mul_add, mul_add]
  have hself : star (S c) * (S c * star (S c)) = star (S c) := by
    rw [← mul_assoc, isometry c, one_mul]
  have hcross (d : Fin 3) (hcd : c ≠ d) :
      star (S c) * (S d * star (S d)) = 0 := by
    rw [← mul_assoc, orthogonality c d hcd, zero_mul]
  fin_cases c <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk.injEq, Nat.succ.injEq,
      OfNat.ofNat_eq_ofNat, Nat.reduceAdd, not_false_eq_true] at *
  · change star (S 0) -
      (star (S 0) * (S 0 * star (S 0)) +
        star (S 0) * (S 1 * star (S 1)) +
        star (S 0) * (S 2 * star (S 2))) = 0
    rw [hself, hcross 1 (by decide), hcross 2 (by decide)]
    simp
  · have hself' : star (S 1) * (S 1 * star (S 1)) = star (S 1) := by
      simpa using hself
    have hcross0 : star (S 1) * (S 0 * star (S 0)) = 0 := by
      simpa using hcross 0 (by decide)
    have hcross2 : star (S 1) * (S 2 * star (S 2)) = 0 := by
      simpa using hcross 2 (by decide)
    change star (S 1) -
      (star (S 1) * (S 0 * star (S 0)) +
        star (S 1) * (S 1 * star (S 1)) +
        star (S 1) * (S 2 * star (S 2))) = 0
    rw [hcross0, hself', hcross2]
    simp
  · have hself' : star (S 2) * (S 2 * star (S 2)) = star (S 2) := by
      simpa using hself
    have hcross0 : star (S 2) * (S 0 * star (S 0)) = 0 := by
      simpa using hcross 0 (by decide)
    have hcross1 : star (S 2) * (S 1 * star (S 1)) = 0 := by
      simpa using hcross 1 (by decide)
    change star (S 2) -
      (star (S 2) * (S 0 * star (S 0)) +
        star (S 2) * (S 1 * star (S 1)) +
        star (S 2) * (S 2 * star (S 2))) = 0
    rw [hcross0, hcross1, hself']
    simp

theorem toeplitz_defect_right_annihilation_all
    (S : Fin 3 → A)
    (isometry : ∀ c, star (S c) * S c = 1)
    (orthogonality : ∀ c d, c ≠ d → star (S c) * S d = 0) :
    ∀ c, toeplitzDefectP0 S * S c = 0 := by
  intro c
  dsimp [toeplitzDefectP0]
  rw [sub_mul, one_mul, add_mul, add_mul]
  have hself : (S c * star (S c)) * S c = S c := by
    rw [mul_assoc, isometry c, mul_one]
  have hcross (d : Fin 3) (hcd : c ≠ d) :
      (S d * star (S d)) * S c = 0 := by
    rw [mul_assoc, orthogonality d c (Ne.symm hcd), mul_zero]
  fin_cases c <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk.injEq, Nat.succ.injEq,
      OfNat.ofNat_eq_ofNat, Nat.reduceAdd, not_false_eq_true] at *
  · change S 0 -
      ((S 0 * star (S 0)) * S 0 +
        (S 1 * star (S 1)) * S 0 +
        (S 2 * star (S 2)) * S 0) = 0
    rw [hself, hcross 1 (by decide), hcross 2 (by decide)]
    simp
  · have hself' : (S 1 * star (S 1)) * S 1 = S 1 := by
      simpa using hself
    have hcross0 : (S 0 * star (S 0)) * S 1 = 0 := by
      simpa using hcross 0 (by decide)
    have hcross2 : (S 2 * star (S 2)) * S 1 = 0 := by
      simpa using hcross 2 (by decide)
    change S 1 -
      ((S 0 * star (S 0)) * S 1 +
        (S 1 * star (S 1)) * S 1 +
        (S 2 * star (S 2)) * S 1) = 0
    rw [hcross0, hself', hcross2]
    simp
  · have hself' : (S 2 * star (S 2)) * S 2 = S 2 := by
      simpa using hself
    have hcross0 : (S 0 * star (S 0)) * S 2 = 0 := by
      simpa using hcross 0 (by decide)
    have hcross1 : (S 1 * star (S 1)) * S 2 = 0 := by
      simpa using hcross 1 (by decide)
    change S 2 -
      ((S 0 * star (S 0)) * S 2 +
        (S 1 * star (S 1)) * S 2 +
        (S 2 * star (S 2)) * S 2) = 0
    rw [hcross0, hcross1, hself']
    simp

theorem toeplitz_range_projection_idempotent
    (S : Fin 3 → A)
    (isometry : ∀ c, star (S c) * S c = 1)
    (c : Fin 3) :
    (S c * star (S c)) * (S c * star (S c)) =
      S c * star (S c) := by
  calc
    (S c * star (S c)) * (S c * star (S c)) =
        S c * (star (S c) * S c) * star (S c) := by
      simp only [mul_assoc]
    _ = S c * star (S c) := by rw [isometry c, mul_one]

@[simp] theorem toeplitz_range_projection_star
    (S : Fin 3 → A) (c : Fin 3) :
    star (S c * star (S c)) = S c * star (S c) := by
  simp [star_mul]

theorem toeplitz_range_projection_orthogonal
    (S : Fin 3 → A)
    (orthogonality : ∀ c d, c ≠ d → star (S c) * S d = 0)
    {c d : Fin 3} (hcd : c ≠ d) :
    (S c * star (S c)) * (S d * star (S d)) = 0 := by
  calc
    (S c * star (S c)) * (S d * star (S d)) =
        S c * ((star (S c) * S d) * star (S d)) := by
      noncomm_ring
    _ = 0 := by rw [orthogonality c d hcd, zero_mul, mul_zero]

theorem toeplitz_defect_idempotent
    (S : Fin 3 → A)
    (isometry : ∀ c, star (S c) * S c = 1)
    (orthogonality : ∀ c d, c ≠ d → star (S c) * S d = 0) :
    toeplitzDefectP0 S * toeplitzDefectP0 S = toeplitzDefectP0 S := by
  have h0 := toeplitz_defect_right_annihilation_all S isometry orthogonality 0
  have h1 := toeplitz_defect_right_annihilation_all S isometry orthogonality 1
  have h2 := toeplitz_defect_right_annihilation_all S isometry orthogonality 2
  change toeplitzDefectP0 S *
      (1 - (S 0 * star (S 0) +
        S 1 * star (S 1) + S 2 * star (S 2))) =
    toeplitzDefectP0 S
  rw [mul_sub, mul_one, mul_add, mul_add]
  rw [← mul_assoc, h0, zero_mul]
  rw [← mul_assoc, h1, zero_mul]
  rw [← mul_assoc, h2, zero_mul]
  simp

@[simp] theorem toeplitz_defect_star
    (S : Fin 3 → A) :
    star (toeplitzDefectP0 S) = toeplitzDefectP0 S := by
  simp [toeplitzDefectP0, star_mul]

theorem toeplitz_defect_tilt_invariant (S : Fin 3 → A) :
    toeplitzDefectP0 (toeplitzTiltOperator S) = toeplitzDefectP0 S := by
  unfold toeplitzDefectP0 toeplitzTiltOperator
  change 1 -
      (S 1 * star (S 1) + S 2 * star (S 2) + S 0 * star (S 0)) =
    1 - (S 0 * star (S 0) + S 1 * star (S 1) + S 2 * star (S 2))
  abel

end InfoGeometry.Fractal
