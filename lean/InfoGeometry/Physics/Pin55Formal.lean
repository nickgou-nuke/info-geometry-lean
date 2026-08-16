import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

/-!
# Split `(5,5)` Clifford finite relations

Uses mathlib's `CliffordAlgebra` with the split `(5,5)` quadratic form.
It proves exact generator identities such as `(e₀·e₅)² = 1`.

This is not a construction of a topological `Pin(5,5)` quotient, a proof that a
four-element set is literally a V4 subgroup, CCC, conformal inversion, or full
orbit classification.
-/

open CliffordAlgebra
open QuadraticMap

noncomputable section

namespace InfoGeometry.Physics.Pin55Formal

/-! ## 1. Split (5,5) quadratic form via `QuadraticMap.proj` -/

/-- q(v) = Σ_{i<5} v_i² - Σ_{i≥5} v_i². Uses `QuadraticMap.proj i i` for each coordinate. -/
def q55 : QuadraticForm ℚ (Fin 10 → ℚ) :=
  (proj 0 0 + proj 1 1 + proj 2 2 + proj 3 3 + proj 4 4) -
  (proj 5 5 + proj 6 6 + proj 7 7 + proj 8 8 + proj 9 9)

/-- Basis vectors e₀ (norm 1) and e₅ (norm -1). -/
def ε₀ : Fin 10 → ℚ := fun i => if i = 0 then 1 else 0
def ε₅ : Fin 10 → ℚ := fun i => if i = 5 then 1 else 0

@[simp] theorem q55_ε₀ : q55 ε₀ = 1 := by
  simp [q55, ε₀, proj_apply]

@[simp] theorem q55_ε₅ : q55 ε₅ = -1 := by
  simp [q55, ε₅, proj_apply]

theorem ε₀_ε₅_orth : q55.IsOrtho ε₀ ε₅ := by
  simp [q55, QuadraticMap.IsOrtho, ε₀, ε₅, proj_apply]

/-! ## 2. Finite Clifford relations and projective sign shadow -/

def r₀ : CliffordAlgebra q55 := ι q55 ε₀
def r₅ : CliffordAlgebra q55 := ι q55 ε₅

theorem r₀_sq : r₀ * r₀ = 1 := by
  calc r₀ * r₀ = algebraMap ℚ (CliffordAlgebra q55) (q55 ε₀) := ι_sq_scalar _ _
    _ = 1 := by simp

theorem r₅_sq : r₅ * r₅ = -1 := by
  calc r₅ * r₅ = algebraMap ℚ (CliffordAlgebra q55) (q55 ε₅) := ι_sq_scalar _ _
    _ = -1 := by simp

theorem anticomm : r₀ * r₅ = -(r₅ * r₀) :=
  ι_mul_ι_comm_of_isOrtho ε₀_ε₅_orth

/-- Exact Clifford relation `(e₀·e₅)² = 1`. -/
theorem v4_relation : (r₀ * r₅) * (r₀ * r₅) = 1 := by
  have hswap : r₅ * r₀ = -(r₀ * r₅) := by
    calc
      r₅ * r₀ = -(-(r₅ * r₀)) := by simp
      _ = -(r₀ * r₅) := by rw [← anticomm]
  calc
    (r₀ * r₅) * (r₀ * r₅) = r₀ * (r₅ * r₀) * r₅ := by simp [mul_assoc]
    _ = r₀ * (-(r₀ * r₅)) * r₅ := by rw [hswap]
    _ = -(r₀ * r₀ * r₅ * r₅) := by simp [mul_assoc]
    _ = -((r₀ * r₀) * (r₅ * r₅)) := by simp [mul_assoc]
    _ = -((1 : CliffordAlgebra q55) * (-1 : CliffordAlgebra q55)) := by rw [r₀_sq, r₅_sq]
    _ = 1 := by simp

/-- Projective sign equivalence in the Clifford algebra: equality up to central sign. -/
def ProjectiveSignEq (x y : CliffordAlgebra q55) : Prop :=
  x = y ∨ x = -y

/-- Projective sign equivalence is reflexive. -/
theorem projectiveSignEq_refl (x : CliffordAlgebra q55) : ProjectiveSignEq x x := by
  left
  rfl

/-- Projective sign equivalence is symmetric. -/
theorem projectiveSignEq_symm {x y : CliffordAlgebra q55} (h : ProjectiveSignEq x y) :
    ProjectiveSignEq y x := by
  rcases h with h | h
  · left
    simpa [h]
  · right
    simpa [h] using (neg_neg y).symm

/-- Projective sign equivalence is transitive. -/
theorem projectiveSignEq_trans {x y z : CliffordAlgebra q55} :
    ProjectiveSignEq x y → ProjectiveSignEq y z → ProjectiveSignEq x z := by
  intro hxy hyz
  rcases hxy with hxy | hxy
  · cases hyz with
    | inl hyz => left; exact hxy.trans hyz
    | inr hyz => right; exact hxy.trans (by simpa [hyz] )
  · cases hyz with
    | inl hyz => right; exact hxy.trans (by simpa [hyz] )
    | inr hyz =>
        left
        calc
          x = -y := hxy
          _ = -(-z) := by rw [hyz]
          _ = z := by simp

/-- Projective sign is respected by left multiplication by a common factor. -/
theorem projectiveSignEq_mul_left {x y z : CliffordAlgebra q55}
    (h : ProjectiveSignEq x y) : ProjectiveSignEq (z * x) (z * y) := by
  rcases h with h | h
  · left; simpa [h]
  · right; simpa [h, neg_mul]

/-- Projective sign is respected by right multiplication by a common factor. -/
theorem projectiveSignEq_mul_right {x y z : CliffordAlgebra q55}
    (h : ProjectiveSignEq x y) : ProjectiveSignEq (x * z) (y * z) := by
  rcases h with h | h
  · left; simpa [h]
  · right; simpa [h, mul_neg]

/-- Exact involutivity of `r₀`. -/
theorem r₀_projective_involutive : ProjectiveSignEq (r₀ * r₀) 1 := by
  left
  exact r₀_sq

/-- `r₅² = -1`, hence `r₅` is involutive only after quotienting central sign. -/
theorem r₅_projective_involutive : ProjectiveSignEq (r₅ * r₅) 1 := by
  right
  exact r₅_sq

/-- Exact involutivity of the product generator `r₀*r₅`. -/
theorem r₀r₅_projective_involutive : ProjectiveSignEq ((r₀ * r₅) * (r₀ * r₅)) 1 := by
  left
  exact v4_relation

/-- The four displayed Clifford elements used as a finite frame.  This is not
claimed to be a literal subgroup: `r₅² = -1`, so closure holds only after a
separate projective-sign quotient construction. -/
def v4Set : Set (CliffordAlgebra q55) := {1, r₀, r₅, r₀ * r₅}

end InfoGeometry.Physics.Pin55Formal
