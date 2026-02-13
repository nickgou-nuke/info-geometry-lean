import InfoGeometry.Clifford.Cl11
import Mathlib

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Projectivization dictionary: two nonzero vectors represent the same ray
iff they differ by a nonzero real scalar. -/
def SameRayDoubled (v w : DoubledSpace E) : Prop :=
  ∃ a : ℝ, a ≠ 0 ∧ w = a • v

lemma sameRay_refl {v : DoubledSpace E} : SameRayDoubled v v := by
  refine ⟨1, by norm_num, ?_⟩
  simp

lemma sameRay_symm {v w : DoubledSpace E} :
    SameRayDoubled v w → SameRayDoubled w v := by
  rintro ⟨a, ha, rfl⟩
  refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
  calc
    v = (a⁻¹ * a) • v := by simp [ha]
    _ = a⁻¹ • (a • v) := by simp [smul_smul]

lemma sameRay_trans {u v w : DoubledSpace E} :
    SameRayDoubled u v → SameRayDoubled v w → SameRayDoubled u w := by
  rintro ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
  simp [smul_smul, mul_comm]

/-- Setoid for projectivized doubled states (rays). -/
def sameRaySetoid : Setoid (DoubledSpace E) where
  r := SameRayDoubled
  iseqv := ⟨
    by intro x; exact sameRay_refl (E := E),
    by intro x y hxy; exact sameRay_symm (E := E) hxy,
    by intro x y z hxy hyz; exact sameRay_trans (E := E) hxy hyz
  ⟩

/-- Projective states: quotient of doubled states by nonzero real rescaling. -/
def ProjectiveState : Type _ := Quotient (sameRaySetoid (E := E))

/-- Canonical projection from a doubled state to its projective ray class. -/
def projectivize (v : DoubledSpace E) : ProjectiveState (E := E) :=
  Quotient.mk'' v

end KreinClifford
