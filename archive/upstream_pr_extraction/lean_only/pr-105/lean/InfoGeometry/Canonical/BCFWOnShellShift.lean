import Mathlib

namespace InfoGeometry.Canonical

open Complex

/-- An abstract vector space over ℂ with a symmetric bilinear form (dot product).
    This serves as the ambient momentum space. -/
class MomentumSpace (V : Type*) [AddCommGroup V] [Module ℂ V] where
  inner : V → V → ℂ
  inner_symm : ∀ x y, inner x y = inner y x
  inner_add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  inner_smul_left : ∀ (c : ℂ) x y, inner (c • x) y = c * inner x y

export MomentumSpace (inner inner_symm inner_add_left inner_smul_left)

section BCFW

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [MomentumSpace V]

/-- The core data of a BCFW shift for two massless momenta p_i, p_j and a shift vector q.
    The shift vector q must be null and orthogonal to both p_i and p_j. -/
structure BCFWShiftData (V : Type*) [AddCommGroup V] [Module ℂ V] [MomentumSpace V] where
  pi : V
  pj : V
  q : V
  pi_null : inner pi pi = 0
  pj_null : inner pj pj = 0
  q_null : inner q q = 0
  pi_ortho_q : inner pi q = 0
  pj_ortho_q : inner pj q = 0

variable (data : BCFWShiftData V) (z : ℂ)

/-- The shifted momentum p_i(z) = p_i + z q -/
def shiftedPi : V :=
  data.pi + z • data.q

/-- The shifted momentum p_j(z) = p_j - z q -/
def shiftedPj : V :=
  data.pj - z • data.q

@[simp]
lemma inner_add_right (x y z : V) : inner x (y + z) = inner x y + inner x z := by
  rw [inner_symm, inner_add_left, inner_symm, inner_symm z x]

@[simp]
lemma inner_smul_right (c : ℂ) (x y : V) : inner x (c • y) = c * inner x y := by
  rw [inner_symm, inner_smul_left, inner_symm]

@[simp]
lemma inner_sub_left (x y z : V) : inner (x - y) z = inner x z - inner y z := by
  have h : x - y = x + (-1 : ℂ) • y := by
    rw [neg_one_smul]
    exact sub_eq_add_neg x y
  rw [h, inner_add_left, inner_smul_left]
  ring

@[simp]
lemma inner_sub_right (x y z : V) : inner x (y - z) = inner x y - inner x z := by
  rw [inner_symm, inner_sub_left, inner_symm, inner_symm z x]

attribute [simp] inner_add_left inner_smul_left

/-- Proof that the shifted p_i(z) remains on-shell (massless). -/
theorem bcfw_shift_left_null : inner (shiftedPi data z) (shiftedPi data z) = 0 := by
  dsimp [shiftedPi]
  simp [data.pi_null, data.pi_ortho_q, data.q_null, inner_symm data.q data.pi]

/-- Proof that the shifted p_j(z) remains on-shell (massless). -/
theorem bcfw_shift_right_null : inner (shiftedPj data z) (shiftedPj data z) = 0 := by
  dsimp [shiftedPj]
  simp [data.pj_null, data.pj_ortho_q, data.q_null, inner_symm data.q data.pj]

/-- Total momentum conservation is preserved under the shift: p_i(z) + p_j(z) = p_i + p_j. -/
theorem bcfw_shift_momentum_conservation :
    shiftedPi data z + shiftedPj data z = data.pi + data.pj := by
  dsimp [shiftedPi, shiftedPj]
  abel

/-- For an intermediate channel momentum P_I containing p_i but not p_j, 
    the shifted channel momentum is P_I(z) = P_I + z q. -/
def shiftedChannel (PI : V) (z : ℂ) : V :=
  PI + z • data.q

/-- The invariant mass squared of the shifted channel is P_I(z)² = P_I² + z * (2 P_I · q). -/
lemma shiftedChannel_sq (PI : V) (z : ℂ) :
    inner (shiftedChannel data PI z) (shiftedChannel data PI z) =
    inner PI PI + z * (2 * inner PI data.q) := by
  dsimp [shiftedChannel]
  simp [data.q_null, inner_symm data.q PI]
  ring

/--
The shifted intermediate channel becomes on-shell at the affine root
`-inner PI PI / (2 * inner PI q)` when the slope is nonzero.
-/
theorem bcfw_channel_goes_onShell
    (PI : V) (hslope : 2 * inner PI data.q ≠ 0) :
    inner (shiftedChannel data PI (-inner PI PI / (2 * inner PI data.q)))
          (shiftedChannel data PI (-inner PI PI / (2 * inner PI data.q))) = 0 := by
  rw [shiftedChannel_sq]
  have hmul :
      (-inner PI PI / (2 * inner PI data.q)) * (2 * inner PI data.q) = -inner PI PI := by
    exact div_mul_cancel₀ (-inner PI PI) hslope
  rw [hmul]
  ring

end BCFW

end InfoGeometry.Canonical
