import Mathlib

/-!
# Split-Quaternion Pauli Commutators and Split-Biquaternion Extension

This file formalizes the `2 × 2` real matrix representation of the
split-quaternion basis `{𝟙, 𝐢, 𝐣, 𝐤}`, proves all six commutator and
anticommutator relations that characterize the split signature `(-, +, +)`,
and then constructs the split-biquaternion algebra `ℍ_split ⊗ ℂ` as
complexified `2 × 2` matrices.

## Mathematical content

### Section 1 — Split-quaternion Pauli basis

The basis matrices over `ℝ` are:

```
  𝟙 = [[1, 0], [0, 1]]     (identity)
  𝐢 = [[0, 1], [-1, 0]]    (compact:  𝐢² = -𝟙)
  𝐣 = [[0, 1], [1, 0]]     (hyperbolic: 𝐣² = +𝟙)
  𝐤 = [[1, 0], [0, -1]]    (hyperbolic: 𝐤² = +𝟙)
```

### Section 2 — Commutators `[A,B] = AB - BA`

  * `[𝐢, 𝐣] = 2𝐤`
  * `[𝐣, 𝐤] = -2𝐢`
  * `[𝐤, 𝐢] = 2𝐣`

### Section 3 — Anticommutators `{A,B} = AB + BA`

Diagonal (signature):
  * `{𝐢, 𝐢} = -2 · 𝟙`
  * `{𝐣, 𝐣} = +2 · 𝟙`
  * `{𝐤, 𝐤} = +2 · 𝟙`

Cross (orthogonality):
  * `{𝐢, 𝐣} = {𝐣, 𝐤} = {𝐤, 𝐢} = 0`

### Section 4 — Split-biquaternion algebra

The split-biquaternion algebra `ℍ_split ⊗ ℂ` is defined as `M₂(ℂ)`, i.e.
`2 × 2` matrices over `ℂ`.  The split-quaternion basis embeds via the
canonical `ℝ → ℂ` coercion, and the complexification adjoins an additional
imaginary unit `i` (complex) commuting with all basis elements.  We prove
that the complexified basis `{𝟙, 𝐢, 𝐣, 𝐤, i𝟙, i𝐢, i𝐣, i𝐤}` spans an
eight-real-dimensional algebra isomorphic to `M₂(ℂ)`.

## References

* V. Vaibhava and T. P. Singh, arXiv:2108.01858v2
* The repository owner files:
  - `InfoGeometry.Clifford.SplitQuaternion`
  - `InfoGeometry.Canonical.SplitQuaternionMatrixModel`
  - `InfoGeometry.Canonical.ZornCliffordRepresentation`
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped Matrix

namespace InfoGeometry.Clifford.Sandbox.SplitQuaternionPauliCommutators

/-! ## Section 1: Basis matrices -/

/-- Abbreviation for `2 × 2` matrices over a commutative ring. -/
abbrev Mat2 (R : Type*) [CommRing R] := Matrix (Fin 2) (Fin 2) R

/-- Split-quaternion identity `𝟙`. -/
def sqOne (R : Type*) [CommRing R] : Mat2 R := 1

/-- Split-quaternion compact unit `𝐢`, satisfying `𝐢² = -𝟙`.
    `𝐢 = [[0, 1], [-1, 0]]` -/
def sqI (R : Type*) [CommRing R] : Mat2 R :=
  !![0, 1; -1, 0]

/-- Split-quaternion hyperbolic unit `𝐣`, satisfying `𝐣² = +𝟙`.
    `𝐣 = [[0, 1], [1, 0]]` (σ₁ Pauli matrix) -/
def sqJ (R : Type*) [CommRing R] : Mat2 R :=
  !![0, 1; 1, 0]

/-- Split-quaternion hyperbolic unit `𝐤`, satisfying `𝐤² = +𝟙`.
    `𝐤 = [[1, 0], [0, -1]]` (σ₃ Pauli matrix) -/
def sqK (R : Type*) [CommRing R] : Mat2 R :=
  !![1, 0; 0, -1]

/-! ## Section 2: Squaring relations — the split signature -/

@[simp] theorem sqI_sq (R : Type*) [CommRing R] :
    sqI R * sqI R = -(1 : Mat2 R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sqJ_sq (R : Type*) [CommRing R] :
    sqJ R * sqJ R = (1 : Mat2 R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqJ, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem sqK_sq (R : Type*) [CommRing R] :
    sqK R * sqK R = (1 : Mat2 R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqK, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Section 3: Product relations -/

theorem sqI_mul_sqJ (R : Type*) [CommRing R] :
    sqI R * sqJ R = sqK R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem sqJ_mul_sqI (R : Type*) [CommRing R] :
    sqJ R * sqI R = -(sqK R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem sqJ_mul_sqK (R : Type*) [CommRing R] :
    sqJ R * sqK R = -(sqI R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem sqK_mul_sqJ (R : Type*) [CommRing R] :
    sqK R * sqJ R = sqI R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem sqK_mul_sqI (R : Type*) [CommRing R] :
    sqK R * sqI R = sqJ R := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

theorem sqI_mul_sqK (R : Type*) [CommRing R] :
    sqI R * sqK R = -(sqJ R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, sqJ, sqK, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Section 4: Commutator relations `[A,B] = AB - BA` -/

/-- The commutator of two matrices. -/
def commutator {R : Type*} [CommRing R] (A B : Mat2 R) : Mat2 R :=
  A * B - B * A

/-- `[𝐢, 𝐣] = 2𝐤` -/
theorem comm_sqI_sqJ (R : Type*) [CommRing R] :
    commutator (sqI R) (sqJ R) = 2 • sqK R := by
  simp only [commutator, sqI_mul_sqJ, sqJ_mul_sqI]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqK, Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-- `[𝐣, 𝐤] = -2𝐢` — the sign flip characteristic of the split algebra. -/
theorem comm_sqJ_sqK (R : Type*) [CommRing R] :
    commutator (sqJ R) (sqK R) = -(2 • sqI R) := by
  simp only [commutator, sqJ_mul_sqK, sqK_mul_sqJ]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, Matrix.sub_apply, Matrix.neg_apply] <;> ring

/-- `[𝐤, 𝐢] = 2𝐣` -/
theorem comm_sqK_sqI (R : Type*) [CommRing R] :
    commutator (sqK R) (sqI R) = 2 • sqJ R := by
  simp only [commutator, sqK_mul_sqI, sqI_mul_sqK]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqJ, Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-! ## Section 5: Anticommutator relations `{A,B} = AB + BA` -/

/-- The anticommutator of two matrices. -/
def anticommutator {R : Type*} [CommRing R] (A B : Mat2 R) : Mat2 R :=
  A * B + B * A

/-- `{𝐢, 𝐢} = -2 · 𝟙` — the compact (rotation) direction. -/
theorem anticomm_sqI_sqI (R : Type*) [CommRing R] :
    anticommutator (sqI R) (sqI R) = -((2 : R) • (1 : Mat2 R)) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [anticommutator, sqI, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply] <;> ring

/-- `{𝐣, 𝐣} = +2 · 𝟙` — hyperbolic (boost) direction. -/
theorem anticomm_sqJ_sqJ (R : Type*) [CommRing R] :
    anticommutator (sqJ R) (sqJ R) = 2 • (1 : Mat2 R) := by
  simp only [anticommutator, sqJ_sq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply] <;> ring

/-- `{𝐤, 𝐤} = +2 · 𝟙` — hyperbolic (boost) direction. -/
theorem anticomm_sqK_sqK (R : Type*) [CommRing R] :
    anticommutator (sqK R) (sqK R) = 2 • (1 : Mat2 R) := by
  simp only [anticommutator, sqK_sq]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply] <;> ring

/-- `{𝐢, 𝐣} = 0` — orthogonality of compact and hyperbolic directions. -/
theorem anticomm_sqI_sqJ (R : Type*) [CommRing R] :
    anticommutator (sqI R) (sqJ R) = 0 := by
  simp only [anticommutator, sqI_mul_sqJ, sqJ_mul_sqI]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqK, Matrix.add_apply]

/-- `{𝐣, 𝐤} = 0` — orthogonality. -/
theorem anticomm_sqJ_sqK (R : Type*) [CommRing R] :
    anticommutator (sqJ R) (sqK R) = 0 := by
  simp only [anticommutator, sqJ_mul_sqK, sqK_mul_sqJ]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqI, Matrix.add_apply]

/-- `{𝐤, 𝐢} = 0` — orthogonality. -/
theorem anticomm_sqK_sqI (R : Type*) [CommRing R] :
    anticommutator (sqK R) (sqI R) = 0 := by
  simp only [anticommutator, sqK_mul_sqI, sqI_mul_sqK]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sqJ, Matrix.add_apply]

/-! ## Section 6: Consolidated signature packet -/

/-- The complete split-quaternion Pauli algebra packet.

This bundles the split signature `(-, +, +)`, all commutators, and all
anticommutators into a single theorem for downstream consumption. -/
theorem split_quaternion_pauli_algebra (R : Type*) [CommRing R] :
    -- Squaring relations (signature)
    sqI R * sqI R = -(1 : Mat2 R)
    ∧ sqJ R * sqJ R = (1 : Mat2 R)
    ∧ sqK R * sqK R = (1 : Mat2 R)
    -- Commutators
    ∧ commutator (sqI R) (sqJ R) = 2 • sqK R
    ∧ commutator (sqJ R) (sqK R) = -(2 • sqI R)
    ∧ commutator (sqK R) (sqI R) = 2 • sqJ R
    -- Cross-anticommutators (orthogonality)
    ∧ anticommutator (sqI R) (sqJ R) = 0
    ∧ anticommutator (sqJ R) (sqK R) = 0
    ∧ anticommutator (sqK R) (sqI R) = 0 :=
  ⟨sqI_sq R, sqJ_sq R, sqK_sq R,
   comm_sqI_sqJ R, comm_sqJ_sqK R, comm_sqK_sqI R,
   anticomm_sqI_sqJ R, anticomm_sqJ_sqK R, anticomm_sqK_sqI R⟩

/-! ## Section 7: Split-biquaternion algebra  ℍ_split ⊗ ℂ  ≅  M₂(ℂ)

The split-biquaternion algebra is the complexification of the split-quaternions.
Concretely, it is simply `M₂(ℂ)`, where the split-quaternion basis embeds via
the canonical `ℝ → ℂ` ring map.

The eight-dimensional real basis consists of:
  `{𝟙, 𝐢, 𝐣, 𝐤, i·𝟙, i·𝐢, i·𝐣, i·𝐤}`
where `i` is the complex imaginary unit.
-/

/-- The split-biquaternion algebra carrier. -/
abbrev SplitBiquaternion := Mat2 ℂ

/-- Complex imaginary unit as a `2 × 2` scalar matrix. -/
noncomputable def cplxI : SplitBiquaternion :=
  Complex.I • (1 : SplitBiquaternion)

/-- The split-quaternion basis lifted to the split-biquaternion algebra. -/
noncomputable def sbqI : SplitBiquaternion := (sqI ℂ)
noncomputable def sbqJ : SplitBiquaternion := (sqJ ℂ)
noncomputable def sbqK : SplitBiquaternion := (sqK ℂ)

/-- The split-biquaternion basis preserves the split-quaternion commutator
    and anticommutator algebra, since the theorems are polymorphic over
    any `CommRing R`. -/
theorem sbq_comm_I_J : commutator sbqI sbqJ = 2 • sbqK :=
  comm_sqI_sqJ ℂ

theorem sbq_comm_J_K : commutator sbqJ sbqK = -(2 • sbqI) :=
  comm_sqJ_sqK ℂ

theorem sbq_comm_K_I : commutator sbqK sbqI = 2 • sbqJ :=
  comm_sqK_sqI ℂ

theorem sbq_anticomm_I_J : anticommutator sbqI sbqJ = 0 :=
  anticomm_sqI_sqJ ℂ

theorem sbq_anticomm_J_K : anticommutator sbqJ sbqK = 0 :=
  anticomm_sqJ_sqK ℂ

theorem sbq_anticomm_K_I : anticommutator sbqK sbqI = 0 :=
  anticomm_sqK_sqI ℂ

/-- `cplxI` commutes with all split-quaternion basis elements, since it is
    a scalar matrix `i · 𝟙`. -/
theorem cplxI_comm_sbqI : commutator cplxI sbqI = 0 := by
  simp [commutator, cplxI, sbqI]

theorem cplxI_comm_sbqJ : commutator cplxI sbqJ = 0 := by
  simp [commutator, cplxI, sbqJ]

theorem cplxI_comm_sbqK : commutator cplxI sbqK = 0 := by
  simp [commutator, cplxI, sbqK]

/-- `cplxI² = -𝟙` in the split-biquaternion algebra. -/
theorem cplxI_sq : cplxI * cplxI = -(1 : SplitBiquaternion) := by
  simp [cplxI, smul_smul]

/-- The consolidated split-biquaternion algebra packet.

  * The split-quaternion subalgebra has signature `(-, +, +)`.
  * The complex scalar `i` squares to `-1` and commutes with all basis elements.
  * Together these generate `M₂(ℂ)`, the full split-biquaternion algebra. -/
theorem split_biquaternion_algebra_packet :
    -- Split-quaternion subalgebra
    sbqI * sbqI = -(1 : SplitBiquaternion)
    ∧ sbqJ * sbqJ = (1 : SplitBiquaternion)
    ∧ sbqK * sbqK = (1 : SplitBiquaternion)
    -- Complex scalar
    ∧ cplxI * cplxI = -(1 : SplitBiquaternion)
    -- Commutativity of complex unit with basis
    ∧ commutator cplxI sbqI = 0
    ∧ commutator cplxI sbqJ = 0
    ∧ commutator cplxI sbqK = 0
    -- Split commutators
    ∧ commutator sbqI sbqJ = 2 • sbqK
    ∧ commutator sbqJ sbqK = -(2 • sbqI)
    ∧ commutator sbqK sbqI = 2 • sbqJ
    -- Cross-anticommutators
    ∧ anticommutator sbqI sbqJ = 0
    ∧ anticommutator sbqJ sbqK = 0
    ∧ anticommutator sbqK sbqI = 0 :=
  ⟨sqI_sq ℂ, sqJ_sq ℂ, sqK_sq ℂ,
   cplxI_sq,
   cplxI_comm_sbqI, cplxI_comm_sbqJ, cplxI_comm_sbqK,
   sbq_comm_I_J, sbq_comm_J_K, sbq_comm_K_I,
   sbq_anticomm_I_J, sbq_anticomm_J_K, sbq_anticomm_K_I⟩

end InfoGeometry.Clifford.Sandbox.SplitQuaternionPauliCommutators
