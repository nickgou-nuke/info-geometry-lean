import InfoGeometry.Krein.SplitQuadratic
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace SplitQuadraticSheets

open InfoGeometry.Krein
open SplitQuadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- The `+1` eigensheet of the doubled-space fundamental symmetry. -/
def plusSheet : Set H₂ :=
  {u | spectral_epsilon (E := E) u = u}

/-- The `-1` eigensheet of the doubled-space fundamental symmetry. -/
def minusSheet : Set H₂ :=
  {u | spectral_epsilon (E := E) u = -u}

/-- Canonical point on the positive split sheet. -/
noncomputable def plusPoint (x : E) : H₂ :=
  to_doubled x 0

/-- Canonical point on the negative split sheet. -/
noncomputable def minusPoint (ξ : E) : H₂ :=
  to_doubled 0 ξ

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem fst_plusPoint (x : E) :
    WithLp.fst (plusPoint (E := E) x) = x := by
  simp [plusPoint]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem snd_plusPoint (x : E) :
    WithLp.snd (plusPoint (E := E) x) = 0 := by
  simp [plusPoint]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem fst_minusPoint (ξ : E) :
    WithLp.fst (minusPoint (E := E) ξ) = 0 := by
  simp [minusPoint]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] theorem snd_minusPoint (ξ : E) :
    WithLp.snd (minusPoint (E := E) ξ) = ξ := by
  simp [minusPoint]

omit [CompleteSpace E] in
@[simp] theorem plusPoint_mem_plusSheet (x : E) :
    plusPoint (E := E) x ∈ plusSheet (E := E) := by
  change spectral_epsilon (E := E) (plusPoint (E := E) x) = plusPoint (E := E) x
  apply DoubledSpace.ext <;> simp [plusPoint, spectral_epsilon]

omit [CompleteSpace E] in
@[simp] theorem minusPoint_mem_minusSheet (ξ : E) :
    minusPoint (E := E) ξ ∈ minusSheet (E := E) := by
  change spectral_epsilon (E := E) (minusPoint (E := E) ξ) = -(minusPoint (E := E) ξ)
  apply DoubledSpace.ext <;> simp [minusPoint, spectral_epsilon]

omit [CompleteSpace E] in
@[simp] theorem mem_plusSheet_iff_snd_eq_zero (u : H₂) :
    u ∈ plusSheet (E := E) ↔ WithLp.snd u = 0 := by
  constructor
  · intro hu
    have hsnd : -WithLp.snd u = WithLp.snd u := by
      simpa [plusSheet, spectral_epsilon_apply] using congrArg WithLp.snd hu
    have hsnd' : WithLp.snd u = -WithLp.snd u := by
      simpa using congrArg Neg.neg hsnd
    rw [eq_neg_iff_add_eq_zero] at hsnd'
    have htwo : (2 : ℝ) • WithLp.snd u = 0 := by
      simpa [two_smul] using hsnd'
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · intro hsnd
    change spectral_epsilon (E := E) u = u
    apply DoubledSpace.ext <;> simp [spectral_epsilon, hsnd]

omit [CompleteSpace E] in
@[simp] theorem mem_minusSheet_iff_fst_eq_zero (u : H₂) :
    u ∈ minusSheet (E := E) ↔ WithLp.fst u = 0 := by
  constructor
  · intro hu
    have hfst : WithLp.fst u = -WithLp.fst u := by
      simpa [minusSheet, spectral_epsilon_apply] using congrArg WithLp.fst hu
    rw [eq_neg_iff_add_eq_zero] at hfst
    have htwo : (2 : ℝ) • WithLp.fst u = 0 := by
      simpa [two_smul] using hfst
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  · intro hfst
    change spectral_epsilon (E := E) u = -u
    apply DoubledSpace.ext <;> simp [spectral_epsilon, hfst]

omit [CompleteSpace E] in
theorem eq_plusPoint_of_mem_plusSheet {u : H₂} (hu : u ∈ plusSheet (E := E)) :
    u = plusPoint (E := E) (WithLp.fst u) := by
  apply DoubledSpace.ext
  · simp [plusPoint]
  · simp [plusPoint, (mem_plusSheet_iff_snd_eq_zero (E := E) u).mp hu]

omit [CompleteSpace E] in
theorem eq_minusPoint_of_mem_minusSheet {u : H₂} (hu : u ∈ minusSheet (E := E)) :
    u = minusPoint (E := E) (WithLp.snd u) := by
  apply DoubledSpace.ext
  · simp [minusPoint, (mem_minusSheet_iff_fst_eq_zero (E := E) u).mp hu]
  · simp [minusPoint]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem plusPoint_sub (x y : E) :
    plusPoint (E := E) x - plusPoint (E := E) y = plusPoint (E := E) (x - y) := by
  apply DoubledSpace.ext
  · rw [WithLp.sub_fst]
    simp [plusPoint]
  · rw [WithLp.sub_snd]
    simp [plusPoint]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem minusPoint_sub (ξ η : E) :
    minusPoint (E := E) ξ - minusPoint (E := E) η = minusPoint (E := E) (ξ - η) := by
  apply DoubledSpace.ext
  · rw [WithLp.sub_fst]
    simp [minusPoint]
  · rw [WithLp.sub_snd]
    simp [minusPoint]

theorem kreinInner_plusPoint (x y : E) :
    KreinSpace.kreinInner (H := H₂) (plusPoint (E := E) x) (plusPoint (E := E) y)
      = inner ℝ x y := by
  rw [krein_inner_prod_l2 (E := E)]
  simp only [plusPoint, to_doubled, WithLp.ofLp_toLp, inner_zero_right, sub_zero]

theorem kreinInner_minusPoint (ξ η : E) :
    KreinSpace.kreinInner (H := H₂) (minusPoint (E := E) ξ) (minusPoint (E := E) η)
      = -inner ℝ ξ η := by
  rw [krein_inner_prod_l2 (E := E)]
  simp only [minusPoint, to_doubled, WithLp.ofLp_toLp, inner_zero_left, zero_sub]

theorem potential_plusPoint_eq_half_norm_sq (x : E) :
    SplitQuadratic.potential (E := E) (plusPoint (E := E) x)
      = (1 / 2 : ℝ) * inner ℝ x x := by
  rw [SplitQuadratic.potential, kreinInner_plusPoint]

theorem potential_minusPoint_eq_neg_half_norm_sq (ξ : E) :
    SplitQuadratic.potential (E := E) (minusPoint (E := E) ξ)
      = -((1 / 2 : ℝ) * inner ℝ ξ ξ) := by
  rw [SplitQuadratic.potential, kreinInner_minusPoint]
  ring

/-- On the positive split sheet, the signed Krein divergence becomes Euclidean. -/
@[rep_depth krein]
theorem divergence_plusPoint_eq_half_sqdist (x y : E) :
    SplitQuadratic.divergence (E := E) (plusPoint (E := E) x) (plusPoint (E := E) y)
      = (1 / 2 : ℝ) * inner ℝ (x - y) (x - y) := by
  rw [SplitQuadratic.divergence_eq_half_signed_krein_sq, plusPoint_sub, kreinInner_plusPoint]

/-- On the negative split sheet, the signed Krein divergence becomes negative Euclidean distance. -/
theorem divergence_minusPoint_eq_neg_half_sqdist (ξ η : E) :
    SplitQuadratic.divergence (E := E) (minusPoint (E := E) ξ) (minusPoint (E := E) η)
      = -((1 / 2 : ℝ) * inner ℝ (ξ - η) (ξ - η)) := by
  rw [SplitQuadratic.divergence_eq_half_signed_krein_sq, minusPoint_sub, kreinInner_minusPoint]
  ring

/-- Positive split-sheet interaction reproduces the Euclidean decomposition. -/
theorem neg_divergence_plusPoint_eq_dot_minus_half_norms (q k : E) :
    -SplitQuadratic.divergence (E := E) (plusPoint (E := E) q) (plusPoint (E := E) k)
      = inner ℝ q k - (1 / 2 : ℝ) * inner ℝ q q - (1 / 2 : ℝ) * inner ℝ k k := by
  rw [SplitQuadratic.neg_divergence_eq_krein_minus_half_diagonals,
    kreinInner_plusPoint, kreinInner_plusPoint, kreinInner_plusPoint]

/-- Negative split-sheet interaction flips the sign of the bilinear coupling. -/
theorem neg_divergence_minusPoint_eq_neg_dot_plus_half_norms (q k : E) :
    -SplitQuadratic.divergence (E := E) (minusPoint (E := E) q) (minusPoint (E := E) k)
      = -inner ℝ q k + (1 / 2 : ℝ) * inner ℝ q q + (1 / 2 : ℝ) * inner ℝ k k := by
  rw [SplitQuadratic.neg_divergence_eq_krein_minus_half_diagonals,
    kreinInner_minusPoint, kreinInner_minusPoint, kreinInner_minusPoint]
  ring

/-- The split quadratic divergence is nonnegative on the `+1` spectral sheet. -/
theorem divergence_nonneg_of_mem_plusSheet {q k : H₂}
    (hq : q ∈ plusSheet (E := E)) (hk : k ∈ plusSheet (E := E)) :
    0 ≤ SplitQuadratic.divergence (E := E) q k := by
  rw [eq_plusPoint_of_mem_plusSheet (E := E) hq, eq_plusPoint_of_mem_plusSheet (E := E) hk,
    divergence_plusPoint_eq_half_sqdist]
  exact mul_nonneg (by norm_num) real_inner_self_nonneg

/-- The split quadratic divergence is nonpositive on the `-1` spectral sheet. -/
theorem divergence_nonpos_of_mem_minusSheet {q k : H₂}
    (hq : q ∈ minusSheet (E := E)) (hk : k ∈ minusSheet (E := E)) :
    SplitQuadratic.divergence (E := E) q k ≤ 0 := by
  rw [eq_minusPoint_of_mem_minusSheet (E := E) hq, eq_minusPoint_of_mem_minusSheet (E := E) hk,
    divergence_minusPoint_eq_neg_half_sqdist]
  exact neg_nonpos.mpr (mul_nonneg (by norm_num) real_inner_self_nonneg)

end SplitQuadraticSheets
