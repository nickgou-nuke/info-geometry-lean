import proofs.RealPin55TwistedAction
import proofs.RealOrthogonalGroup55

/-! # Orthogonality of the full real Pin twisted action -/

noncomputable section
namespace RealPin55OrthogonalAction

open Clifford55
open RealPin55Core
open RealPin55TwistedAction

theorem normalized_unit_inverse_pos {u : Cl55ˣ} {a : V55}
    (hua : (u : Cl55) = ι55 a) (ha : Q55 a = 1) :
    ((u⁻¹ : Cl55ˣ) : Cl55) = ι55 a := by
  have hu2 : u * u = 1 := by
    apply Units.ext
    change (u : Cl55) * (u : Cl55) = 1
    rw [hua, CliffordAlgebra.ι_sq_scalar, ha]
    simp
  have hinv : u⁻¹ = u := by
    calc
      u⁻¹ = u⁻¹ * 1 := by simp
      _ = u⁻¹ * (u * u) := by rw [hu2]
      _ = u := by simp
  rw [hinv, hua]

theorem normalized_unit_inverse_neg {u : Cl55ˣ} {a : V55}
    (hua : (u : Cl55) = ι55 a) (ha : Q55 a = -1) :
    ((u⁻¹ : Cl55ˣ) : Cl55) = -ι55 a := by
  have hu_neg_u : u * (-u) = 1 := by
    apply Units.ext
    change (u : Cl55) * (-(u : Cl55)) = 1
    rw [hua, mul_neg, CliffordAlgebra.ι_sq_scalar, ha]
    simp
  have hinv : u⁻¹ = -u := by
    calc
      u⁻¹ = u⁻¹ * 1 := by simp
      _ = u⁻¹ * (u * (-u)) := by rw [hu_neg_u]
      _ = -u := by simp
  rw [hinv]
  simp [hua]

def reflectedVector (a v : V55) (q : ℝ) : V55 :=
  v - (q * QuadraticMap.polar Q55 a v) • a

def anisotropicReflection (a v : V55) : V55 :=
  v - ((Q55 a)⁻¹ * QuadraticMap.polar Q55 a v) • a

theorem anisotropicReflection_preserves_Q {a : V55} (ha : Q55 a ≠ 0)
    (v : V55) : Q55 (anisotropicReflection a v) = Q55 v := by
  rw [anisotropicReflection, sub_eq_add_neg,
    QuadraticMap.map_add (Q55 : V55 → ℝ)]
  rw [← neg_smul]
  rw [QuadraticMap.map_smul,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_comm Q55 v a]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem polar_anisotropicReflection {a : V55} (ha : Q55 a ≠ 0)
    (v : V55) :
    QuadraticMap.polar Q55 a (anisotropicReflection a v) =
      -QuadraticMap.polar Q55 a v := by
  rw [anisotropicReflection, QuadraticMap.polar_sub_right,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_self]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem anisotropicReflection_involutive {a : V55} (ha : Q55 a ≠ 0) :
    Function.Involutive (anisotropicReflection a) := by
  intro v
  rw [anisotropicReflection, polar_anisotropicReflection ha]
  unfold anisotropicReflection
  module

@[simp] theorem anisotropicReflection_self {a : V55} (ha : Q55 a ≠ 0) :
    anisotropicReflection a a = -a := by
  have hs : (Q55 a)⁻¹ * (2 • Q55 a) = 2 := by
    rw [nsmul_eq_mul]
    field_simp
    norm_num
  rw [anisotropicReflection, QuadraticMap.polar_self]
  rw [hs]
  module

theorem reflectedVector_eq_anisotropicReflection {a : V55}
    (ha : Q55 a = 1 ∨ Q55 a = -1) (v : V55) :
    reflectedVector a v (Q55 a) = anisotropicReflection a v := by
  rcases ha with h | h <;>
    simp [reflectedVector, anisotropicReflection, h]

theorem anisotropicReflection_smul {a : V55} (ha : Q55 a ≠ 0)
    {c : ℝ} (hc : c ≠ 0) (v : V55) :
    anisotropicReflection (c • a) v = anisotropicReflection a v := by
  unfold anisotropicReflection
  rw [QuadraticMap.map_smul, QuadraticMap.polar_smul_left]
  simp only [smul_smul]
  congr 1
  apply congrArg (fun r : ℝ ↦ r • a)
  simp only [smul_eq_mul]
  field_simp

theorem exists_normalized_smul (a : V55) (ha : Q55 a ≠ 0) :
    ∃ c : ℝ, c ≠ 0 ∧ (Q55 (c • a) = 1 ∨ Q55 (c • a) = -1) := by
  let s : ℝ := Real.sqrt |Q55 a|
  have habs : 0 < |Q55 a| := abs_pos.mpr ha
  have hspos : 0 < s := Real.sqrt_pos.2 habs
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsquare : s ^ 2 = |Q55 a| := by
    exact Real.sq_sqrt (le_of_lt habs)
  refine ⟨s⁻¹, inv_ne_zero hsne, ?_⟩
  rw [QuadraticMap.map_smul]
  simp only [smul_eq_mul]
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · right
    rw [abs_of_neg hneg] at hsquare
    field_simp
    nlinarith [hsquare]
  · left
    rw [abs_of_pos hpos] at hsquare
    field_simp
    nlinarith [hsquare]

theorem generator_twisted_reflection {u : Cl55ˣ} {a : V55}
    (hu : u ∈ normalizedVectorUnits) (hua : (u : Cl55) = ι55 a)
    (ha : Q55 a = 1 ∨ Q55 a = -1) (v : V55) :
    twistedVector (⟨u, Subgroup.subset_closure hu⟩ : FullPin55) v =
      reflectedVector a v (Q55 a) := by
  apply iota55_injective
  rw [iota_twistedVector]
  have hcliff := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q55) a v
  have hsq : ι55 a * ι55 a = algebraMap ℝ Cl55 (Q55 a) :=
    CliffordAlgebra.ι_sq_scalar Q55 a
  let b : ℝ := QuadraticMap.polar Q55 a v
  have hav : ι55 a * ι55 v = algebraMap ℝ Cl55 b - ι55 v * ι55 a := by
    dsimp [b]
    exact eq_sub_of_add_eq hcliff
  rcases ha with hpos | hneg
  · rw [hua, CliffordAlgebra.involute_ι,
      normalized_unit_inverse_pos hua hpos]
    simp only [reflectedVector, hpos, one_mul, map_sub, map_smul]
    change -ι55 a * ι55 v * ι55 a =
      ι55 v - algebraMap ℝ Cl55 b * ι55 a
    calc
      -ι55 a * ι55 v * ι55 a = -(ι55 a * ι55 v) * ι55 a := by
        noncomm_ring
      _ = -(algebraMap ℝ Cl55 b) * ι55 a +
          ι55 v * (ι55 a * ι55 a) := by rw [hav]; noncomm_ring
      _ = ι55 v - algebraMap ℝ Cl55 b * ι55 a := by
        rw [hsq, hpos]
        simp
        noncomm_ring
  · rw [hua, CliffordAlgebra.involute_ι,
      normalized_unit_inverse_neg hua hneg]
    simp only [reflectedVector, hneg, neg_mul, map_sub, map_smul]
    simp only [one_mul, neg_smul, sub_neg_eq_add]
    change -(ι55 a * ι55 v * -ι55 a) =
      ι55 v + algebraMap ℝ Cl55 b * ι55 a
    calc
      -(ι55 a * ι55 v * -ι55 a) = (ι55 a * ι55 v) * ι55 a := by
        noncomm_ring
      _ = algebraMap ℝ Cl55 b * ι55 a -
          ι55 v * (ι55 a * ι55 a) := by rw [hav]; noncomm_ring
      _ = ι55 v + algebraMap ℝ Cl55 b * ι55 a := by
        rw [hsq, hneg]
        simp
        abel

theorem reflectedVector_preserves_Q {a : V55}
    (ha : Q55 a = 1 ∨ Q55 a = -1) (v : V55) :
    Q55 (reflectedVector a v (Q55 a)) = Q55 v := by
  rcases ha with hpos | hneg
  · simp only [reflectedVector, hpos, one_mul, sub_eq_add_neg,
      ← neg_smul]
    rw [QuadraticMap.map_add (Q55 : V55 → ℝ), QuadraticMap.map_smul,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_comm Q55 v a,
      hpos]
    simp only [smul_eq_mul]
    ring
  · simp only [reflectedVector, hneg, neg_mul, neg_smul, sub_neg_eq_add]
    rw [QuadraticMap.map_add (Q55 : V55 → ℝ), QuadraticMap.map_smul,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_comm Q55 v a,
      hneg]
    simp only [smul_eq_mul]
    ring

theorem normalized_generator_preserves_Q {u : Cl55ˣ}
    (hu : u ∈ normalizedVectorUnits) (v : V55) :
    Q55 (twistedVector
      (⟨u, Subgroup.subset_closure hu⟩ : FullPin55) v) = Q55 v := by
  rcases hu with ⟨a, ha, hua⟩
  rw [generator_twisted_reflection
    (hu := ⟨a, ha, hua⟩) (hua := hua) (ha := ha)]
  exact reflectedVector_preserves_Q ha v

/-- Every normalized non-isotropic vector reflection has a constructive lift
to the signature-correct real Pin group. -/
theorem normalized_reflection_has_fullPin_lift (a : V55)
    (ha : Q55 a = 1 ∨ Q55 a = -1) :
    ∃ g : FullPin55, ∀ v : V55,
      twistedVector g v = reflectedVector a v (Q55 a) := by
  have hunit : IsUnit (Q55 a) := by
    rcases ha with h | h
    · rw [h]
      exact isUnit_one
    · rw [h]
      exact isUnit_iff_ne_zero.mpr (by norm_num)
  let u : Cl55ˣ := vectorUnit a hunit
  have hu : u ∈ normalizedVectorUnits :=
    ⟨a, ha, coe_vectorUnit a hunit⟩
  refine ⟨⟨u, Subgroup.subset_closure hu⟩, ?_⟩
  intro v
  exact generator_twisted_reflection hu (coe_vectorUnit a hunit) ha v

theorem normalized_anisotropicReflection_has_fullPin_lift (a : V55)
    (ha : Q55 a = 1 ∨ Q55 a = -1) :
    ∃ g : FullPin55, ∀ v : V55,
      twistedVector g v = anisotropicReflection a v := by
  rcases normalized_reflection_has_fullPin_lift a ha with ⟨g, hg⟩
  exact ⟨g, fun v ↦ (hg v).trans (reflectedVector_eq_anisotropicReflection ha v)⟩

/-- Every anisotropic split reflection is represented by an explicitly
normalized Clifford vector in `FullPin55`. -/
theorem anisotropicReflection_has_fullPin_lift (a : V55) (ha : Q55 a ≠ 0) :
    ∃ g : FullPin55, ∀ v : V55,
      twistedVector g v = anisotropicReflection a v := by
  rcases exists_normalized_smul a ha with ⟨c, hc, hnorm⟩
  rcases normalized_anisotropicReflection_has_fullPin_lift (c • a) hnorm with
    ⟨g, hg⟩
  refine ⟨g, fun v ↦ ?_⟩
  rw [hg v, anisotropicReflection_smul ha hc]

theorem normalized_generator_inverse_preserves_Q {u : Cl55ˣ}
    (hu : u ∈ normalizedVectorUnits) (v : V55) :
    Q55 (twistedVector
      (⟨u⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure hu)⟩ : FullPin55) v) =
      Q55 v := by
  let g : FullPin55 := ⟨u, Subgroup.subset_closure hu⟩
  have hpres := normalized_generator_preserves_Q hu (twistedVector g⁻¹ v)
  have hcancel : twistedVector g (twistedVector g⁻¹ v) = v := by
    simpa using (twistedVector_mul g g⁻¹ v).symm
  change Q55 (twistedVector g⁻¹ v) = Q55 v
  calc
    Q55 (twistedVector g⁻¹ v) =
        Q55 (twistedVector g (twistedVector g⁻¹ v)) := hpres.symm
    _ = Q55 v := by rw [hcancel]

/-- The signature-correct full Pin closure acts by isometries of the
split quadratic form, not only on its vector generators. -/
theorem fullPin55_preserves_Q (g : FullPin55) (v : V55) :
    Q55 (twistedVector g v) = Q55 v := by
  let p : ∀ u : Cl55ˣ, u ∈ Subgroup.closure normalizedVectorUnits → Prop :=
    fun u hu ↦ ∀ w : V55,
      Q55 (twistedVector (⟨u, hu⟩ : FullPin55) w) = Q55 w
  have hp : p g.1 g.2 := by
    apply Subgroup.closure_induction'' (p := p)
    · intro u hu w
      exact normalized_generator_preserves_Q hu w
    · intro u hu w
      exact normalized_generator_inverse_preserves_Q hu w
    · intro w
      change Q55 (twistedVector (1 : FullPin55) w) = Q55 w
      simp
    · intro x y hx hy ihx ihy w
      let gx : FullPin55 := ⟨x, hx⟩
      let gy : FullPin55 := ⟨y, hy⟩
      change Q55 (twistedVector (gx * gy) w) = Q55 w
      rw [twistedVector_mul]
      exact (ihx (twistedVector gy w)).trans (ihy w)
  exact hp v

end RealPin55OrthogonalAction
end noncomputable section
