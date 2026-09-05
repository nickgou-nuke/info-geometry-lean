import InfoGeometry.Projective.GibbsRayGeometry

/-!
# Exact frame and readout corrections for the supplied attention brainstorm

Finite product projections, tensor-factor occupation projections, and
nonorthogonal key readouts have different laws. These counterexamples audit
those laws; they do not replace the operator-Zorn field carrier.
-/

noncomputable section
namespace InfoGeometry.LLM.AttentionFrameCorrections

open InfoGeometry.Projective.ExpectationRatioMetric
open scoped BigOperators Matrix

section Heads
variable {H V : Type*} [Fintype H] [DecidableEq H] [AddCommGroup V] [Module ℝ V]

/-- A chosen direct-product partition, not a central Clifford idempotent. -/
def headProjection (h : H) : (H → V) →ₗ[ℝ] (H → V) where
  toFun x i := if i = h then x i else 0
  map_add' x y := by funext i; by_cases hi : i = h <;> simp [hi]
  map_smul' c x := by funext i; by_cases hi : i = h <;> simp [hi]

theorem headProjection_comp (h k : H) :
    (headProjection (V := V) h).comp (headProjection k) =
      if h = k then headProjection h else 0 := by
  by_cases hk : h = k
  · subst k
    ext x i
    by_cases hi : i = h <;> simp [headProjection, hi]
  · ext x i
    by_cases hi : i = h <;> by_cases hik : i = k <;>
      simp_all [headProjection]

theorem sum_headProjection : (∑ h : H, headProjection (V := V) h) = LinearMap.id := by
  ext x i
  simp [headProjection, eq_comm]

end Heads

abbrev Bits := Fin 2 → Bool
abbrev BitSpace := Bits → ℝ

def occupationProjection (k : Fin 2) : Module.End ℝ BitSpace where
  toFun x b := if b k = false then x b else 0
  map_add' x y := by funext b; by_cases h : b k = false <;> simp [h]
  map_smul' c x := by funext b; by_cases h : b k = false <;> simp [h]

def bitParity (k : Fin 2) : Module.End ℝ BitSpace where
  toFun x b := if b k = false then x b else -x b
  map_add' x y := by funext b; by_cases h : b k = false <;> simp [h]
  map_smul' c x := by funext b; by_cases h : b k = false <;> simp [h]

/-- Connect the occupation projector explicitly to the source's (1+sigma_z)/2. -/
theorem occupationProjection_eq (k : Fin 2) :
    occupationProjection k = (1/2 : ℝ) • (1 + bitParity k) := by
  ext x b
  by_cases h : b k = false <;> simp [occupationProjection, bitParity, h] <;> ring

/-- Disjoint tensor factors do not imply orthogonal occupation projectors. -/
theorem distinct_head_occupation_projections_overlap :
    occupationProjection 0 * occupationProjection 1 ≠ 0 := by
  intro h
  have hv := congrArg (fun T : Module.End ℝ BitSpace => T (fun _ => 1) (fun _ => false)) h
  change (1 : ℝ) = 0 at hv
  norm_num at hv

theorem occupation_projections_not_complete :
    occupationProjection 0 + occupationProjection 1 ≠ (1 : Module.End ℝ BitSpace) := by
  intro h
  have hv := congrArg (fun T : Module.End ℝ BitSpace => T (fun _ => 1) (fun _ => false)) h
  change (1 : ℝ) + 1 = 1 at hv
  norm_num at hv

def repoint : Module.End ℝ BitSpace where
  toFun x _ := x (fun _ => true)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem occupation_projection_not_central :
    occupationProjection 0 * repoint ≠ repoint * occupationProjection 0 := by
  intro h
  have hv := congrArg (fun T : Module.End ℝ BitSpace => T (fun _ => 1) (fun _ => false)) h
  change (1 : ℝ) = 0 at hv
  norm_num at hv

/-- A Fourier character in a logarithmic ratio; not a Radon transform. -/
def dilationCharacter (ν r : ℝ) : ℂ :=
  Complex.exp (((ν * Real.log r : ℝ) : ℂ) * Complex.I)

theorem dilationCharacter_mul (ν r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    dilationCharacter ν (r*s) = dilationCharacter ν r * dilationCharacter ν s := by
  unfold dilationCharacter
  rw [Real.log_mul hr.ne' hs.ne']
  have h : (((ν * (Real.log r + Real.log s) : ℝ) : ℂ) * Complex.I) =
      ((ν * Real.log r : ℝ) : ℂ) * Complex.I +
      ((ν * Real.log s : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_add]

theorem dilationCharacter_norm (ν r : ℝ) : ‖dilationCharacter ν r‖ = 1 := by
  simp [dilationCharacter, Complex.norm_exp]

theorem ratioCharacter_cocycle {ι : Type*} (q : Ray ι) (ν : ℝ) (i j k : ι) :
    dilationCharacter ν (ratio q i j) * dilationCharacter ν (ratio q j k) =
      dilationCharacter ν (ratio q i k) := by
  rw [← dilationCharacter_mul ν _ _ (ratio_pos q i j) (ratio_pos q j k), ratio_cocycle]

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def key : Fin 3 → Fin 2 → ℝ
  | 0 => ![1,0]
  | 1 => ![0,1]
  | 2 => ![3/5,4/5]

/-- Three normalized, overcomplete keys in a two-dimensional coefficient space. -/
theorem key_normalized (k : Fin 3) : ∑ i, (key k i)^2 = 1 := by
  fin_cases k <;> norm_num [key, Fin.sum_univ_two]

theorem keys_not_orthogonal : ∑ i, key 0 i * key 2 i = (3/5 : ℝ) := by
  norm_num [key, Fin.sum_univ_two]

def keyReadout (M : Mat2) (k : Fin 3) : ℝ := ∑ i, ∑ j, key k i * M i j * key k j

theorem maximallyMixed_key_readout (k : Fin 3) :
    keyReadout ((1/2 : ℝ) • (1 : Mat2)) k = (1/2 : ℝ) := by
  fin_cases k <;> norm_num [keyReadout, key, Fin.sum_univ_two]

/-- Born readouts on nonorthogonal normalized keys need not form a probability row. -/
theorem nonorthogonal_key_readouts_not_normalized :
    (∑ k : Fin 3, keyReadout ((1/2 : ℝ) • (1 : Mat2)) k) ≠ 1 := by
  simp_rw [maximallyMixed_key_readout]
  norm_num

theorem uniform_softmax_three (k : Fin 3) :
    InfoGeometry.Routing.FiniteSoftmax.weight (fun _ : Fin 3 => 0) 1 k = (1/3 : ℝ) := by
  norm_num [InfoGeometry.Routing.FiniteSoftmax.weight,
    InfoGeometry.Routing.FiniteSoftmax.partitionZ]

/-- Even at zero logits the proposed nonorthogonal-key density identification fails. -/
theorem key_readout_not_softmax (k : Fin 3) :
    keyReadout ((1/2 : ℝ) • (1 : Mat2)) k ≠
      InfoGeometry.Routing.FiniteSoftmax.weight (fun _ : Fin 3 => 0) 1 k := by
  rw [maximallyMixed_key_readout, uniform_softmax_three]
  norm_num

end InfoGeometry.LLM.AttentionFrameCorrections
