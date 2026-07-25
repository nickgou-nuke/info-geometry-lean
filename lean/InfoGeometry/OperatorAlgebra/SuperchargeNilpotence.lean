import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.CliffordCAR

/-!
# Supercharge Nilpotence — Q² = 0, D² = H (PROVED)

Uses `ι_sq_scalar` (ι(v)² = Q(v)·1) and `QuadraticMap.map_add`
(standalone theorem, not field notation) plus polar bilinearity
(`QuadraticMap.polar_add_left`, `QuadraticMap.polar_smul_left`).

Key API notes (from mathlib4):
- `QuadraticMap.map_add f x y` — standalone theorem, f:M→N
- `ι_mul_ι_add_swap a b` — Q is implicit, gives polar
- `(Q : QuadraticMap ...).map_smul` — field notation works for map_smul
- `QuadraticMap.polar_add_left Q x x' y` — standalone
- `QuadraticMap.polar_smul_left Q a x y` — standalone
-/

open InfoGeometry.OperatorAlgebra.CliffordCAR
open InfoGeometry.Algebraic.SplitSignature
open CliffordAlgebra

noncomputable section

namespace InfoGeometry.OperatorAlgebra.SuperchargeNilpotence

def s (m : ℕ) (r : ℝ) : Clnn m := algebraMap ℝ (Clnn m) r

def Q (n : ℕ) (w : Fin n → ℝ) : Clnn n := ∑ i : Fin n, s n (w i) * ann n i
def Qdag (n : ℕ) (w : Fin n → ℝ) : Clnn n := ∑ i : Fin n, s n (w i) * cre n i
def D (n : ℕ) (w : Fin n → ℝ) : Clnn n := Q n w + Qdag n w
def H (n : ℕ) (w : Fin n → ℝ) : Clnn n := Q n w * Qdag n w + Qdag n w * Q n w

/-! Q = ι(v), Q† = ι(v†) -/

lemma Q_eq_iota (n : ℕ) (w : Fin n → ℝ) :
    Q n w = ι (splitQuadraticForm n) (∑ i : Fin n, w i • aVec n i) := by
  dsimp [Q, ann, s]
  refine calc
    (∑ i : Fin n, (algebraMap ℝ (Clnn n)) (w i) * ι (splitQuadraticForm n) (aVec n i))
        = (∑ i : Fin n, ι (splitQuadraticForm n) (w i • aVec n i)) := by
      refine Finset.sum_congr rfl (λ i _ => ?_)
      simpa [Algebra.smul_def] using
        ((ι (splitQuadraticForm n)).map_smul (w i) (aVec n i)).symm
    _ = ι (splitQuadraticForm n) (∑ i : Fin n, w i • aVec n i) := by
      rw [← map_sum (ι (splitQuadraticForm n))]

lemma Qdag_eq_iota (n : ℕ) (w : Fin n → ℝ) :
    Qdag n w = ι (splitQuadraticForm n) (∑ i : Fin n, w i • aDagVec n i) := by
  dsimp [Qdag, cre, s]
  refine calc
    (∑ i : Fin n, (algebraMap ℝ (Clnn n)) (w i) * ι (splitQuadraticForm n) (aDagVec n i))
        = (∑ i : Fin n, ι (splitQuadraticForm n) (w i • aDagVec n i)) := by
      refine Finset.sum_congr rfl (λ i _ => ?_)
      simpa [Algebra.smul_def] using
        ((ι (splitQuadraticForm n)).map_smul (w i) (aDagVec n i)).symm
    _ = ι (splitQuadraticForm n) (∑ i : Fin n, w i • aDagVec n i) := by
      rw [← map_sum (ι (splitQuadraticForm n))]

/-! Q(v) = 0 for v = Σ w_i·aVec_i -/

lemma QF_zero (n : ℕ) (w : Fin n → ℝ) :
    (splitQuadraticForm n) (∑ i : Fin n, w i • aVec n i) = 0 := by
  have h : ∀ (T : Finset (Fin n)),
      (splitQuadraticForm n) (∑ i ∈ T, w i • aVec n i) = 0 := by
    intro T
    induction' T using Finset.induction_on with k T hk ih
    · simp
    · rw [Finset.sum_insert hk]
      -- Use standalone QuadraticMap.map_add: Q(x+y) = Q(x) + Q(y) + polar(x,y)
      rw [QuadraticMap.map_add (splitQuadraticForm n) _ _]
      rw [ih, add_zero]
      -- Q(w_k·v_k) = w_k²·Q(v_k) = 0
      rw [(splitQuadraticForm n).map_smul (w k) (aVec n k),
        Q_aVec n k, smul_zero]
      -- polar(Σ_T w_i·v_i, w_k·v_k) = 0 by bilinearity + polar_ann_ann
      have h_polar : QuadraticMap.polar (splitQuadraticForm n)
          (∑ i ∈ T, w i • aVec n i) (w k • aVec n k) = 0 := by
        have h_T : ∀ (S : Finset (Fin n)),
            QuadraticMap.polar (splitQuadraticForm n)
              (∑ i ∈ S, w i • aVec n i) (w k • aVec n k) = 0 := by
          intro S
          induction' S using Finset.induction_on with j S hj ihS
          · simp [QuadraticMap.polar_zero_left]
          · rw [Finset.sum_insert hj]
            rw [QuadraticMap.polar_add_left (splitQuadraticForm n) _ _ _]
            rw [QuadraticMap.polar_smul_left (splitQuadraticForm n) (w j) _ _]
            rw [QuadraticMap.polar_smul_right (splitQuadraticForm n) (w k) _ _]
            -- polar(v_j, v_k) = 0 from polar_ann_ann
            rw [polar_ann_ann n j k, smul_zero, smul_zero]
            rw [ihS, add_zero]
        exact h_T T
      -- map_add gives polar(new, sum), but h_polar proves polar(sum, new) = 0
      -- polar is symmetric, so swap
      rw [QuadraticMap.polar_comm (splitQuadraticForm n) _ _, h_polar, add_zero]
  exact h Finset.univ

lemma QF_zero_dag (n : ℕ) (w : Fin n → ℝ) :
    (splitQuadraticForm n) (∑ i : Fin n, w i • aDagVec n i) = 0 := by
  have h : ∀ (T : Finset (Fin n)),
      (splitQuadraticForm n) (∑ i ∈ T, w i • aDagVec n i) = 0 := by
    intro T
    induction' T using Finset.induction_on with k T hk ih
    · simp
    · rw [Finset.sum_insert hk]
      rw [QuadraticMap.map_add (splitQuadraticForm n) _ _]
      rw [ih, add_zero]
      rw [(splitQuadraticForm n).map_smul (w k) (aDagVec n k),
        Q_aDagVec n k, smul_zero]
      have h_polar : QuadraticMap.polar (splitQuadraticForm n)
          (∑ i ∈ T, w i • aDagVec n i) (w k • aDagVec n k) = 0 := by
        have h_T : ∀ (S : Finset (Fin n)),
            QuadraticMap.polar (splitQuadraticForm n)
              (∑ i ∈ S, w i • aDagVec n i) (w k • aDagVec n k) = 0 := by
          intro S
          induction' S using Finset.induction_on with j S hj ihS
          · simp [QuadraticMap.polar_zero_left]
          · rw [Finset.sum_insert hj]
            rw [QuadraticMap.polar_add_left (splitQuadraticForm n) _ _ _]
            rw [QuadraticMap.polar_smul_left (splitQuadraticForm n) (w j) _ _]
            rw [QuadraticMap.polar_smul_right (splitQuadraticForm n) (w k) _ _]
            rw [polar_cre_cre n j k, smul_zero, smul_zero]
            rw [ihS, add_zero]
        exact h_T T
      -- map_add gives polar(new, sum), but h_polar proves polar(sum, new) = 0
      -- polar is symmetric, so swap
      rw [QuadraticMap.polar_comm (splitQuadraticForm n) _ _, h_polar, add_zero]
  exact h Finset.univ

/-! Q² = 0, Q†² = 0 -/

theorem Q_sq_zero (n : ℕ) (w : Fin n → ℝ) : Q n w * Q n w = 0 := by
  rw [Q_eq_iota n w]
  rw [ι_sq_scalar (splitQuadraticForm n) (∑ i : Fin n, w i • aVec n i)]
  rw [QF_zero n w]
  simp

theorem Qdag_sq_zero (n : ℕ) (w : Fin n → ℝ) : Qdag n w * Qdag n w = 0 := by
  rw [Qdag_eq_iota n w]
  rw [ι_sq_scalar (splitQuadraticForm n) (∑ i : Fin n, w i • aDagVec n i)]
  rw [QF_zero_dag n w]
  simp

/-! {Q, Q†} = Σ w_i² -/

theorem anticommutator_eq_sum_squares (n : ℕ) (w : Fin n → ℝ) :
    Q n w * Qdag n w + Qdag n w * Q n w = s n (∑ i : Fin n, w i * w i) := by
  rw [Q_eq_iota n w, Qdag_eq_iota n w]
  -- ι(v)·ι(w) + ι(w)·ι(v) = algebraMap(polar(v,w))
  rw [ι_mul_ι_add_swap (Q := splitQuadraticForm n)
    (a := ∑ i : Fin n, w i • aVec n i) (b := ∑ i : Fin n, w i • aDagVec n i)]
  -- Need: polar(Σ w_i·aVec_i, Σ w_j·aDagVec_j) = Σ w_i²
  have h_polar_val : QuadraticMap.polar (splitQuadraticForm n)
      (∑ i : Fin n, w i • aVec n i) (∑ j : Fin n, w j • aDagVec n j) =
      ∑ i : Fin n, w i * w i := by
    -- Expand first sum (first argument of polar) by induction
    have h : ∀ (T : Finset (Fin n)),
        QuadraticMap.polar (splitQuadraticForm n)
          (∑ i ∈ T, w i • aVec n i) (∑ j : Fin n, w j • aDagVec n j) =
        ∑ i ∈ T, w i * w i := by
      intro T
      induction' T using Finset.induction_on with k T hk ih
      · simp
      · rw [Finset.sum_insert hk]
        rw [QuadraticMap.polar_add_left (splitQuadraticForm n) _ _ _]
        rw [QuadraticMap.polar_smul_left (splitQuadraticForm n) (w k) _ _]
        -- Need: polar(aVec_k, Σ_j w_j·aDagVec_j) = w_k
        have h_pol_k : QuadraticMap.polar (splitQuadraticForm n) (aVec n k)
            (∑ j : Fin n, w j • aDagVec n j) = w k := by
          -- Expand second sum
          have h' : ∀ (S : Finset (Fin n)),
              QuadraticMap.polar (splitQuadraticForm n) (aVec n k)
                (∑ j ∈ S, w j • aDagVec n j) =
              (if k ∈ S then w k else 0) := by
            intro S
            induction' S using Finset.induction_on with j S hj ihS
            · simp
            · rw [Finset.sum_insert hj]
              rw [QuadraticMap.polar_add_right (splitQuadraticForm n) _ _ _]
              rw [QuadraticMap.polar_smul_right (splitQuadraticForm n) (w j) _ _]
              rw [polar_ann_cre n k j]
              by_cases hkj : k = j
              · subst hkj; simp [ihS, hj]
              · -- k ≠ j, so k was not just inserted. k is either in S (from before) or not in S.
                -- We know j ∉ S (hj). So k may or may not be in S.
                -- The if-then-else from polar_ann_cre gave 0 (since k≠j).
                -- Then w_j * 0 = 0, and we keep ihS.
                simp [ihS, hkj]
          rw [h' (Finset.univ : Finset (Fin n))]
          simp [Finset.mem_univ]
        rw [h_pol_k, ih]
        simp [Finset.sum_insert hk]
    -- Apply with T = Finset.univ
    simpa using h Finset.univ
  rw [h_polar_val]
  simp [s, Clnn]

theorem H_eq_sum_squares (n : ℕ) (w : Fin n → ℝ) :
    H n w = s n (∑ i : Fin n, w i * w i) :=
  anticommutator_eq_sum_squares n w

theorem D_sq_eq_H (n : ℕ) (w : Fin n → ℝ) : D n w * D n w = H n w := by
  have hQ := Q_sq_zero n w
  have hQDag := Qdag_sq_zero n w
  dsimp [D, H]
  rw [add_mul, mul_add, mul_add, hQ, hQDag]
  simp

end InfoGeometry.OperatorAlgebra.SuperchargeNilpotence
