import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.DiracColimit
import InfoGeometry.External.Auto.KANFormalization

noncomputable section

namespace InfoGeometry.Quantum.PrimonCuntzTower

open Complex
open scoped BigOperators

/-- Finite Hilbert stages: `ℂ^(n+1)` with Euclidean structure. -/
abbrev Stage (n : ℕ) : Type := EuclideanSpace ℂ (Fin (n + 1))

instance (n : ℕ) : NormedAddCommGroup (Stage n) := by infer_instance
instance (n : ℕ) : InnerProductSpace ℂ (Stage n) := by infer_instance
instance (n : ℕ) : CompleteSpace (Stage n) := by infer_instance

/-- One-step embedding: keep old coordinates and append one zero tail coordinate. -/
def embFun (n : ℕ) (f : Stage n) : Stage (n + 1) :=
  WithLp.toLp 2 (fun i : Fin (n + 2) =>
    if h : i.1 ≤ n then f ⟨i.1, by omega⟩ else 0)

/-- Linear finite-stage embedding map. -/
def emb (n : ℕ) : Stage n →ₗ[ℂ] Stage (n + 1) :=
  {
    toFun := embFun n
  , map_add' := by
      intro f g
      apply PiLp.ext
      intro i
      by_cases h : i.1 ≤ n
      · simp [embFun, h]
      · simp [embFun, h]
  , map_smul' := by
      intro c f
      apply PiLp.ext
      intro i
      by_cases h : i.1 ≤ n
      · simp [embFun, h]
      · simp [embFun, h]
  }

/-- Norm preservation for the embedding (isometry in the Euclidean norm). -/
lemma emb_isometry (n : ℕ) (f : Stage n) : ‖embFun n f‖ = ‖f‖ := by
  have hsq : ‖embFun n f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    have hcast : ∀ x : Fin (n + 1), x.1 ≤ n := fun x => Nat.lt_succ_iff.mp x.isLt
    simp [embFun, hcast, pow_two]
  have hf : 0 ≤ ‖embFun n f‖ := norm_nonneg _
  have hg : 0 ≤ ‖f‖ := norm_nonneg _
  nlinarith

/-- Explicit `LinearIsometry` version of the one-step embedding. -/
def embIsometry (n : ℕ) : Stage n →ₗᵢ[ℂ] Stage (n + 1) :=
  LinearIsometry.mk (emb n) (fun f => emb_isometry n f)

/-- Diagonal finite-mode Dirac operator with explicit real spectral weights.
    This is a conservative Cuntz/Clifford-style toy model:
    each coordinate `i` is weighted by the energy `i+1`.
-/
def D_n (n : ℕ) : Stage n →L[ℂ] Stage n :=
  {
    toFun := fun f => WithLp.toLp 2 (fun i : Fin (n + 1) => ((i.1 : ℕ) + 1 : ℂ) * f i)
  , map_add' := by
      intro f g
      apply PiLp.ext
      intro i
      simp [mul_add]
  , map_smul' := by
      intro c f
      apply PiLp.ext
      intro i
      simp [mul_left_comm]
  }

/--
Finite Cuntz creation map `S_i`: insert one scalar into coordinate `i`.

At a finite cutoff this is the coordinate version of a Cuntz isometry lane.
-/
def cuntzS (n : ℕ) (i : Fin (n + 1)) (z : ℂ) : Stage n :=
  WithLp.toLp 2 (fun j : Fin (n + 1) => if j = i then z else 0)

/-- Finite Cuntz adjoint `S_i^*`: read coordinate `i`. -/
def cuntzSStar (n : ℕ) (i : Fin (n + 1)) (f : Stage n) : ℂ :=
  f i

/-- Coordinate projection `S_i S_i^*`. -/
def cuntzRangeProjection (n : ℕ) (i : Fin (n + 1)) (f : Stage n) : Stage n :=
  cuntzS n i (cuntzSStar n i f)

/-- Dirac-Hodge operator written through finite Cuntz range projections. -/
def diracHodgeCuntz (n : ℕ) (f : Stage n) : Stage n :=
  ∑ i : Fin (n + 1), ((i.1 : ℕ) + 1 : ℂ) • cuntzRangeProjection n i f

theorem cuntzRangeProjection_apply (n : ℕ) (i j : Fin (n + 1)) (f : Stage n) :
    cuntzRangeProjection n i f j = if j = i then f i else 0 := by
  simp [cuntzRangeProjection, cuntzS, cuntzSStar]

theorem diracHodgeCuntz_apply (n : ℕ) (f : Stage n) (j : Fin (n + 1)) :
    diracHodgeCuntz n f j = ((j.1 : ℕ) + 1 : ℂ) * f j := by
  classical
  unfold diracHodgeCuntz
  calc
    (∑ i : Fin (n + 1), ((i.1 : ℕ) + 1 : ℂ) • cuntzRangeProjection n i f) j
        = ∑ i : Fin (n + 1),
            ((i.1 : ℕ) + 1 : ℂ) * (if j = i then f i else 0) := by
            simp [cuntzRangeProjection_apply]
    _ = ((j.1 : ℕ) + 1 : ℂ) * f j := by
            rw [Finset.sum_eq_single j]
            · simp
            · intro i _ hij
              have hji : j ≠ i := by exact Ne.symm hij
              simp [hji]
            · intro hj
              simp at hj

/-- The finite Dirac-Hodge operator is exactly `Σ (i+1) S_i S_i^*`. -/
theorem diracHodgeCuntz_eq_D_n (n : ℕ) :
    diracHodgeCuntz n = D_n n := by
  funext f
  apply PiLp.ext
  intro j
  simp [diracHodgeCuntz_apply, D_n]

lemma D_n_selfAdjoint (n : ℕ) : IsSelfAdjoint (D_n n) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp [D_n, PiLp.inner_apply, mul_assoc, mul_left_comm]

/-- Finite-stage compatibility: `D` commutes with the embeddings. -/
lemma D_n_comm (n : ℕ) :
    (D_n (n + 1)).comp (emb n).toContinuousLinearMap =
      (emb n).toContinuousLinearMap.comp (D_n n) := by
  ext f i
  simp [D_n, emb, embFun]

/-!
Algebraic Cuntz/finite-support colimit

The completed Hilbert colimit of the prime-weight Dirac is an unbounded-operator
problem.  The algebraic Cuntz lift below proves the honest finite-support
colimit statement first: every finite stage embeds into a common sequence space,
the embeddings are compatible, and the diagonal Dirac action descends to this
algebraic colimit.
-/

/-- Ambient sequence space for the algebraic Cuntz colimit. -/
abbrev CuntzSequence : Type := ℕ → ℂ

/-- Lift a finite stage vector to the common sequence space by zero extension. -/
def stageToSequence (n : ℕ) (f : Stage n) : CuntzSequence :=
  fun k => if h : k ≤ n then f ⟨k, by omega⟩ else 0

/-- Algebraic diagonal Dirac on the common sequence space. -/
def algebraicDirac (x : CuntzSequence) : CuntzSequence :=
  fun k => ((k : ℕ) + 1 : ℂ) * x k

/-- The algebraic Cuntz/finite-support colimit is the union of finite cylinders. -/
def AlgebraicCuntzColimit : Set CuntzSequence :=
  Set.range (fun p : Sigma Stage => stageToSequence p.1 p.2)

theorem stageToSequence_apply_of_le {n k : ℕ} (f : Stage n) (h : k ≤ n) :
    stageToSequence n f k = f ⟨k, by omega⟩ := by
  simp [stageToSequence, h]

theorem stageToSequence_apply_of_not_le {n k : ℕ} (f : Stage n) (h : ¬ k ≤ n) :
    stageToSequence n f k = 0 := by
  simp [stageToSequence, h]

/-- One-step stage embedding is the same point in the algebraic colimit. -/
theorem stageToSequence_emb (n : ℕ) (f : Stage n) :
    stageToSequence (n + 1) (emb n f) = stageToSequence n f := by
  funext k
  by_cases hk : k ≤ n
  · have hk_succ : k ≤ n + 1 := Nat.le_trans hk (Nat.le_succ n)
    simp [stageToSequence, emb, embFun, hk, hk_succ]
  · have hk_old : stageToSequence n f k = 0 := by
      simp [stageToSequence, hk]
    by_cases hk_succ : k ≤ n + 1
    · have hk_eq : k = n + 1 := by omega
      subst hk_eq
      simp [stageToSequence, emb, embFun, hk]
    · simp [stageToSequence, hk, hk_succ]

/-- The diagonal Dirac lifts exactly to the common algebraic sequence space. -/
theorem stageToSequence_D (n : ℕ) (f : Stage n) :
    stageToSequence n ((D_n n) f) = algebraicDirac (stageToSequence n f) := by
  funext k
  by_cases hk : k ≤ n
  · simp [stageToSequence, algebraicDirac, D_n, hk]
  · simp [stageToSequence, algebraicDirac, hk]

/-- The Cuntz `Σ (i+1)S_iS_i^*` expression lifts to the algebraic colimit Dirac. -/
theorem stageToSequence_diracHodgeCuntz (n : ℕ) (f : Stage n) :
    stageToSequence n (diracHodgeCuntz n f) =
      algebraicDirac (stageToSequence n f) := by
  rw [diracHodgeCuntz_eq_D_n]
  exact stageToSequence_D n f

/-- Every finite stage vector defines an element of the algebraic Cuntz colimit. -/
theorem stageToSequence_mem_colimit (n : ℕ) (f : Stage n) :
    stageToSequence n f ∈ AlgebraicCuntzColimit := by
  exact ⟨⟨n, f⟩, rfl⟩

/--
The lifted diagonal Dirac preserves the algebraic Cuntz colimit.

This is the concrete colimit lift we can prove without invoking a completed
Hilbert direct limit or boundedness of the infinite diagonal operator.
-/
theorem algebraicDirac_preserves_colimit {x : CuntzSequence}
    (hx : x ∈ AlgebraicCuntzColimit) :
    algebraicDirac x ∈ AlgebraicCuntzColimit := by
  rcases hx with ⟨p, rfl⟩
  exact ⟨⟨p.1, (D_n p.1) p.2⟩, by
    exact stageToSequence_D p.1 p.2⟩

/-- The finite compatibility theorem rephrased in the common colimit target. -/
theorem algebraicDirac_emb_compatible (n : ℕ) (f : Stage n) :
    algebraicDirac (stageToSequence (n + 1) (emb n f)) =
      algebraicDirac (stageToSequence n f) := by
  rw [stageToSequence_emb]

/-- The Cuntz-operator Dirac-Hodge expression is compatible with stage embeddings in the colimit. -/
theorem diracHodgeCuntz_emb_compatible (n : ℕ) (f : Stage n) :
    stageToSequence (n + 1) (diracHodgeCuntz (n + 1) (emb n f)) =
      stageToSequence n (diracHodgeCuntz n f) := by
  rw [stageToSequence_diracHodgeCuntz (n + 1) (emb n f)]
  rw [stageToSequence_diracHodgeCuntz n f]
  rw [stageToSequence_emb]

/-- Iterated Cuntz embedding through `k` finite stages. -/
def embIter (n : ℕ) : (k : ℕ) → Stage n → Stage (n + k)
  | 0, f => f
  | k + 1, f => emb (n + k) (embIter n k f)

@[simp] theorem embIter_zero (n : ℕ) (f : Stage n) :
    embIter n 0 f = f := rfl

@[simp] theorem embIter_succ (n k : ℕ) (f : Stage n) :
    embIter n (k + 1) f = emb (n + k) (embIter n k f) := rfl

/--
Inductive colimit lift: any finite number of Cuntz embeddings represents the
same point in the algebraic sequence colimit.
-/
theorem stageToSequence_embIter (n k : ℕ) (f : Stage n) :
    stageToSequence (n + k) (embIter n k f) = stageToSequence n f := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [embIter_succ]
      exact (by
        simpa [Nat.add_assoc] using
          (stageToSequence_emb (n + k) (embIter n k f)).trans ih)

/-- The algebraic Dirac is compatible with every finite iterated Cuntz lift. -/
theorem algebraicDirac_embIter_compatible (n k : ℕ) (f : Stage n) :
    algebraicDirac (stageToSequence (n + k) (embIter n k f)) =
      algebraicDirac (stageToSequence n f) := by
  rw [stageToSequence_embIter]

/--
The Cuntz `Σ(i+1)S_iS_i^*` Dirac-Hodge expression is compatible with every
finite iterated lift into the algebraic colimit.
-/
theorem diracHodgeCuntz_embIter_compatible (n k : ℕ) (f : Stage n) :
    stageToSequence (n + k)
        (diracHodgeCuntz (n + k) (embIter n k f)) =
      stageToSequence n (diracHodgeCuntz n f) := by
  rw [stageToSequence_diracHodgeCuntz (n + k) (embIter n k f)]
  rw [stageToSequence_diracHodgeCuntz n f]
  rw [stageToSequence_embIter]

/-- Scaffold data record (parallel to the existing finite-stage interface). -/
structure PrimonCuntzTowerData where
  Stage : ℕ → Type*
  [hNorm : ∀ n, NormedAddCommGroup (Stage n)]
  [hIP : ∀ n, InnerProductSpace ℂ (Stage n)]
  [hCS : ∀ n, CompleteSpace (Stage n)]
  emb : ∀ n, Stage n →ₗᵢ[ℂ] Stage (n + 1)
  D : ∀ n, Stage n →L[ℂ] Stage n
  hD_selfAdj : ∀ n, IsSelfAdjoint (D n)
  hD_comm : ∀ n, (D (n + 1)).comp (emb n).toContinuousLinearMap =
    (emb n).toContinuousLinearMap.comp (D n)

/-- Concrete finite scaffold package for this step of the tower. -/
def primonCuntzTowerData : PrimonCuntzTowerData :=
  { Stage := Stage
  , emb := embIsometry
  , D := D_n
  , hD_selfAdj := D_n_selfAdjoint
  , hD_comm := D_n_comm }

/-- KAN-modeled finite spectral sector at stage `n`: compact/nilpotent sectors are unit,
    logarithmic sector is diagonal weights `i+1`. -/
def primonCuntzKANFactor (n : ℕ) : InfoGeometry.Quantum.KANFormalization.KANFactor (Fin (n + 1)) :=
  { K := 1
  , A := Matrix.diagonal (fun i : Fin (n + 1) => (i.1 + 1 : ℝ))
  , N := 1 }

/-- Log-determinant bridge for the finite stage A-spectrum (conservative: finite product only). -/
 theorem primonCuntz_tower_kan_log_bridge (n : ℕ) :
    Real.log (Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor n))) =
      ∑ i : Fin (n + 1), Real.log ((i.1 + 1 : ℝ)) := by
  have hK : Matrix.det (primonCuntzKANFactor n).K = 1 := by simp [primonCuntzKANFactor]
  have hN : Matrix.det (primonCuntzKANFactor n).N = 1 := by simp [primonCuntzKANFactor]
  rw [InfoGeometry.Quantum.KANFormalization.KANFactor.det_total]
  rw [hK, hN, one_mul, mul_one]
  have hne : ∀ x ∈ (Finset.univ : Finset (Fin (n + 1))), (x.1 + 1 : ℝ) ≠ 0 := by
    intro x hx
    positivity
  have hdiag : Matrix.det (primonCuntzKANFactor n).A = ∏ i : Fin (n + 1), ((i.1 + 1 : ℝ)) := by
    simp [primonCuntzKANFactor, Matrix.det_diagonal]
  rw [hdiag]
  rw [Real.log_prod hne]

/-- Determinant step recursion across one finite tower extension:
    the extra (n+1)-st mode contributes one extra diagonal weight (n+2). -/
theorem primonCuntz_tower_kan_det_rec (n : ℕ) :
    Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor (n + 1))) =
      Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor n)) * (n + 2 : ℝ) := by
  have hprod : (∏ i : Fin (n + 2), (i.1 + 1 : ℝ)) =
      (∏ i : Fin (n + 1), (i.1 + 1 : ℝ)) * (n + 2 : ℝ) := by
    have hcast : (∏ i : Fin (n + 1), (i.castSucc.1 + 1 : ℝ)) =
        (∏ i : Fin (n + 1), (i.1 + 1 : ℝ)) := by
      simp
    have hlast : (((Fin.last (n + 1)).1 : ℝ) + 1) = (n + 2 : ℝ) := by
      have h : ((Fin.last (n + 1)).1 : ℝ) = (n + 1 : ℝ) := by
        simp [Fin.last]
      rw [h]
      ring
    calc
      (∏ i : Fin (n + 2), (i.1 + 1 : ℝ))
          = (∏ i : Fin (n + 1), (i.castSucc.1 + 1 : ℝ)) * (((Fin.last (n + 1)).1 : ℝ) + 1) := by
              simpa using
                (Fin.prod_univ_castSucc (n := n + 1)
                  (f := fun i : Fin (n + 2) => (i.1 + 1 : ℝ)))
      _ = (∏ i : Fin (n + 1), (i.1 + 1 : ℝ)) * (((Fin.last (n + 1)).1 : ℝ) + 1) := by
              rw [hcast]
      _ = (∏ i : Fin (n + 1), (i.1 + 1 : ℝ)) * (n + 2 : ℝ) := by rw [hlast]
  calc
    Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor (n + 1)))
      = ∏ i : Fin (n + 2), (i.1 + 1 : ℝ) := by
          simp [primonCuntzKANFactor, InfoGeometry.Quantum.KANFormalization.KANFactor.det_total, Matrix.det_diagonal]
    _ = (∏ i : Fin (n + 1), (i.1 + 1 : ℝ)) * (n + 2 : ℝ) := hprod
    _ = Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor n)) * (n + 2 : ℝ) := by
          simp [primonCuntzKANFactor, InfoGeometry.Quantum.KANFormalization.KANFactor.det_total, Matrix.det_diagonal]

/-- Log-recursion across the finite tower: `log det` picks up the new mode weight. -/
theorem primonCuntz_tower_kan_log_rec (n : ℕ) :
    Real.log (Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor (n + 1)))) =
      Real.log (Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor n))) +
      Real.log (n + 2 : ℝ) := by
  rw [primonCuntz_tower_kan_det_rec (n := n)]
  have hdetn : Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor n)) ≠ 0 := by
    have hdet : Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total (primonCuntzKANFactor n)) =
        ∏ i : Fin (n + 1), (i.1 + 1 : ℝ) := by
      simp [primonCuntzKANFactor, InfoGeometry.Quantum.KANFormalization.KANFactor.det_total, Matrix.det_diagonal]
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => by positivity)
  have htwo : (n + 2 : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul hdetn htwo]

/--
Final finite-stage Primon/Cuntz-to-KAN bridge.

This bundles the stage Dirac facts (`D_n` is self-adjoint and commutes with
the embeddings) with the finite KAN determinant/log dictionary.  It is only a
finite-stage statement: no global operator decomposition is assumed here.
-/
theorem primonCuntz_finite_stage_KAN_bridge (n : ℕ) :
    IsSelfAdjoint (D_n n) ∧
      (D_n (n + 1)).comp (emb n).toContinuousLinearMap =
        (emb n).toContinuousLinearMap.comp (D_n n) ∧
      Matrix.det (primonCuntzKANFactor n).K = 1 ∧
      Matrix.det (primonCuntzKANFactor n).N = 1 ∧
      Real.log (Matrix.det (InfoGeometry.Quantum.KANFormalization.KANFactor.total
        (primonCuntzKANFactor n))) =
        ∑ i : Fin (n + 1), Real.log ((i.1 + 1 : ℝ)) := by
  exact ⟨D_n_selfAdjoint n, D_n_comm n,
    by simp [primonCuntzKANFactor],
    by simp [primonCuntzKANFactor],
    primonCuntz_tower_kan_log_bridge n⟩

/-- Concrete Dirac-colimit record using this explicit finite model. -/
def primonCuntzDiracData : InfoGeometry.Canonical.DiracColimit.DiracColimitData :=
  { Stage := Stage
  , hNorm := by infer_instance
  , hIP := by infer_instance
  , hCS := by infer_instance
  , emb := embIsometry
  , D := D_n
  , hD_selfAdj := by intro n; exact D_n_selfAdjoint n
  , hD_comm := D_n_comm
  }

/-- A synthesis lemma in the same explicit style as previous scaffold files. -/
theorem primon_cuntz_tower_synthesis :
    (∀ n, ∀ f g : Stage n, emb n (f + g) = emb n f + emb n g) ∧
    (∀ n, ∀ f : Stage n, ‖embFun n f‖ = ‖f‖) ∧
    (∀ n, ∀ f g : Stage n, inner ℂ ((D_n n) f) g = inner ℂ f ((D_n n) g)) ∧
    (∀ n, diracHodgeCuntz n = D_n n) ∧
    (∀ n, (D_n (n + 1)).comp (emb n).toContinuousLinearMap =
      (emb n).toContinuousLinearMap.comp (D_n n)) ∧
    (∀ n, ∀ f : Stage n,
      stageToSequence (n + 1) (emb n f) = stageToSequence n f) ∧
    (∀ n, ∀ f : Stage n,
      stageToSequence n ((D_n n) f) = algebraicDirac (stageToSequence n f)) ∧
    (∀ n, ∀ f : Stage n,
      stageToSequence n (diracHodgeCuntz n f) =
        algebraicDirac (stageToSequence n f)) ∧
    (∀ n, ∀ f : Stage n,
      stageToSequence (n + 1) (diracHodgeCuntz (n + 1) (emb n f)) =
        stageToSequence n (diracHodgeCuntz n f)) ∧
    (∀ n k, ∀ f : Stage n,
      stageToSequence (n + k) (embIter n k f) = stageToSequence n f) ∧
    (∀ n k, ∀ f : Stage n,
      stageToSequence (n + k)
          (diracHodgeCuntz (n + k) (embIter n k f)) =
        stageToSequence n (diracHodgeCuntz n f)) ∧
    (∀ x : CuntzSequence, x ∈ AlgebraicCuntzColimit →
      algebraicDirac x ∈ AlgebraicCuntzColimit) := by
  constructor
  · intro n f g
    exact (emb n).map_add f g
  constructor
  · intro n f
    exact emb_isometry n f
  constructor
  · intro n f g
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (D_n_selfAdjoint n)) f g
  constructor
  · intro n
    exact diracHodgeCuntz_eq_D_n n
  constructor
  · intro n
    exact D_n_comm n
  constructor
  · intro n f
    exact stageToSequence_emb n f
  constructor
  · intro n f
    exact stageToSequence_D n f
  constructor
  · intro n f
    exact stageToSequence_diracHodgeCuntz n f
  constructor
  · intro n f
    exact diracHodgeCuntz_emb_compatible n f
  constructor
  · intro n k f
    exact stageToSequence_embIter n k f
  constructor
  · intro n k f
    exact diracHodgeCuntz_embIter_compatible n k f
  · intro x hx
    exact algebraicDirac_preserves_colimit hx

end InfoGeometry.Quantum.PrimonCuntzTower
