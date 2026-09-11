import InfoGeometry.Topology.AmplituhedronTopCatStageDiagram
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Transport of symbolic feasible regions across a stage inclusion

The zero-column inclusion sends a 3-column feasible region into a 4-column
feasible region whenever old coordinates agree and the new coordinate target
contains zero.  The resulting subtype map is continuous.
-/

namespace InfoGeometry.Topology.AmplituhedronColimit

def initialFeasible
    (targets : (Fin 4 × Fin 3) → Set ℝ) :
    Set (AmplituhedronAlgebra 3) :=
  {M | ∀ ij, M ij.1 ij.2 ∈ targets ij}

def extendedFeasible
    (targets : (Fin 4 × Fin 4) → Set ℝ) :
    Set (AmplituhedronAlgebra 4) :=
  {M | ∀ ij, M ij.1 ij.2 ∈ targets ij}

theorem isClosed_initialFeasible
    (targets : (Fin 4 × Fin 3) → Set ℝ)
    (hclosed : ∀ ij, IsClosed (targets ij)) :
    IsClosed (initialFeasible targets) := by
  rw [show initialFeasible targets =
      ⋂ ij, {M : AmplituhedronAlgebra 3 | M ij.1 ij.2 ∈ targets ij} by
    ext M
    simp [initialFeasible]]
  exact isClosed_iInter (fun ij =>
    (hclosed ij).preimage ((continuous_apply ij.2).comp (continuous_apply ij.1)))

theorem isClosed_extendedFeasible
    (targets : (Fin 4 × Fin 4) → Set ℝ)
    (hclosed : ∀ ij, IsClosed (targets ij)) :
    IsClosed (extendedFeasible targets) := by
  rw [show extendedFeasible targets =
      ⋂ ij, {M : AmplituhedronAlgebra 4 | M ij.1 ij.2 ∈ targets ij} by
    ext M
    simp [extendedFeasible]]
  exact isClosed_iInter (fun ij =>
    (hclosed ij).preimage ((continuous_apply ij.2).comp (continuous_apply ij.1)))

def initialBoundedFeasible
    (targets : (Fin 4 × Fin 3) → Set ℝ) (B : ℝ) :
    Set (AmplituhedronAlgebra 3) :=
  initialFeasible targets ∩
    positiveGrassmannianCoordinateBox (k := 4) (n := 3) B

def extendedBoundedFeasible
    (targets : (Fin 4 × Fin 4) → Set ℝ) (B : ℝ) :
    Set (AmplituhedronAlgebra 4) :=
  extendedFeasible targets ∩
    positiveGrassmannianCoordinateBox (k := 4) (n := 4) B

theorem isCompact_initialBoundedFeasible
    (targets : (Fin 4 × Fin 3) → Set ℝ) (B : ℝ)
    (hclosed : ∀ ij, IsClosed (targets ij)) :
    IsCompact (initialBoundedFeasible targets B) := by
  unfold initialBoundedFeasible
  simpa [Set.inter_comm] using
    (isCompact_positiveGrassmannianCoordinateBox (k := 4) (n := 3) B).inter_right
      (isClosed_initialFeasible targets hclosed)

theorem isCompact_extendedBoundedFeasible
    (targets : (Fin 4 × Fin 4) → Set ℝ) (B : ℝ)
    (hclosed : ∀ ij, IsClosed (targets ij)) :
    IsCompact (extendedBoundedFeasible targets B) := by
  unfold extendedBoundedFeasible
  simpa [Set.inter_comm] using
    (isCompact_positiveGrassmannianCoordinateBox (k := 4) (n := 4) B).inter_right
      (isClosed_extendedFeasible targets hclosed)

theorem inclusion_maps_feasible
    (targets₃ : (Fin 4 × Fin 3) → Set ℝ)
    (targets₄ : (Fin 4 × Fin 4) → Set ℝ)
    (h_old : ∀ (i : Fin 4) (j : Fin 3),
      targets₄ (i, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 3)⟩) =
        targets₃ (i, j))
    (h_new : ∀ i : Fin 4,
      (0 : ℝ) ∈ targets₄ (i, ⟨3, Nat.lt_succ_self 3⟩))
    {M : AmplituhedronAlgebra 3} (hM : M ∈ initialFeasible targets₃) :
    amplituhedronInclusion 3 M ∈ extendedFeasible targets₄ := by
  intro ij
  by_cases hj : ij.2.val < 3
  · let j3 : Fin 3 := ⟨ij.2.val, hj⟩
    have hij : ij.2 =
        ⟨j3.val, Nat.lt_trans j3.isLt (Nat.lt_succ_self 3)⟩ := by
      apply Fin.ext
      rfl
    dsimp [amplituhedronInclusion]
    rw [dif_pos hj]
    have htargets : targets₄ ij = targets₃ (ij.1, j3) := by
      rw [show ij =
          (ij.1, ⟨j3.val, Nat.lt_trans j3.isLt (Nat.lt_succ_self 3)⟩) by
        apply Prod.ext <;> simp [hij]]
      exact h_old ij.1 j3
    rw [htargets]
    exact hM (ij.1, j3)
  · have hjlast : ij.2 = ⟨3, Nat.lt_succ_self 3⟩ := by
      apply Fin.ext
      have hle : ij.2.val ≤ 3 := Nat.le_of_lt_succ ij.2.isLt
      have hge : 3 ≤ ij.2.val := Nat.le_of_not_lt hj
      exact Nat.le_antisymm hle hge
    dsimp [amplituhedronInclusion]
    rw [dif_neg hj]
    have htargets : targets₄ ij =
        targets₄ (ij.1, ⟨3, Nat.lt_succ_self 3⟩) := by
      rw [show ij = (ij.1, ⟨3, Nat.lt_succ_self 3⟩) by
        apply Prod.ext <;> simp [hjlast]]
    rw [htargets]
    exact h_new ij.1

theorem inclusion_maps_boundedFeasible
    (targets₃ : (Fin 4 × Fin 3) → Set ℝ)
    (targets₄ : (Fin 4 × Fin 4) → Set ℝ)
    (h_old : ∀ (i : Fin 4) (j : Fin 3),
      targets₄ (i, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 3)⟩) =
        targets₃ (i, j))
    (h_new : ∀ i : Fin 4,
      (0 : ℝ) ∈ targets₄ (i, ⟨3, Nat.lt_succ_self 3⟩))
    (B : ℝ) (hB : 0 ≤ B)
    {M : AmplituhedronAlgebra 3}
    (hM : M ∈ initialBoundedFeasible targets₃ B) :
    amplituhedronInclusion 3 M ∈ extendedBoundedFeasible targets₄ B := by
  refine ⟨inclusion_maps_feasible targets₃ targets₄ h_old h_new hM.1, ?_⟩
  unfold initialBoundedFeasible at hM
  unfold positiveGrassmannianCoordinateBox at hM ⊢
  intro i hi
  intro j hj
  by_cases hj' : j.val < 3
  · let j3 : Fin 3 := ⟨j.val, hj'⟩
    have hj4 : j = ⟨j3.val, Nat.lt_trans j3.isLt (Nat.lt_succ_self 3)⟩ := by
      apply Fin.ext
      rfl
    rw [hj4]
    rw [amplituhedronInclusion_old_column]
    exact hM.2 i (by trivial) j3 (by trivial)
  · have hjlast : j = ⟨3, Nat.lt_succ_self 3⟩ := by
      apply Fin.ext
      exact Nat.le_antisymm (Nat.le_of_lt_succ j.isLt) (Nat.le_of_not_lt hj')
    rw [hjlast]
    rw [amplituhedronInclusion_new_column]
    exact ⟨neg_nonpos.mpr hB, hB⟩

def boundedFeasibleStageMap
    (targets₃ : (Fin 4 × Fin 3) → Set ℝ)
    (targets₄ : (Fin 4 × Fin 4) → Set ℝ)
    (h_old : ∀ (i : Fin 4) (j : Fin 3),
      targets₄ (i, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 3)⟩) =
        targets₃ (i, j))
    (h_new : ∀ i : Fin 4,
      (0 : ℝ) ∈ targets₄ (i, ⟨3, Nat.lt_succ_self 3⟩))
    (B : ℝ) (hB : 0 ≤ B) :
    {M : AmplituhedronAlgebra 3 // M ∈ initialBoundedFeasible targets₃ B} →
      {M : AmplituhedronAlgebra 4 // M ∈ extendedBoundedFeasible targets₄ B} :=
  fun M => ⟨amplituhedronInclusion 3 M.1,
    inclusion_maps_boundedFeasible targets₃ targets₄ h_old h_new B hB M.2⟩

theorem continuous_boundedFeasibleStageMap
    (targets₃ : (Fin 4 × Fin 3) → Set ℝ)
    (targets₄ : (Fin 4 × Fin 4) → Set ℝ)
    (h_old : ∀ (i : Fin 4) (j : Fin 3),
      targets₄ (i, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 3)⟩) =
        targets₃ (i, j))
    (h_new : ∀ i : Fin 4,
      (0 : ℝ) ∈ targets₄ (i, ⟨3, Nat.lt_succ_self 3⟩))
    (B : ℝ) (hB : 0 ≤ B) :
    Continuous (boundedFeasibleStageMap targets₃ targets₄ h_old h_new B hB) := by
  apply Continuous.subtype_mk
  · unfold amplituhedronInclusion
    fun_prop

theorem isCompact_boundedFeasibleStageMap_image
    (targets₃ : (Fin 4 × Fin 3) → Set ℝ)
    (targets₄ : (Fin 4 × Fin 4) → Set ℝ)
    (h_old : ∀ (i : Fin 4) (j : Fin 3),
      targets₄ (i, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 3)⟩) =
        targets₃ (i, j))
    (h_new : ∀ i : Fin 4,
      (0 : ℝ) ∈ targets₄ (i, ⟨3, Nat.lt_succ_self 3⟩))
    (B : ℝ) (hB : 0 ≤ B)
    (hclosed₃ : ∀ ij, IsClosed (targets₃ ij)) :
    IsCompact
      (boundedFeasibleStageMap targets₃ targets₄ h_old h_new B hB '' Set.univ) := by
  letI : CompactSpace {M : AmplituhedronAlgebra 3 // M ∈ initialBoundedFeasible targets₃ B} :=
    isCompact_iff_compactSpace.mp
      (isCompact_initialBoundedFeasible targets₃ B hclosed₃)
  exact isCompact_univ.image
    (continuous_boundedFeasibleStageMap targets₃ targets₄ h_old h_new B hB)

def feasibleStageMap
    (targets₃ : (Fin 4 × Fin 3) → Set ℝ)
    (targets₄ : (Fin 4 × Fin 4) → Set ℝ)
    (h_old : ∀ (i : Fin 4) (j : Fin 3),
      targets₄ (i, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 3)⟩) =
        targets₃ (i, j))
    (h_new : ∀ i : Fin 4,
      (0 : ℝ) ∈ targets₄ (i, ⟨3, Nat.lt_succ_self 3⟩)) :
    {M : AmplituhedronAlgebra 3 // M ∈ initialFeasible targets₃} →
      {M : AmplituhedronAlgebra 4 // M ∈ extendedFeasible targets₄} :=
  fun M => ⟨amplituhedronInclusion 3 M.1,
    inclusion_maps_feasible targets₃ targets₄ h_old h_new M.2⟩

theorem continuous_feasibleStageMap
    (targets₃ : (Fin 4 × Fin 3) → Set ℝ)
    (targets₄ : (Fin 4 × Fin 4) → Set ℝ)
    (h_old : ∀ (i : Fin 4) (j : Fin 3),
      targets₄ (i, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 3)⟩) =
        targets₃ (i, j))
    (h_new : ∀ i : Fin 4,
      (0 : ℝ) ∈ targets₄ (i, ⟨3, Nat.lt_succ_self 3⟩)) :
    Continuous (feasibleStageMap targets₃ targets₄ h_old h_new) := by
  apply Continuous.subtype_mk
  · unfold amplituhedronInclusion
    fun_prop

theorem isCompact_feasibleStageMap_image
    (targets₃ : (Fin 4 × Fin 3) → Set ℝ)
    (targets₄ : (Fin 4 × Fin 4) → Set ℝ)
    (h_old : ∀ (i : Fin 4) (j : Fin 3),
      targets₄ (i, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self 3)⟩) =
        targets₃ (i, j))
    (h_new : ∀ i : Fin 4,
      (0 : ℝ) ∈ targets₄ (i, ⟨3, Nat.lt_succ_self 3⟩))
    (K : Set {M : AmplituhedronAlgebra 3 // M ∈ initialFeasible targets₃})
    (hK : IsCompact K) :
    IsCompact (feasibleStageMap targets₃ targets₄ h_old h_new '' K) := by
  exact hK.image (continuous_feasibleStageMap targets₃ targets₄ h_old h_new)

end InfoGeometry.Topology.AmplituhedronColimit
