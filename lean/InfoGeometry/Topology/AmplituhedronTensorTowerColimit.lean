import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Tietze
import InfoGeometry.Canonical.PositiveGrassmannianAmplituhedron
import InfoGeometry.Topology.PositiveGrassmannianAmplituhedronTopological

/-!
# Amplituhedron Tensor Tower Colimit

This module keeps only the finite boundary-face tower that is actually
supported by the current mathlib-style codebase:

* the finite amplituhedron chart is a matrix carrier over `ℝ`;
* the `n`-point stage includes into the `(n+1)`-point stage by appending a
  zero column;
* that inclusion is split by truncation, so the boundary face is a retract;
* the compatible boundary-face tower commutes with the finite inclusions.

It does not assert a canonical-form or residue theorem.
-/

namespace InfoGeometry.Topology.AmplituhedronColimit

open InfoGeometry.Canonical
open InfoGeometry.Topology

/-- Kinematic algebra for an n-point scattering amplitude. -/
abbrev AmplituhedronAlgebra (n : ℕ) := Matrix (Fin 4) (Fin n) ℝ

instance (n : ℕ) : AddCommGroup (AmplituhedronAlgebra n) := by
  dsimp [AmplituhedronAlgebra]
  infer_instance

instance (n : ℕ) : Module ℝ (AmplituhedronAlgebra n) := by
  dsimp [AmplituhedronAlgebra]
  infer_instance

/-- Natural inclusion of n-point into (n+1)-point kinematics. -/
def amplituhedronInclusion (n : ℕ) :
    AmplituhedronAlgebra n →ₗ[ℝ] AmplituhedronAlgebra (n + 1) where
  toFun M := Matrix.of (fun i j => if hj : j.val < n then M i ⟨j.val, hj⟩ else 0)
  map_add' M N := by
    ext i j
    dsimp
    split_ifs <;> simp
  map_smul' c M := by
    ext i j
    dsimp
    split_ifs <;> simp

theorem amplituhedronInclusion_injective (n : ℕ) :
    Function.Injective (amplituhedronInclusion n) := by
  intro M N h
  ext i j
  have hentry := congrArg
    (fun X : AmplituhedronAlgebra (n + 1) =>
      X i ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩) h
  simpa [amplituhedronInclusion] using hentry

theorem amplituhedronInclusion_old_column (n : ℕ)
    (M : AmplituhedronAlgebra n) (i : Fin 4) (j : Fin n) :
    amplituhedronInclusion n M i
        ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩ = M i j := by
  simp [amplituhedronInclusion]

theorem amplituhedronInclusion_new_column (n : ℕ)
    (M : AmplituhedronAlgebra n) (i : Fin 4) :
    amplituhedronInclusion n M i
        ⟨n, Nat.lt_succ_self n⟩ = 0 := by
  simp [amplituhedronInclusion]

theorem firstTwoRows_inclusion_nonnegativeChart
    (n : ℕ) (C : AmplituhedronAlgebra n)
    (hC : firstTwoRows C ∈
      positiveGrassmannianChart (k := 2) (n := n)) :
    firstTwoRows (amplituhedronInclusion n C) ∈
      positiveGrassmannianChart (k := 2) (n := n + 1) := by
  change HasNonnegativeMaximalMinors
    (firstTwoRows (amplituhedronInclusion n C))
  change HasNonnegativeMaximalMinors (firstTwoRows C) at hC
  have hcomm :
      firstTwoRows (amplituhedronInclusion n C) =
        appendZeroColumn₂ (firstTwoRows C) := by
    ext i j
    by_cases hj : j.val < n
    · simp [firstTwoRows, amplituhedronInclusion, appendZeroColumn₂, hj]
    · simp [firstTwoRows, amplituhedronInclusion, appendZeroColumn₂, hj]
  rw [hcomm]
  exact appendZeroColumn₂_nonnegative (firstTwoRows C) hC


/-- The image of the finite-stage inclusion is the coordinate boundary face
    cut out by the newly appended zero column. -/
def zeroLastColumnFace (n : ℕ) :
    Submodule ℝ (AmplituhedronAlgebra (n + 1)) where
  carrier := {M | ∀ i : Fin 4, M i ⟨n, Nat.lt_succ_self n⟩ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro M N hM hN i
    simp [hM i, hN i]
  smul_mem' := by
    intro c M hM i
    simp [hM i]

theorem amplituhedronInclusion_mem_zeroLastColumnFace
    (n : ℕ) (M : AmplituhedronAlgebra n) :
    amplituhedronInclusion n M ∈ zeroLastColumnFace n := by
  intro i
  exact amplituhedronInclusion_new_column n M i

/-- The coordinate zero-last-column face is closed in the ambient matrix
topology. -/
theorem isClosed_zeroLastColumnFace (n : ℕ) :
    IsClosed (zeroLastColumnFace n : Set (AmplituhedronAlgebra (n + 1))) := by
  change IsClosed
    ({M : AmplituhedronAlgebra (n + 1) | ∀ i : Fin 4, M i ⟨n, Nat.lt_succ_self n⟩ = 0} : Set _)
  rw [show ({M : AmplituhedronAlgebra (n + 1) | ∀ i : Fin 4, M i ⟨n, Nat.lt_succ_self n⟩ = 0} : Set _) =
    ⋂ i : Fin 4, {M : AmplituhedronAlgebra (n + 1) | M i ⟨n, Nat.lt_succ_self n⟩ = 0} by
      ext M
      simp]
  apply isClosed_iInter
  intro i
  have hrow : Continuous (fun M : AmplituhedronAlgebra (n + 1) => M i) :=
    continuous_apply i
  have hcol : Continuous (fun v : Fin (n + 1) → ℝ => v ⟨n, Nat.lt_succ_self n⟩) :=
    continuous_apply _
  exact isClosed_singleton.preimage (hcol.comp hrow)

def truncateLastColumn (n : ℕ) :
    AmplituhedronAlgebra (n + 1) →ₗ[ℝ] AmplituhedronAlgebra n where
  toFun M := Matrix.of (fun i j =>
    M i ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩)
  map_add' M N := by
    ext i j
    simp
  map_smul' c M := by
    ext i j
    simp

theorem truncateLastColumn_comp_amplituhedronInclusion (n : ℕ) :
    (truncateLastColumn n).comp (amplituhedronInclusion n) =
      LinearMap.id := by
  ext M i j
  simp [truncateLastColumn, amplituhedronInclusion]

theorem amplituhedronInclusion_range_eq_zeroLastColumnFace (n : ℕ) :
    LinearMap.range (amplituhedronInclusion n) =
      zeroLastColumnFace n := by
  apply le_antisymm
  · rintro _ ⟨M, rfl⟩
    exact amplituhedronInclusion_mem_zeroLastColumnFace n M
  · intro M hM
    refine ⟨truncateLastColumn n M, ?_⟩
    ext i j
    by_cases hj : j.val < n
    · simp [amplituhedronInclusion, truncateLastColumn, hj]
    · have hj_eq : j = ⟨n, Nat.lt_succ_self n⟩ := by
        apply Fin.ext
        have hj_le : j.val ≤ n := Nat.le_of_lt_succ j.isLt
        have hj_ge : n ≤ j.val := Nat.le_of_not_lt hj
        exact Nat.le_antisymm hj_le hj_ge
      subst hj_eq
      simp [amplituhedronInclusion, truncateLastColumn, hM i]

theorem amplituhedronInclusion_range_isClosed (n : ℕ) :
    IsClosed (LinearMap.range (amplituhedronInclusion n) : Set (AmplituhedronAlgebra (n + 1))) := by
  rw [amplituhedronInclusion_range_eq_zeroLastColumnFace]
  exact isClosed_zeroLastColumnFace n

/-- The boundary face is bundled as a linear copy of the preceding stage. -/
def boundaryFaceEmbedding (n : ℕ) :
    AmplituhedronAlgebra n →ₗ[ℝ] zeroLastColumnFace n where
  toFun M :=
    ⟨amplituhedronInclusion n M,
      amplituhedronInclusion_mem_zeroLastColumnFace n M⟩
  map_add' M N := by
    ext i j
    by_cases hj : (j : Fin (n + 1)).val < n
    · simp [amplituhedronInclusion, hj]
    · simp [amplituhedronInclusion, hj]
  map_smul' c M := by
    ext i j
    by_cases hj : (j : Fin (n + 1)).val < n
    · simp [amplituhedronInclusion, hj]
    · simp [amplituhedronInclusion, hj]

theorem boundaryFaceEmbedding_injective (n : ℕ) :
    Function.Injective (boundaryFaceEmbedding n) := by
  intro M N h
  apply amplituhedronInclusion_injective n
  exact congrArg Subtype.val h

theorem boundaryFaceEmbedding_surjective (n : ℕ) :
    Function.Surjective (boundaryFaceEmbedding n) := by
  intro X
  have hX : X.1 ∈ LinearMap.range (amplituhedronInclusion n) := by
    rw [amplituhedronInclusion_range_eq_zeroLastColumnFace]
    exact X.2
  rcases hX with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  apply Subtype.ext
  exact hM

noncomputable def boundaryFaceEquiv (n : ℕ) :
    AmplituhedronAlgebra n ≃ₗ[ℝ] zeroLastColumnFace n :=
  LinearEquiv.ofBijective
    (boundaryFaceEmbedding n)
    ⟨boundaryFaceEmbedding_injective n, boundaryFaceEmbedding_surjective n⟩

/-- The boundary face equivalence is a genuine homeomorphism of the
finite-dimensional topological spaces. -/
noncomputable def boundaryFaceHomeomorph (n : ℕ) :
    AmplituhedronAlgebra n ≃ₜ zeroLastColumnFace n :=
  (boundaryFaceEquiv n).toContinuousLinearEquiv.toHomeomorph

/-- The zero-last-column face retracts back to the previous finite stage. -/
def boundaryFaceRetraction (n : ℕ) :
    zeroLastColumnFace n →ₗ[ℝ] AmplituhedronAlgebra n :=
  (truncateLastColumn n).comp (Submodule.subtype (zeroLastColumnFace n))

theorem boundaryFaceRetraction_comp_boundaryFaceEmbedding (n : ℕ) :
    (boundaryFaceRetraction n).comp (boundaryFaceEmbedding n) =
      LinearMap.id := by
  ext M i j
  simp [boundaryFaceRetraction, boundaryFaceEmbedding,
    truncateLastColumn, amplituhedronInclusion]

/-- Boundary faces themselves form a compatible tower: extending a point of
    the old face appends one further zero column. -/
def boundaryFaceInclusion (n : ℕ) :
    zeroLastColumnFace n →ₗ[ℝ] zeroLastColumnFace (n + 1) where
  toFun X :=
    ⟨amplituhedronInclusion (n + 1) X.1,
      amplituhedronInclusion_mem_zeroLastColumnFace (n + 1) X.1⟩
  map_add' X Y := by
    ext i j
    by_cases hj : (j : Fin (n + 1 + 1)).val ≤ n
    · simp [amplituhedronInclusion, hj]
    · simp [amplituhedronInclusion, hj]
  map_smul' c X := by
    ext i j
    by_cases hj : (j : Fin (n + 1 + 1)).val ≤ n
    · simp [amplituhedronInclusion, hj]
    · simp [amplituhedronInclusion, hj]

theorem boundaryFaceInclusion_injective (n : ℕ) :
    Function.Injective (boundaryFaceInclusion n) := by
  intro X Y h
  apply Subtype.ext
  apply amplituhedronInclusion_injective (n + 1)
  exact congrArg Subtype.val h

theorem boundaryFace_tower_comm (n : ℕ) (M : AmplituhedronAlgebra n) :
    boundaryFaceInclusion n
        (boundaryFaceEmbedding n M) =
      boundaryFaceEmbedding (n + 1)
        (amplituhedronInclusion n M) := by
  apply Subtype.ext
  rfl

end InfoGeometry.Topology.AmplituhedronColimit
