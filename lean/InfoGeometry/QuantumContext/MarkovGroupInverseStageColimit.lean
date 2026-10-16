/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.HartwigSouriauFrameDrazin
import InfoGeometry.QuantumContext.PetzMatrixStageLimit
import InfoGeometry.QuantumContext.MarkovAttentionGroupInverse
import InfoGeometry.QuantumContext.MarkovMetriplecticGroupInverseLift

/-!
# Group-inverse transport through the complex matrix-stage colimit

The finite stages are full matrix rings `Matrix (BitWord n) (BitWord n) ℂ`.
Their existing transition maps and canonical quotient-colimit inclusions are
unital ring homomorphisms, so they preserve supplied group-inverse equations
and their regular and complementary idempotents. This module transports
witnesses; it does not construct an inverse for an arbitrary stage element or
assert that positivity or stochasticity is preserved by these algebra maps.
-/

namespace InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit

open InfoGeometry.Canonical.HartwigSouriauFrameDrazin
open InfoGeometry.Canonical.ComplexMatrixStage
open InfoGeometry.Canonical.GenuineMatrixStageMorphism
open InfoGeometry.Canonical.MatrixStageInductiveLimit
open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.QuantumContext.MarkovDrazin

/-! ## Finite matrix-stage transport -/

/-- A supplied group-inverse witness is preserved by every transition map in
the noncommutative complex matrix tower. -/
theorem groupInverse_stageMorphism {m n : ℕ} (h : m ≤ n)
    (A G : Stage m) (hG : IsGroupInverse A G) :
    IsGroupInverse (stageMorphism m n h A) (stageMorphism m n h G) := by
  constructor
  · have h₁ := congrArg (stageMorphism m n h) hG.1
    simpa only [map_mul] using h₁
  constructor
  · have h₂ := congrArg (stageMorphism m n h) hG.2.1
    simpa only [map_mul] using h₂
  · have h₃ := congrArg (stageMorphism m n h) hG.2.2
    simpa only [map_mul] using h₃

/-- The regular idempotent of a stage group inverse is transported by the same
matrix-stage map. -/
theorem regularIdempotent_stageMorphism {m n : ℕ} (h : m ≤ n)
    (A G : Stage m) :
    stageMorphism m n h (regularIdempotent A G) =
      regularIdempotent (stageMorphism m n h A) (stageMorphism m n h G) := by
  change stageMorphism m n h (A * G) =
    stageMorphism m n h A * stageMorphism m n h G
  exact map_mul (stageMorphism m n h) A G

/-- The complementary idempotent of a stage group inverse is transported by
the same matrix-stage map. -/
theorem principalIdempotent_stageMorphism {m n : ℕ} (h : m ≤ n)
    (A G : Stage m) :
    stageMorphism m n h (principalIdempotent A G) =
      principalIdempotent (stageMorphism m n h A) (stageMorphism m n h G) := by
  change stageMorphism m n h (1 - A * G) =
    1 - stageMorphism m n h A * stageMorphism m n h G
  simp only [map_sub, map_one, map_mul]

/-- The transported regular element is an idempotent whenever its source
elements form a group-inverse pair. -/
theorem regularIdempotent_stageMorphism_idempotent {m n : ℕ}
    (h : m ≤ n) (A G : Stage m) (hG : IsGroupInverse A G) :
    regularIdempotent (stageMorphism m n h A) (stageMorphism m n h G) *
      regularIdempotent (stageMorphism m n h A) (stageMorphism m n h G) =
        regularIdempotent (stageMorphism m n h A) (stageMorphism m n h G) := by
  exact regularIdempotent_idempotent (groupInverse_stageMorphism h A G hG)

/-- The transported complementary element is an idempotent whenever its
source elements form a group-inverse pair. -/
theorem principalIdempotent_stageMorphism_idempotent {m n : ℕ}
    (h : m ≤ n) (A G : Stage m) (hG : IsGroupInverse A G) :
    principalIdempotent (stageMorphism m n h A) (stageMorphism m n h G) *
      principalIdempotent (stageMorphism m n h A) (stageMorphism m n h G) =
        principalIdempotent (stageMorphism m n h A) (stageMorphism m n h G) := by
  exact principalIdempotent_idempotent (groupInverse_stageMorphism h A G hG)

/-! ## Real Markov matrices in a complex finite stage -/

/-- Entrywise complexification as an `ℝ`-algebra hom on a full finite matrix
ring. The matrix carrier and its multiplication remain noncommutative. -/
noncomputable def realMatrixComplexifyAlgHom {ι : Type*} [Fintype ι]
    [DecidableEq ι] : Matrix ι ι ℝ →ₐ[ℝ] Matrix ι ι ℂ where
  toFun A := (algebraMap ℝ ℂ).mapMatrix A
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [RingHom.mapMatrix_apply, Matrix.one_apply, h]
  map_mul' A B := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.mul_apply, map_mul]
  map_zero' := by
    ext i j
    simp [RingHom.mapMatrix_apply]
  map_add' A B := by
    ext i j
    simp [RingHom.mapMatrix_apply]
  commutes' r := by
    ext i j
    by_cases h : i = j <;>
      simp [RingHom.mapMatrix_apply, Matrix.algebraMap_eq_diagonal, h]

/-- Reindex and complexify a real full-matrix operator into the repository's
complex `BitWord` stage. The equivalence is explicit, so the finite dimension
match is part of the theorem input rather than inferred from notation. -/
noncomputable def realMatrixToComplexStage {ι : Type*} [Fintype ι]
    [DecidableEq ι] (n : ℕ) (e : ι ≃ BitWord n) :
    Matrix ι ι ℝ →ₐ[ℝ] Stage n :=
  (Matrix.reindexAlgEquiv ℝ ℂ e).toAlgHom.comp realMatrixComplexifyAlgHom

/-- Complexification and reindexing preserve a supplied group-inverse
witness on the full finite matrix carrier. -/
theorem groupInverse_realMatrixToComplexStage {ι : Type*} [Fintype ι]
    [DecidableEq ι] (n : ℕ) (e : ι ≃ BitWord n)
    (A G : Matrix ι ι ℝ) (hG : IsGroupInverse A G) :
    IsGroupInverse (realMatrixToComplexStage n e A)
      (realMatrixToComplexStage n e G) := by
  constructor
  · have h₁ := congrArg (realMatrixToComplexStage n e) hG.1
    simpa only [map_mul] using h₁
  constructor
  · have h₂ := congrArg (realMatrixToComplexStage n e) hG.2.1
    simpa only [map_mul] using h₂
  · have h₃ := congrArg (realMatrixToComplexStage n e) hG.2.2
    simpa only [map_mul] using h₃

/-- Every finite row-stochastic matrix has its Markov Laplacian group inverse
represented at any explicitly equivalent `BitWord` stage. This transports
the algebraic witness; complexification does not claim to preserve an ordered
or stochastic interpretation over `ℂ`. -/
theorem exists_rowStochastic_groupInverse_inComplexStage
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (n : ℕ) (e : ι ≃ BitWord n) (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ G : Stage n,
      IsGroupInverse (realMatrixToComplexStage n e (1 - P)) G := by
  obtain ⟨D, hD⟩ := exists_stochastic_laplacian_groupInverse P hP
  obtain ⟨G, hG⟩ := matrix_groupInverse_of_linear_groupInverse (1 - P) D (by
    simpa using hD)
  exact ⟨realMatrixToComplexStage n e G,
    groupInverse_realMatrixToComplexStage n e (1 - P) G hG⟩

/-! ## Quotient direct-colimit transport -/

/-- A supplied finite-stage group-inverse witness remains a group-inverse
witness after the canonical inclusion into the quotient matrix-stage colimit. -/
theorem groupInverse_canonicalStageHom (n : ℕ) (A G : Stage n)
    (hG : IsGroupInverse A G) :
    IsGroupInverse (canonicalStageHom n A) (canonicalStageHom n G) := by
  constructor
  · have h₁ := congrArg (canonicalStageHom n) hG.1
    simpa only [map_mul] using h₁
  constructor
  · have h₂ := congrArg (canonicalStageHom n) hG.2.1
    simpa only [map_mul] using h₂
  · have h₃ := congrArg (canonicalStageHom n) hG.2.2
    simpa only [map_mul] using h₃

/-- The finite Markov Laplacian group-inverse witness survives the canonical
inclusion into the quotient matrix-stage colimit. The conclusion is an
algebraic group-inverse pair in the colimit algebra, not a Markov kernel over
complex scalars. -/
theorem exists_rowStochastic_groupInverse_inMatrixStageLimit
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (n : ℕ) (e : ι ≃ BitWord n) (P : Matrix ι ι ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ ι) :
    ∃ G : MatrixStageLimit,
      IsGroupInverse
        (canonicalStageHom n (realMatrixToComplexStage n e (1 - P))) G := by
  obtain ⟨G, hG⟩ := exists_rowStochastic_groupInverse_inComplexStage n e P hP
  exact ⟨canonicalStageHom n G,
    groupInverse_canonicalStageHom n _ G hG⟩

/-- The regular idempotent is compatible with the quotient-colimit inclusion. -/
theorem regularIdempotent_canonicalStageHom (n : ℕ) (A G : Stage n) :
    canonicalStageHom n (regularIdempotent A G) =
      regularIdempotent (canonicalStageHom n A) (canonicalStageHom n G) := by
  change canonicalStageHom n (A * G) =
    canonicalStageHom n A * canonicalStageHom n G
  exact map_mul (canonicalStageHom n) A G

/-- The complementary idempotent is compatible with the quotient-colimit
inclusion. -/
theorem principalIdempotent_canonicalStageHom (n : ℕ) (A G : Stage n) :
    canonicalStageHom n (principalIdempotent A G) =
      principalIdempotent (canonicalStageHom n A) (canonicalStageHom n G) := by
  change canonicalStageHom n (1 - A * G) =
    1 - canonicalStageHom n A * canonicalStageHom n G
  simp only [map_sub, map_one, map_mul]

/-- The regular idempotent remains idempotent in the quotient colimit when
its finite-stage source is a group-inverse pair. -/
theorem regularIdempotent_canonicalStageHom_idempotent (n : ℕ)
    (A G : Stage n) (hG : IsGroupInverse A G) :
    regularIdempotent (canonicalStageHom n A) (canonicalStageHom n G) *
      regularIdempotent (canonicalStageHom n A) (canonicalStageHom n G) =
        regularIdempotent (canonicalStageHom n A) (canonicalStageHom n G) := by
  exact regularIdempotent_idempotent (groupInverse_canonicalStageHom n A G hG)

/-- The complementary idempotent remains idempotent in the quotient colimit
when its finite-stage source is a group-inverse pair. -/
theorem principalIdempotent_canonicalStageHom_idempotent (n : ℕ)
    (A G : Stage n) (hG : IsGroupInverse A G) :
    principalIdempotent (canonicalStageHom n A) (canonicalStageHom n G) *
      principalIdempotent (canonicalStageHom n A) (canonicalStageHom n G) =
        principalIdempotent (canonicalStageHom n A) (canonicalStageHom n G) := by
  exact principalIdempotent_idempotent (groupInverse_canonicalStageHom n A G hG)

/-- A higher-stage regular idempotent has the same quotient-colimit image as
the idempotent represented at its source stage. -/
theorem regularIdempotent_mixedStage_readback {m n : ℕ} (h : m ≤ n)
    (A G : Stage m) :
    canonicalStageHom n
        (regularIdempotent (stageMorphism m n h A) (stageMorphism m n h G)) =
      canonicalStageHom m (regularIdempotent A G) := by
  rw [← regularIdempotent_stageMorphism h A G]
  exact congrArg (fun f : Stage m →⋆ₐ[ℂ] MatrixStageLimit =>
    f (regularIdempotent A G)) (canonicalStageHom_comp h)

/-- The complementary idempotent has the same quotient-colimit readback from
every higher stage. -/
theorem principalIdempotent_mixedStage_readback {m n : ℕ} (h : m ≤ n)
    (A G : Stage m) :
    canonicalStageHom n
        (principalIdempotent (stageMorphism m n h A) (stageMorphism m n h G)) =
      canonicalStageHom m (principalIdempotent A G) := by
  rw [← principalIdempotent_stageMorphism h A G]
  exact congrArg (fun f : Stage m →⋆ₐ[ℂ] MatrixStageLimit =>
    f (principalIdempotent A G)) (canonicalStageHom_comp h)

end InfoGeometry.QuantumContext.MarkovGroupInverseStageColimit
