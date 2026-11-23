/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Block
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Pi
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinExistenceBridge
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Volume.Pfaffian
import InfoGeometry.Canonical.DiracSouriauDecoupledDrazin
import InfoGeometry.Algebra.GradedNullconeAlgebra

/-!
# InfoGeometry.Canonical.DiracSouriauOperator

Formalization of the 4x4 Dirac-Souriau sector of the $C\ell(4,4)$ informational
gravity framework. This module defines the block structure of the operator
and provides the constructive existence proofs for the Drazin-Penrose decoupling.

This module replaces the lyrical hypothesis of Zorn-spacetime with an explicit
linkage to the `ZornMatrix` formalization.
-/

namespace InfoGeometry.Canonical.DiracSouriau

open Matrix

/-- Trap T16 non-commutativity witness for `2 × 2` matrices over any nontrivial commutative ring `R`. -/
theorem mat2_ring_mul_noncommutative_witness {R : Type*} [CommRing R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 2) (Fin 2) R, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- Trap T16 non-commutativity witness for `2 × 2` real matrices in the Dirac-Souriau sector. -/
theorem mat2_mul_noncommutative_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], ?_⟩
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00

/--
The 4x4 Dirac-Souriau Sector representation of the $C\ell(4,4)$ informational 
gravity operator. This structure formalizes the block-decoupled 
thermodynamic/topological interface.

Spacetime is an emergent macroscopic statistic of Zorn spinors,
as formalized in `InfoGeometry.Canonical.ZornSpinor`.
-/
@[rep_depth transport]
structure DiracSouriauSector (R : Type*) [CommRing R] where
  /-- Bosonic (Thermodynamic) Block: represents thermal fluctuations (A). -/
  A : Matrix (Fin 2) (Fin 2) R
  /-- Fermionic (Topological) Block: represents topological charge and regularization (K). -/
  K : Matrix (Fin 2) (Fin 2) R
  /-- Supersymmetric Intertwiner: mediates thermodynamic-topological coupling (B). -/
  B : Matrix (Fin 2) (Fin 2) R

namespace DiracSouriauSector

variable {R : Type*} [CommRing R]

/--
Construct a Dirac-Souriau sector from Zorn matrix coefficients.
This anchors the operator in the Zorn-spinor algebra.
-/

noncomputable def ofZorn (z1 z2 zB : ZornMatrix R) : DiracSouriauSector R where
  A := z1.coarseGrain
  K := z2.coarseGrain
  B := !![ZornMatrix.dot zB.x zB.y, zB.a; zB.b, ZornMatrix.dot zB.y zB.x]

/-- 
The antisymmetry constraint on the supercharge intertwiner (C) for 
$C\ell(4,4)$ vacuum stability. In this sector, C = -Bᵀ.
-/

@[rep_depth transport]
def C (S : DiracSouriauSector R) : Matrix (Fin 2) (Fin 2) R :=
  -S.B.transpose

/-- 
Assembles the blocks into the full 4x4 Dirac-Souriau supermatrix.
This matrix is the "reduced owner surface" for the 4x4 sector.
Using the sum type `Fin 2 ⊕ Fin 2` for the index set to match `fromBlocks`.
-/

@[rep_depth transport]
def toMatrix (S : DiracSouriauSector R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  fromBlocks S.A S.B S.C S.K

/-- The assembled operator is exactly the declared block matrix. -/

@[rep_depth transport]
theorem toMatrix_eq_fromBlocks (S : DiracSouriauSector R) :
    S.toMatrix = fromBlocks S.A S.B S.C S.K := by
  rfl

/--
Constructive Proof: Drazin-Penrose existence for fields.
Any Dirac-Souriau operator over a field admits a Drazin inverse,
rigorously enabling the split into a topological Core and a dissipative Shell.
-/

theorem exists_drazinInverse {K : Type*} [Field K] (S : DiracSouriauSector K) :
    ∃ (k : ℕ) (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K),
      InfoGeometry.Canonical.Drazin.IsDrazinInverse S.toMatrix D k := by
  -- Convert Matrix to Endomorphism
  let M := S.toMatrix
  letI : AddCommGroup ((Fin 2 ⊕ Fin 2) → K) := Pi.addCommGroup
  letI : Module K ((Fin 2 ⊕ Fin 2) → K) :=
    Pi.module (Fin 2 ⊕ Fin 2) (fun _ => K) K
  let f : Module.End K ((Fin 2 ⊕ Fin 2) → K) := Matrix.toLin' M
  -- Use global existence for finite-dimensional endomorphisms
  obtain ⟨k, d, hd⟩ :=
    DrazinExistenceBridge.exists_canonicalDrazinInverse_global f
  -- Convert Endomorphism back to Matrix using LinearMap.toMatrix'
  let D := LinearMap.toMatrix' d
  refine ⟨k, D, ?_⟩
  -- Prove the Drazin laws in Matrix form
  constructor
  · apply Matrix.toLin'.injective
    simpa [M, D, Matrix.toLin'_toMatrix', Matrix.toLin'_mul,
      Module.End.mul_eq_comp] using hd.1
  · constructor
    · apply Matrix.toLin'.injective
      simpa [M, D, Matrix.toLin'_toMatrix', Matrix.toLin'_mul,
        Module.End.mul_eq_comp] using hd.2.1
    · apply Matrix.toLin'.injective
      -- Adjust for composition order: (f^(k+1)) ∘ₗ d = f^k
      have h3 := hd.2.2
      simpa [M, D, Matrix.toLin'_toMatrix', Matrix.toLin'_mul,
        Matrix.toLin'_pow, Module.End.mul_eq_comp] using h3

/--
Predicate encoding the Drazin inverse property.
This is now a proven property for sectors over fields.
-/

def HasDrazinInverse (S : DiracSouriauSector R) (k : ℕ) : Prop :=
  ∃ D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R,
    InfoGeometry.Canonical.Drazin.IsDrazinInverse S.toMatrix D k

/--
Discharge the Drazin hypothesis for field-based configurations.
-/

theorem hasDrazinInverse_of_field {K : Type*} [Field K] (S : DiracSouriauSector K) :
    ∃ k, S.HasDrazinInverse k := by
  obtain ⟨k, D, hD⟩ := S.exists_drazinInverse
  exact ⟨k, D, hD⟩

/--
Context carrying an explicit Drazin inverse for one concrete Dirac-Souriau
sector. This is intentionally proof-carrying data, not a generalized closure
claim about all block matrices.
-/

structure DrazinInverseContext (S : DiracSouriauSector R) where
  k : ℕ
  D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R
  isDrazin : InfoGeometry.Canonical.Drazin.IsDrazinInverse S.toMatrix D k

/--
The field-level Drazin existence theorem supplies an explicit inverse context
existentially. We do not choose a canonical stored inverse here.
-/

theorem exists_drazinInverseContext_of_field
    {K : Type*} [Field K] (S : DiracSouriauSector K) :
    ∃ Ctxt : DrazinInverseContext S, S.HasDrazinInverse Ctxt.k := by
  obtain ⟨k, D, hD⟩ := S.exists_drazinInverse
  exact ⟨⟨k, D, hD⟩, ⟨D, hD⟩⟩

/-- A Drazin inverse context discharges the local hypothesis predicate. -/

theorem hasDrazinInverse_of_context
    {S : DiracSouriauSector R} (Ctxt : DrazinInverseContext S) :
    S.HasDrazinInverse Ctxt.k := by
  exact ⟨Ctxt.D, Ctxt.isDrazin⟩

/-- Unpack a Drazin hypothesis into its explicit witness. -/

theorem exists_drazinInverse_of_hasDrazinInverse
    {S : DiracSouriauSector R} {k : ℕ} (h : S.HasDrazinInverse k) :
    ∃ D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R,
      InfoGeometry.Canonical.Drazin.IsDrazinInverse S.toMatrix D k := by
  rcases h with ⟨D, hD⟩
  exact ⟨D, hD⟩

/--
Constructive Drazin witness from an explicit two-sided inverse of the full
assembled `4×4` block operator.  This is the source-safe invertible case:
the Drazin index is `0`.
-/

def drazinInverseContext_zero_of_twoSidedInverse
    (S : DiracSouriauSector R)
    (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (hSD : S.toMatrix * D = 1)
    (hDS : D * S.toMatrix = 1) :
    DrazinInverseContext S := by
  refine ⟨0, D, ?_⟩
  exact InfoGeometry.Canonical.Drazin.IsDrazinInverse.mk
    (by rw [hSD, hDS])
    (by rw [hDS, one_mul])
    (by simpa using hSD)

/-- The local two-sided inverse context discharges `HasDrazinInverse` at index `0`. -/

theorem hasDrazinInverse_zero_of_twoSidedInverse
    (S : DiracSouriauSector R)
    (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (hSD : S.toMatrix * D = 1)
    (hDS : D * S.toMatrix = 1) :
    S.HasDrazinInverse 0 := by
  exact ⟨D, (drazinInverseContext_zero_of_twoSidedInverse S D hSD hDS).isDrazin⟩

/--
In the decoupled case `B = 0` (hence also `C = 0`), explicit two-sided
inverses of the bosonic and topological `2×2` blocks assemble into a two-sided
inverse of the full `4×4` Dirac-Souriau operator.
-/
theorem toMatrix_has_twoSidedInverse_of_decoupled
    (S : DiracSouriauSector R)
    (Ainv Kinv : Matrix (Fin 2) (Fin 2) R)
    (hB : S.B = 0)
    (hA_right : S.A * Ainv = 1)
    (hA_left : Ainv * S.A = 1)
    (hK_right : S.K * Kinv = 1)
    (hK_left : Kinv * S.K = 1) :
    let D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
      fromBlocks Ainv 0 0 Kinv
    S.toMatrix * D = 1 ∧ D * S.toMatrix = 1 := by
  let D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
    fromBlocks Ainv 0 0 Kinv
  have hC : S.C = 0 := by
    simp [DiracSouriauSector.C, hB]
  refine ⟨?_, ?_⟩
  · ext i j <;> cases i <;> cases j <;>
      simp [DiracSouriauSector.toMatrix, DiracSouriauSector.C, hB,
        Matrix.fromBlocks_multiply, Matrix.one_apply, hA_right, hK_right]
  · ext i j <;> cases i <;> cases j <;>
      simp [DiracSouriauSector.toMatrix, DiracSouriauSector.C, hB,
        Matrix.fromBlocks_multiply, Matrix.one_apply, hA_left, hK_left]

/--
A decoupled Dirac-Souriau sector with explicit inverse blocks has Drazin index
`0`, hence lies entirely in the regular (non-nilpotent) lane.
-/
theorem hasDrazinInverse_zero_of_decoupled
    (S : DiracSouriauSector R)
    (Ainv Kinv : Matrix (Fin 2) (Fin 2) R)
    (hB : S.B = 0)
    (hA_right : S.A * Ainv = 1)
    (hA_left : Ainv * S.A = 1)
    (hK_right : S.K * Kinv = 1)
    (hK_left : Kinv * S.K = 1) :
    S.HasDrazinInverse 0 := by
  let D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
    fromBlocks Ainv 0 0 Kinv
  have hInv :=
    toMatrix_has_twoSidedInverse_of_decoupled S Ainv Kinv hB hA_right hA_left hK_right hK_left
  exact hasDrazinInverse_zero_of_twoSidedInverse S D hInv.1 hInv.2

/--
A decoupled Dirac-Souriau sector with invertible bosonic block and nilpotent
fermionic block admits a Drazin inverse of index 2.
-/
theorem hasDrazinInverse_two_of_decoupled_nilpotent
    {K : Type*} [Field K] (S : DiracSouriauSector K)
    (hB : S.B = 0)
    (hA : IsUnit S.A.det)
    (hK : S.K ^ 2 = 0) :
    S.HasDrazinInverse 2 := by
  have hC : S.C = 0 := by
    simp [C, hB]
  have hMatrix : S.toMatrix = fromBlocks S.A 0 0 S.K := by
    rw [toMatrix_eq_fromBlocks S]
    ext i j <;> cases i <;> cases j <;> simp [hB, hC]
  obtain ⟨D, hD⟩ := block_drazin_inverse_decoupled S.A hA S.K hK
  use D
  rw [hMatrix]
  exact hD

/--
Constructive inverse context for the decoupled `B = 0` lane with explicit block
inverses. This exports the existing decoupled Drazin route as proof-carrying
data instead of only the proposition `HasDrazinInverse 0`.
-/
def drazinInverseContext_zero_of_decoupled
    (S : DiracSouriauSector R)
    (Ainv Kinv : Matrix (Fin 2) (Fin 2) R)
    (hB : S.B = 0)
    (hA_right : S.A * Ainv = 1)
    (hA_left : Ainv * S.A = 1)
    (hK_right : S.K * Kinv = 1)
    (hK_left : Kinv * S.K = 1) :
    DrazinInverseContext S := by
  let D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
    fromBlocks Ainv 0 0 Kinv
  have hInv :=
    toMatrix_has_twoSidedInverse_of_decoupled S Ainv Kinv hB hA_right hA_left hK_right hK_left
  exact drazinInverseContext_zero_of_twoSidedInverse S D hInv.1 hInv.2

/--
The constructive decoupled witness context recovers the old proposition-level
surface at index `0`.
-/
theorem hasDrazinInverse_zero_of_decoupled_context
    (S : DiracSouriauSector R)
    (Ainv Kinv : Matrix (Fin 2) (Fin 2) R)
    (hB : S.B = 0)
    (hA_right : S.A * Ainv = 1)
    (hA_left : Ainv * S.A = 1)
    (hK_right : S.K * Kinv = 1)
    (hK_left : Kinv * S.K = 1) :
    S.HasDrazinInverse
      (drazinInverseContext_zero_of_decoupled S Ainv Kinv hB hA_right hA_left hK_right hK_left).k := by
  exact hasDrazinInverse_of_context
    (drazinInverseContext_zero_of_decoupled S Ainv Kinv hB hA_right hA_left hK_right hK_left)

/--
Definition-level supersymmetric stability.
The operator preserves the $C\ell(4,4)$ vacuum if the intertwiner B is
balanced by its supersymmetric partner C.
-/

@[rep_depth transport]
theorem supercharge_conservation_satisfied (S : DiracSouriauSector R) :
    S.C = -S.B.transpose := by
  rfl

/--
The Schur-complement Berezinian for the 4x4 sector.
This represents the statistical dissipation of the configuration.
-/

@[rep_depth transport]
noncomputable def berezinian [Field R] (S : DiracSouriauSector R) : R :=
  open scoped Classical in
  if IsUnit S.K.det then
    (S.A - S.B * S.K⁻¹ * S.C).det / S.K.det
  else
    0

/-- Genuine polynomial Pfaffian for a `2×2` skew-symmetric block over any commutative ring `R`. -/
@[rep_depth transport]
def pfaffianPoly (M : Matrix (Fin 2) (Fin 2) R) : R :=
  M 0 1

/-- Skew-symmetry predicate for `2×2` matrix blocks: vanishing diagonal and anti-symmetric off-diagonals. -/
@[rep_depth transport]
def IsSkew2 (M : Matrix (Fin 2) (Fin 2) R) : Prop :=
  M 0 0 = 0 ∧ M 1 1 = 0 ∧ M 1 0 = -M 0 1

/-- Exact polynomial Pfaffian-squared theorem: for any skew `2×2` matrix over a commutative ring `R`,
`(Pf M)² = det M` identically without square roots or real-analytic approximations. -/
@[rep_depth transport]
theorem pfaffianPoly_sq_eq_det (M : Matrix (Fin 2) (Fin 2) R) (h : IsSkew2 M) :
    pfaffianPoly M * pfaffianPoly M = M.det := by
  rcases h with ⟨h00, h11, h10⟩
  simp [pfaffianPoly, Matrix.det_fin_two, h00, h11, h10]

/-- Determinant of any real `2×2` skew matrix is unconditionally non-negative. -/
@[rep_depth transport]
theorem skew2_det_nonneg (M : Matrix (Fin 2) (Fin 2) ℝ) (h : IsSkew2 M) :
    0 ≤ M.det := by
  rw [← pfaffianPoly_sq_eq_det M h]
  exact mul_self_nonneg _

/-- The classical scalar Pfaffian `√det M` matches the absolute value of the genuine polynomial Pfaffian. -/
@[rep_depth transport]
theorem pfaffian_eq_abs_pfaffianPoly (M : Matrix (Fin 2) (Fin 2) ℝ) (h : IsSkew2 M) :
    Real.sqrt M.det = |pfaffianPoly M| := by
  rw [← pfaffianPoly_sq_eq_det M h]
  rw [← sq, Real.sqrt_sq_eq_abs]

/--
Scalar Pfaffian proxy for the topological sector `K`.
Under the explicit hypothesis `0 ≤ det K`, it satisfies `pfaffian² = det K`.
-/

@[rep_depth transport]
noncomputable def pfaffian (S : DiracSouriauSector ℝ) : ℝ :=
  Real.sqrt S.K.det

/-- For skew-symmetric topological sectors `K`, the Pfaffian proxy is unconditionally well-defined
and matches the absolute polynomial Pfaffian without extra determinant positivity assumptions. -/
@[rep_depth transport]
theorem pfaffian_eq_abs_pfaffianPoly_of_skew (S : DiracSouriauSector ℝ) (h : IsSkew2 S.K) :
    S.pfaffian = |pfaffianPoly S.K| :=
  pfaffian_eq_abs_pfaffianPoly S.K h

/-- The Pfaffian proxy squares to `det K` when the determinant is nonnegative. -/

@[rep_depth transport]
theorem pfaffian_sq_eq_det_of_det_nonneg
    (S : DiracSouriauSector ℝ) (hdet : 0 ≤ S.K.det) :
    S.pfaffian ^ (2 : ℕ) = S.K.det := by
  unfold pfaffian
  exact Real.sq_sqrt hdet

/-- For skew topological sectors, `pfaffian² = det K` unconditionally. -/
@[rep_depth transport]
theorem pfaffian_sq_eq_det_of_skew (S : DiracSouriauSector ℝ) (h : IsSkew2 S.K) :
    S.pfaffian ^ (2 : ℕ) = S.K.det :=
  pfaffian_sq_eq_det_of_det_nonneg S (skew2_det_nonneg S.K h)

/--
A scalar entropy functional built from the determinant-square-root proxy above
and the conditional Schur-complement Berezinian.
-/

@[rep_depth transport]
noncomputable def souriauEntropy (S : DiracSouriauSector ℝ) : ℝ :=
  Real.log (S.pfaffian) - (1 / 2) * Real.log (S.berezinian)

/-- Decoupled Dirac-Souriau entropy decomposition: for an invertible thermodynamic block `A`
and skew topological block `K`, the entropy splits into the topological Pfaffian and Fisher entropy. -/
@[rep_depth transport]
theorem souriauEntropy_decoupled_skew_split
    (S : DiracSouriauSector ℝ)
    (hB : S.B = 0)
    (hA : 0 < S.A.det)
    (hK_skew : IsSkew2 S.K)
    (hK_ne : pfaffianPoly S.K ≠ 0) :
    S.souriauEntropy = 2 * Real.log S.pfaffian - (1 / 2) * Real.log S.A.det := by
  have hC : S.C = 0 := by simp [C, hB]
  have hK_sq : S.K.det = (pfaffianPoly S.K)^2 := by
    rw [← pfaffianPoly_sq_eq_det S.K hK_skew, sq]
  have hK_pos : 0 < S.K.det := by
    rw [hK_sq]
    exact sq_pos_of_ne_zero hK_ne
  have hK_unit : IsUnit S.K.det := isUnit_iff_ne_zero.mpr hK_pos.ne'
  have hber : S.berezinian = S.A.det / S.K.det := by
    dsimp [berezinian]
    split_ifs with h
    · simp [hB, hC]
    · exact False.elim (h hK_unit)
  have hpf_eq : S.pfaffian = |pfaffianPoly S.K| := pfaffian_eq_abs_pfaffianPoly_of_skew S hK_skew
  have hpf_pos : 0 < S.pfaffian := by
    rw [hpf_eq]
    exact abs_pos.mpr hK_ne
  have hber_div : Real.log S.berezinian = Real.log S.A.det - Real.log S.K.det := by
    rw [hber]
    exact Real.log_div hA.ne' hK_pos.ne'
  have hlog_K : Real.log S.K.det = 2 * Real.log S.pfaffian := by
    have h1 : S.K.det = S.pfaffian ^ 2 := by
      change S.K.det = (Real.sqrt S.K.det) ^ 2
      exact (Real.sq_sqrt hK_pos.le).symm
    rw [h1, Real.log_pow S.pfaffian 2]
    ring
  dsimp [souriauEntropy]
  rw [hber_div, hlog_K]
  ring

/-
Hypothesis 4: Critical Stiffness Threshold.
Cosmic acceleration (Dark Energy) is hypothesized as the elastic rigidity of the
$C\ell(4,4)$ vacuum protecting topological memory (Core) from thermodynamic
collapse (Shell).
-/

/-- BPS protection is the explicit Berezinian threshold inequality. -/
@[rep_depth transport]
def IsBPSProtected (S : DiracSouriauSector ℝ) (κ_crit : ℝ) : Prop :=
  S.berezinian < κ_crit

/-- The predicate unfolds to the threshold inequality. -/
@[rep_depth transport]
theorem IsBPSProtected_iff_exists (S : DiracSouriauSector ℝ) (κ_crit : ℝ) :
    IsBPSProtected S κ_crit ↔ S.berezinian < κ_crit := Iff.rfl

/--
Absolute Pfaffian proxy: unlike `pfaffian`, this has an unconditional square
law, so callers do not need a separate `0 ≤ det K` hypothesis when the intended
readout is the determinant magnitude.
-/

@[rep_depth transport]
noncomputable def pfaffianAbs (S : DiracSouriauSector ℝ) : ℝ :=
  Real.sqrt |S.K.det|

/-- The absolute Pfaffian proxy squares to `|det K|` without extra hypotheses. -/

@[rep_depth transport]
theorem pfaffianAbs_sq_eq_abs_det (S : DiracSouriauSector ℝ) :
    S.pfaffianAbs ^ (2 : ℕ) = |S.K.det| := by
  unfold pfaffianAbs
  exact Real.sq_sqrt (abs_nonneg S.K.det)

/--
The Dirac-Souriau entropy expression is a direct readout of the sector
structure: there is no extra witness data hidden behind the definition.
-/
theorem souriauEntropy_eq
    (S : DiracSouriauSector ℝ) :
    S.souriauEntropy =
      Real.log (Real.sqrt S.K.det) - (1 / 2) *
        Real.log (S.berezinian) := by
  rfl

/-- Canonical `ℤ/2`-grading involution `Γ₄ = diag(I₂, -I₂)` on the `4 × 4` Dirac-Souriau carrier. -/
@[rep_depth transport]
def superGamma4 (R : Type*) [CommRing R] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  fromBlocks 1 0 0 (-1)

/-- Off-diagonal supersymmetric intertwiner block `F_S = [[0, B], [C, 0]]` of a `DiracSouriauSector`. -/
@[rep_depth transport]
def oddBlockMatrix (S : DiracSouriauSector R) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  fromBlocks 0 S.B S.C 0

@[rep_depth transport]
theorem superGamma4_sq :
    superGamma4 R * superGamma4 R = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) := by
  dsimp [superGamma4]
  rw [fromBlocks_multiply]
  simp [← fromBlocks_one]

@[rep_depth transport]
theorem oddBlockMatrix_is_superGamma4_odd (S : DiracSouriauSector R) :
    InfoGeometry.Algebra.GradedNullconeAlgebra.parityConj (superGamma4 R) S.oddBlockMatrix =
      -S.oddBlockMatrix := by
  dsimp [InfoGeometry.Algebra.GradedNullconeAlgebra.parityConj, superGamma4, oddBlockMatrix]
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
  simp

/-- Curved `ℤ/2`-graded DG theorem for the `4 × 4` Dirac-Souriau odd block `F_S`:
`∂_{F_S}²(M) = [F_S², M]`, `∂_{F_S}(F_S²) = 0`, and `F_S² = diag(B C, C B)`. -/
@[rep_depth transport]
theorem diracSouriau_curved_dg_sq_and_bianchi (S : DiracSouriauSector R)
    (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    let Γ := superGamma4 R
    let F := S.oddBlockMatrix
    (InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff Γ F (M * N) =
      InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff Γ F M * N +
        InfoGeometry.Algebra.GradedNullconeAlgebra.parityConj Γ M *
          InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff Γ F N) ∧
    (InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff Γ F
        (InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff Γ F M) =
      (F * F) * M - M * (F * F)) ∧
    (InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff Γ F (F * F) = 0) ∧
    (F * F = fromBlocks (S.B * S.C) 0 0 (S.C * S.B)) := by
  dsimp only
  refine ⟨InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff_mul
      (superGamma4_sq (R := R)) S.oddBlockMatrix M N,
    InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff_sq
      (superGamma4_sq (R := R)) S.oddBlockMatrix_is_superGamma4_odd M,
    InfoGeometry.Algebra.GradedNullconeAlgebra.gradedInnerDiff_curvature_closed
      (superGamma4_sq (R := R)) S.oddBlockMatrix_is_superGamma4_odd, ?_⟩
  dsimp [oddBlockMatrix]
  rw [fromBlocks_multiply]
  simp

end DiracSouriauSector

end InfoGeometry.Canonical.DiracSouriau
