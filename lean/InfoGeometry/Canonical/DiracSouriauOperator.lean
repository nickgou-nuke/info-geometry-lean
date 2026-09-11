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
    simpa [M, D, Matrix.toLin'_toMatrix', Matrix.toLin'_mul] using hd.1
  · constructor
    · apply Matrix.toLin'.injective
      simpa [M, D, Matrix.toLin'_toMatrix', Matrix.toLin'_mul] using hd.2.1
    · apply Matrix.toLin'.injective
      -- Adjust for composition order: (f^(k+1)) ∘ₗ d = f^k
      have h3 := hd.2.2
      simpa [M, D, Matrix.toLin'_toMatrix', Matrix.toLin'_mul, Matrix.toLin'_pow] using h3

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

/--
Scalar Pfaffian proxy for the topological sector `K`.
Under the explicit hypothesis `0 ≤ det K`, it satisfies `pfaffian² = det K`.
-/

@[rep_depth transport]
noncomputable def pfaffian (S : DiracSouriauSector ℝ) : ℝ :=
  Real.sqrt S.K.det

/-- The Pfaffian proxy squares to `det K` when the determinant is nonnegative. -/

@[rep_depth transport]
theorem pfaffian_sq_eq_det_of_det_nonneg
    (S : DiracSouriauSector ℝ) (hdet : 0 ≤ S.K.det) :
    S.pfaffian ^ (2 : ℕ) = S.K.det := by
  unfold pfaffian
  exact Real.sq_sqrt hdet

/--
Formal Pfaffian-Berezinian entropy expression.
The macro-entropy S of the universe is governed by the exact duality between
topological complexity (Pfaffian) and statistical dissipation (Berezinian).
-/

@[rep_depth transport]
noncomputable def souriauEntropy (S : DiracSouriauSector ℝ) : ℝ :=
  Real.log (S.pfaffian) - (1 / 2) * Real.log (S.berezinian)

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

end DiracSouriauSector

end InfoGeometry.Canonical.DiracSouriau
