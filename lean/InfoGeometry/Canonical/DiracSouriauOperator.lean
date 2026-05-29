import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Pi
import InfoGeometry.Meta.Architecture
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinExistenceBridge
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Volume.Pfaffian

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
    InfoGeometry.Canonical.DrazinExistenceBridge.exists_canonicalDrazinInverse_global f
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
Context carrying the explicit Drazin witness for one concrete Dirac-Souriau
sector.  This is intentionally a context object, not a generalized closure
claim about all block matrices.
-/

structure DrazinWitnessContext (S : DiracSouriauSector R) where
  k : ℕ
  D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R
  isDrazin : InfoGeometry.Canonical.Drazin.IsDrazinInverse S.toMatrix D k

/--
Construct the local Drazin witness context from explicit owned Drazin data.

Field-level finite-dimensional existence remains available as an existential
theorem; a structure-valued context must be supplied with the actual witness it
stores.
-/
def DrazinWitnessContext.ofExplicit
    (S : DiracSouriauSector R)
    (k : ℕ)
    (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (hD : InfoGeometry.Canonical.Drazin.IsDrazinInverse S.toMatrix D k) :
    DrazinWitnessContext S :=
  ⟨k, D, hD⟩

/-- A Drazin witness context discharges the local hypothesis predicate. -/

theorem hasDrazinInverse_of_context
    {S : DiracSouriauSector R} (Ctxt : DrazinWitnessContext S) :
    S.HasDrazinInverse Ctxt.k := by
  exact ⟨Ctxt.D, Ctxt.isDrazin⟩

/--
Field-level existence can be presented as an explicit context existential.

This stays in `Prop`, so unpacking the field-level existence theorem does not
manufacture a data object by hidden choice.
-/
theorem exists_drazinWitnessContext_of_field
    {K : Type*} [Field K] (S : DiracSouriauSector K) :
    ∃ Ctxt : DrazinWitnessContext S, S.HasDrazinInverse Ctxt.k := by
  rcases S.exists_drazinInverse with ⟨k, D, hD⟩
  exact ⟨DrazinWitnessContext.ofExplicit S k D hD, D, hD⟩

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

def drazinWitnessContext_zero_of_twoSidedInverse
    (S : DiracSouriauSector R)
    (D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (hSD : S.toMatrix * D = 1)
    (hDS : D * S.toMatrix = 1) :
    DrazinWitnessContext S := by
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
  exact ⟨D, (drazinWitnessContext_zero_of_twoSidedInverse S D hSD hDS).isDrazin⟩

/--
Constructive Drazin witness from an explicit unit for the full assembled `4×4`
block operator.
-/
def drazinWitnessContext_zero_of_unit_toMatrix
    (S : DiracSouriauSector R)
    (u : (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)ˣ)
    (hu : (u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) = S.toMatrix) :
    DrazinWitnessContext S := by
  refine drazinWitnessContext_zero_of_twoSidedInverse S (↑u⁻¹) ?_ ?_
  · rw [← hu]
    exact Units.mul_inv u
  · rw [← hu]
    exact Units.inv_mul u

/--
A unit witness for the assembled block operator discharges the local Drazin
predicate at index `0`, without separately passing the inverse matrix or the two
inverse-law hypotheses.
-/
theorem hasDrazinInverse_zero_of_isUnit_toMatrix
    (S : DiracSouriauSector R)
    (hUnit : IsUnit S.toMatrix) :
    S.HasDrazinInverse 0 := by
  rcases hUnit with ⟨u, hu⟩
  exact ⟨(↑u⁻¹),
    (drazinWitnessContext_zero_of_unit_toMatrix S u hu).isDrazin⟩

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
Constructive Gram-factor witness for the topological block.  A sector with
`K = PᵀP` has nonnegative determinant by the native determinant-square route,
so callers do not need to provide the bare hypothesis `0 ≤ det K`.
-/
@[rep_depth transport]
structure TopologicalGramWitness (S : DiracSouriauSector ℝ) where
  /-- Explicit Gram factor for the topological block. -/
  P : Matrix (Fin 2) (Fin 2) ℝ
  /-- The topological block is the Gram square of `P`. -/
  K_eq_gram : S.K = P.transpose * P

/-- A Gram-factor witness constructively discharges determinant nonnegativity. -/
@[rep_depth transport]
theorem det_nonneg_of_topologicalGramWitness
    {S : DiracSouriauSector ℝ} (W : TopologicalGramWitness S) :
    0 ≤ S.K.det := by
  rw [W.K_eq_gram, Matrix.det_mul, Matrix.det_transpose]
  simpa [pow_two] using sq_nonneg W.P.det

/--
The Pfaffian proxy squares to `det K` on the Gram-factor branch, with no bare
`0 ≤ det K` hypothesis at the call site.
-/
@[rep_depth transport]
theorem pfaffian_sq_eq_det_of_topologicalGramWitness
    {S : DiracSouriauSector ℝ} (W : TopologicalGramWitness S) :
    S.pfaffian ^ (2 : ℕ) = S.K.det := by
  exact pfaffian_sq_eq_det_of_det_nonneg S
    (det_nonneg_of_topologicalGramWitness W)

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

/-- Constructive witness for BPS protection of a Dirac-Souriau sector. -/
@[rep_depth transport]
structure BPSPProtectedWitness (S : DiracSouriauSector ℝ) where
  /-- The critical stiffness threshold parameter. -/
  κ_crit : ℝ
  /-- Proof that the Berezinian is below the critical threshold. -/
  hBelow : S.berezinian < κ_crit

/-- BPS protection means the sector has an explicit stiffness witness. -/
@[rep_depth transport]
def IsBPSProtected (S : DiracSouriauSector ℝ) (κ_crit : ℝ) : Prop :=
  ∃ (w : BPSPProtectedWitness S), w.κ_crit = κ_crit

/-- The original `IsBPSProtected` predicate is equivalent to the existence of a witness. -/
@[rep_depth transport]
theorem IsBPSProtected_iff_exists_witness (S : DiracSouriauSector ℝ) (κ_crit : ℝ) :
    IsBPSProtected S κ_crit ↔ S.berezinian < κ_crit := by
  constructor
  · rintro ⟨w, rfl⟩
    exact w.hBelow
  · intro h
    refine ⟨⟨κ_crit, h⟩, rfl⟩

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
