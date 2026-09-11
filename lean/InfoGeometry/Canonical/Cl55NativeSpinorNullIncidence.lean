import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55SpinorAlgebraEquiv
import InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry

/-!
# Native `Cl(5,5)` spinor null-incidence

This owner uses the existing native algebra equivalence
`Cl55 ≃ₐ[ℝ] SpinorMatrix 5`.  It proves only the finite square identity for
the vector action and its immediate annihilator consequence.  It does not
identify this matrix spinor model with the generic Chevalley exterior-spinor
model, and it does not assert maximality or a pure-spinor classification.
-/

noncomputable section
set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl55NativeSpinorNullIncidence

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.Cl55NeutralHyperbolicIsometry

open InfoGeometry.Clifford.BudinichSpinorsNullVectors

local notation "NativeV55" => InfoGeometry.Clifford.Clifford55.V55

abbrev NativeSpinor55 := SpinorSpace 5

def nativeSpinorAction55 (v : NativeV55) : SpinorMatrix 5 :=
  cl55SpinorAlgEquiv (ι55 v)

def nativeSpinorAnnihilator55 (ψ : NativeSpinor55) : Set NativeV55 :=
  {v | Matrix.mulVec (nativeSpinorAction55 v) ψ = 0}

private theorem algebraMap_scalar_mulVec (r : ℝ) (ψ : NativeSpinor55) :
    Matrix.mulVec (algebraMap ℝ (SpinorMatrix 5) r) ψ = r • ψ := by
  ext i
  simp [Matrix.mulVec, Matrix.algebraMap_matrix_apply, dotProduct]

def nativeSpinorAnnihilatorMap55 (ψ : NativeSpinor55) :
    NativeV55 →ₗ[ℝ] NativeSpinor55 where
  toFun := fun v => Matrix.mulVec (nativeSpinorAction55 v) ψ
  map_add' := by
    intro v w
    simp [nativeSpinorAction55, Matrix.add_mulVec]
  map_smul' := by
    intro a v
    simp [nativeSpinorAction55, Matrix.smul_mulVec]

theorem nativeSpinorAnnihilator55_eq_kernel (ψ : NativeSpinor55) :
    nativeSpinorAnnihilator55 ψ =
      (nativeSpinorAnnihilatorMap55 ψ).ker := by
  rfl

def nativeSpinorActionOperator55 :
    NativeV55 →ₗ[ℝ] NativeSpinor55 →ₗ[ℝ] NativeSpinor55 where
  toFun := fun v =>
    { toFun := fun ψ => Matrix.mulVec (nativeSpinorAction55 v) ψ
      map_add' := by
        intro ψ φ
        exact Matrix.mulVec_add _ _ _
      map_smul' := by
        intro a ψ
        exact Matrix.mulVec_smul _ _ _ }
  map_add' := by
    intro v w
    ext ψ
    simp [nativeSpinorAction55, Matrix.mulVec_add]
  map_smul' := by
    intro a v
    ext ψ
    simp [nativeSpinorAction55, Matrix.mulVec_smul]

theorem nativeSpinorActionOperator55_anticomm (v w : NativeV55)
    (ψ : NativeSpinor55) :
    nativeSpinorActionOperator55 v
          (nativeSpinorActionOperator55 w ψ) +
        nativeSpinorActionOperator55 w
          (nativeSpinorActionOperator55 v ψ) =
      (QuadraticMap.polar Q55 v w) • ψ := by
  change Matrix.mulVec (nativeSpinorAction55 v)
      (Matrix.mulVec (nativeSpinorAction55 w) ψ) +
      Matrix.mulVec (nativeSpinorAction55 w)
        (Matrix.mulVec (nativeSpinorAction55 v) ψ) = _
  have hanti : nativeSpinorAction55 v * nativeSpinorAction55 w +
        nativeSpinorAction55 w * nativeSpinorAction55 v =
      algebraMap ℝ (SpinorMatrix 5) (QuadraticMap.polar Q55 v w) := by
    unfold nativeSpinorAction55
    have h := CliffordAlgebra.ι_mul_ι_add_swap
      (Q := Q55) v w
    have hm := congrArg cl55SpinorAlgEquiv h
    rw [map_add, map_mul, map_mul] at hm
    simpa using hm
  calc
    Matrix.mulVec (nativeSpinorAction55 v)
        (Matrix.mulVec (nativeSpinorAction55 w) ψ) +
        Matrix.mulVec (nativeSpinorAction55 w)
          (Matrix.mulVec (nativeSpinorAction55 v) ψ) =
      Matrix.mulVec (nativeSpinorAction55 v * nativeSpinorAction55 w)
          ψ + Matrix.mulVec (nativeSpinorAction55 w * nativeSpinorAction55 v) ψ := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = Matrix.mulVec
        (nativeSpinorAction55 v * nativeSpinorAction55 w +
          nativeSpinorAction55 w * nativeSpinorAction55 v) ψ := by
            rw [Matrix.add_mulVec]
    _ = Matrix.mulVec
        (algebraMap ℝ (SpinorMatrix 5) (QuadraticMap.polar Q55 v w)) ψ := by
            rw [hanti]
    _ = (QuadraticMap.polar Q55 v w) • ψ :=
      algebraMap_scalar_mulVec _ _

theorem nativeSpinorActionOperator55_satisfies_realCliffordRelation :
    SatisfiesRealCliffordRelation
      (fun v w : NativeV55 => (QuadraticMap.polar Q55 v w) / 2)
      nativeSpinorActionOperator55 := by
  intro v w ψ
  rw [nativeSpinorActionOperator55_anticomm]
  congr 1
  ring

theorem nativeSpinorAnnihilator55_eq_generic_annihilator
    (ψ : NativeSpinor55) :
    nativeSpinorAnnihilator55 ψ =
    (spinorAnnihilator nativeSpinorActionOperator55 ψ : Set NativeV55) := by
  rfl

theorem nativeSpinorAnnihilator55_totallyNull
    {ψ : NativeSpinor55} (hψ : ψ ≠ 0) :
    IsTotallyNull
      (fun v w : NativeV55 => (QuadraticMap.polar Q55 v w) / 2)
      (spinorAnnihilator nativeSpinorActionOperator55 ψ) := by
  exact annihilator_totallyNull_of_realClifford
    nativeSpinorActionOperator55_satisfies_realCliffordRelation hψ

theorem nativeSpinorAction55_eq_representation (v : NativeV55) :
    nativeSpinorAction55 v =
      cl55SpinorRepresentation (ι55 v) := by
  have h := congrArg
      (fun F : Cl55 →ₐ[ℝ] SpinorMatrix 5 => F (ι55 v))
      cl55SpinorAlgEquiv_toAlgHom_eq_representation
  simpa [nativeSpinorAction55] using h

theorem nativeSpinorAction55_neutral_readback (x : NeutralSpace) :
    nativeSpinorAction55 (neutralToV55 x) =
      neutralCliffordMatrixRep
          (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V5)) x) := by
  rw [nativeSpinorAction55_eq_representation]
  exact (neutralCliffordMatrixRep_ι x).symm

theorem nativeSpinorAction55_sq (v : NativeV55) :
    nativeSpinorAction55 v * nativeSpinorAction55 v =
      algebraMap ℝ (SpinorMatrix 5) (Q55 v) := by
  unfold nativeSpinorAction55
  rw [← map_mul, CliffordAlgebra.ι_sq_scalar]
  exact cl55SpinorAlgEquiv.commutes (Q55 v)

theorem nativeSpinorAction55_mulVec_sq (v : NativeV55) (ψ : NativeSpinor55) :
    Matrix.mulVec (nativeSpinorAction55 v)
        (Matrix.mulVec (nativeSpinorAction55 v) ψ) =
      (Q55 v) • ψ := by
  calc
    Matrix.mulVec (nativeSpinorAction55 v)
        (Matrix.mulVec (nativeSpinorAction55 v) ψ) =
      Matrix.mulVec (nativeSpinorAction55 v * nativeSpinorAction55 v) ψ := by
        exact Matrix.mulVec_mulVec ψ (nativeSpinorAction55 v)
          (nativeSpinorAction55 v)
    _ = Matrix.mulVec (algebraMap ℝ (SpinorMatrix 5) (Q55 v)) ψ := by
      rw [nativeSpinorAction55_sq]
    _ = (Q55 v) • ψ := algebraMap_scalar_mulVec (Q55 v) ψ

theorem nativeSpinorAction55_anticomm (v w : NativeV55) :
    nativeSpinorAction55 v * nativeSpinorAction55 w +
        nativeSpinorAction55 w * nativeSpinorAction55 v =
      algebraMap ℝ (SpinorMatrix 5)
        (QuadraticMap.polar Q55 v w) := by
  unfold nativeSpinorAction55
  have h := CliffordAlgebra.ι_mul_ι_add_swap
    (Q := Q55) v w
  have hm := congrArg cl55SpinorAlgEquiv h
  rw [map_add, map_mul, map_mul] at hm
  simpa using hm

theorem nativeSpinorAnnihilator_isotropic
    {ψ : NativeSpinor55} {v w : NativeV55}
    (hv : v ∈ nativeSpinorAnnihilator55 ψ)
    (hw : w ∈ nativeSpinorAnnihilator55 ψ)
    (hψ : ψ ≠ 0) :
    QuadraticMap.polar Q55 v w = 0 := by
  have hanti := nativeSpinorAction55_anticomm v w
  have hzero := congrArg (fun M => Matrix.mulVec M ψ) hanti
  change Matrix.mulVec (nativeSpinorAction55 v * nativeSpinorAction55 w +
        nativeSpinorAction55 w * nativeSpinorAction55 v) ψ =
      Matrix.mulVec (algebraMap ℝ (SpinorMatrix 5)
        (QuadraticMap.polar Q55 v w)) ψ at hzero
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hv, hw] at hzero
  simp only [Matrix.mulVec_zero, add_zero] at hzero
  rw [algebraMap_scalar_mulVec] at hzero
  exact (smul_eq_zero.mp hzero.symm).resolve_right hψ

theorem null_of_nativeSpinorAnnihilator
    {ψ : NativeSpinor55} (hψ : ψ ≠ 0)
    {v : NativeV55} (hv : v ∈ nativeSpinorAnnihilator55 ψ) :
    Q55 v = 0 := by
  have hzero := nativeSpinorAction55_mulVec_sq v ψ
  rw [show Matrix.mulVec (nativeSpinorAction55 v)
      (Matrix.mulVec (nativeSpinorAction55 v) ψ) = 0 by
        rw [hv]
        simp] at hzero
  exact (smul_eq_zero.mp hzero.symm).resolve_right hψ

theorem nativeSpinorAnnihilator_subset_nullCone
    {ψ : NativeSpinor55} (hψ : ψ ≠ 0) :
    nativeSpinorAnnihilator55 ψ ⊆ {v : NativeV55 | Q55 v = 0} := by
  intro v hv
  exact null_of_nativeSpinorAnnihilator hψ hv

end InfoGeometry.Canonical.Cl55NativeSpinorNullIncidence
