import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

/-!
# Projective pure spinors for the concrete split `(5,5)` carrier

The exterior-spinor owner defines purity through the maximal-nullity of the
neutral annihilator.  This file proves the scale-invariance needed to descend
that predicate to real projective spinor space.  No converse pure-spinor
classification or Pin/Spin group action is asserted here.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor

open scoped LinearAlgebra.Projectivization
open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open Module

def IsMaximalNeutralTotallyNull
    (W : Submodule ℝ NeutralSpace) : Prop :=
  InfoGeometry.Clifford.BudinichSpinorsNullVectors.IsTotallyNull
      neutralPairing W ∧
    ∀ T : Submodule ℝ NeutralSpace,
      InfoGeometry.Clifford.BudinichSpinorsNullVectors.IsTotallyNull
          neutralPairing T → W ≤ T → T ≤ W

theorem neutralAnnihilator_smul
    (a : ℝ) (ψ : Spinor) (ha : a ≠ 0) :
    neutralAnnihilator (a • ψ) = neutralAnnihilator ψ := by
  ext w
  rw [mem_neutralAnnihilator_iff, mem_neutralAnnihilator_iff]
  constructor
  · intro h
    have h' : a • neutralAction w ψ = 0 := by
      simpa using h
    exact (smul_eq_zero.mp h').resolve_left ha
  · intro h
    simp [h]

theorem isPureSpinor_smul_iff
    (a : ℝ) (ψ : Spinor) (ha : a ≠ 0) :
    IsPureSpinor (a • ψ) ↔ IsPureSpinor ψ := by
  constructor
  · intro h
    change (a • ψ ≠ 0 ∧ Module.finrank ℝ (neutralAnnihilator (a • ψ)) = 5) at h
    change (ψ ≠ 0 ∧ Module.finrank ℝ (neutralAnnihilator ψ) = 5)
    refine ⟨?_, ?_⟩
    · intro hψ
      apply h.1
      simp [hψ]
    · rw [neutralAnnihilator_smul a ψ ha] at h
      exact h.2
  · intro h
    change (ψ ≠ 0 ∧ Module.finrank ℝ (neutralAnnihilator ψ) = 5) at h
    change (a • ψ ≠ 0 ∧ Module.finrank ℝ (neutralAnnihilator (a • ψ)) = 5)
    refine ⟨?_, ?_⟩
    · intro hzero
      apply h.1
      exact (smul_eq_zero.mp hzero).resolve_left ha
    · rw [neutralAnnihilator_smul a ψ ha]
      exact h.2

private theorem projectivePureSpinor_wellDefined
    (a b : { ψ : Spinor // ψ ≠ 0 }) (t : ℝ)
    (hab : a = t • (b : Spinor)) :
    IsPureSpinor a.1 = IsPureSpinor b.1 := by
  have ht : t ≠ 0 := by
    intro ht
    apply a.property
    rw [hab, ht, zero_smul]
  rw [hab]
  exact propext (isPureSpinor_smul_iff t b.1 ht)

private theorem projectivePureSpinor_annihilator_wellDefined
    (a b : { ψ : Spinor // ψ ≠ 0 }) (t : ℝ)
    (hab : a = t • (b : Spinor)) :
    neutralAnnihilator a.1 = neutralAnnihilator b.1 := by
  have ht : t ≠ 0 := by
    intro ht
    apply a.property
    rw [hab, ht, zero_smul]
  rw [hab, neutralAnnihilator_smul t b.1 ht]

/-- The concrete projective pure-spinor predicate on `ℙ ℝ Spinor`. -/
def ProjectivePureSpinor : Set (ℙ ℝ Spinor) :=
  {p |
    Projectivization.lift
      (fun ψ : { ψ : Spinor // ψ ≠ 0 } => IsPureSpinor ψ.1)
      projectivePureSpinor_wellDefined p}

/-- The annihilator is a well-defined isotropic-plane readout of a projective
pure spinor. -/
def projectivePureSpinorAnnihilator : ℙ ℝ Spinor → Submodule ℝ NeutralSpace :=
  Projectivization.lift
    (fun ψ : { ψ : Spinor // ψ ≠ 0 } => neutralAnnihilator ψ.1)
    projectivePureSpinor_annihilator_wellDefined

@[simp] theorem projectivePureSpinor_mk_iff
    (ψ : Spinor) (hψ : ψ ≠ 0) :
    Projectivization.mk ℝ ψ hψ ∈ ProjectivePureSpinor ↔ IsPureSpinor ψ := by
  rfl

@[simp] theorem projectivePureSpinorAnnihilator_mk
    (ψ : Spinor) (hψ : ψ ≠ 0) :
    projectivePureSpinorAnnihilator
        (Projectivization.mk ℝ ψ hψ) = neutralAnnihilator ψ := by
  rfl

theorem projectivePureSpinorAnnihilator_finrank
    (p : ℙ ℝ Spinor) (hp : p ∈ ProjectivePureSpinor) :
    Module.finrank ℝ (projectivePureSpinorAnnihilator p) = 5 := by
  induction p using Projectivization.ind with
  | h ψ hψ =>
      rw [projectivePureSpinorAnnihilator_mk]
      exact (projectivePureSpinor_mk_iff ψ hψ).mp hp |>.2

theorem projectivePureSpinorAnnihilator_totallyNull
    (p : ℙ ℝ Spinor) (hp : p ∈ ProjectivePureSpinor) :
    InfoGeometry.Clifford.BudinichSpinorsNullVectors.IsTotallyNull
      neutralPairing (projectivePureSpinorAnnihilator p) := by
  induction p using Projectivization.ind with
  | h ψ hψ =>
      rw [projectivePureSpinorAnnihilator_mk]
      have hpure : IsPureSpinor ψ :=
        (projectivePureSpinor_mk_iff ψ hψ).mp hp
      exact neutralAnnihilator_totallyNull hpure.1

theorem pureSpinor_annihilator_orthogonal_eq
    {ψ : Spinor} (hψ : IsPureSpinor ψ) :
    (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin
      (E := V5)).orthogonal (neutralAnnihilator ψ) = neutralAnnihilator ψ := by
  let B := InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin
      (E := V5)
  have hrefl : B.IsRefl := by
    intro x y
    simp [B, InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin_apply,
      add_comm]
  have hnullB : InfoGeometry.Clifford.BudinichSpinorsNullVectors.IsTotallyNull
      (fun x y => B x y) (neutralAnnihilator ψ) := by
    intro x hx y hy
    have h := neutralAnnihilator_totallyNull hψ.1 x hx y hy
    simpa [B, InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin_apply,
      neutralPairing] using congrArg (fun z : ℝ => 2 * z) h
  have hle : neutralAnnihilator ψ ≤ B.orthogonal (neutralAnnihilator ψ) := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hnullB y hy x hx
  have horth : Module.finrank ℝ (B.orthogonal (neutralAnnihilator ψ)) = 5 := by
    have h := LinearMap.BilinForm.finrank_orthogonal
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin_nondegenerate hrefl (neutralAnnihilator ψ)
    rw [neutralSpace_finrank, hψ.2] at h
    norm_num at h ⊢
    exact h
  symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hψ.2, horth]

theorem pureSpinor_annihilator_isMaximalNeutralTotallyNull
    {ψ : Spinor} (hψ : IsPureSpinor ψ) :
    IsMaximalNeutralTotallyNull (neutralAnnihilator ψ) := by
  let B := InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin
      (E := V5)
  refine ⟨neutralAnnihilator_totallyNull hψ.1, ?_⟩
  intro T hT hsub x hx
  have hxorth : x ∈ B.orthogonal (neutralAnnihilator ψ) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    simpa [LinearMap.BilinForm.IsOrtho, B,
      InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralBilin_apply,
      neutralPairing] using hT y (hsub hy) x hx
  rw [pureSpinor_annihilator_orthogonal_eq hψ] at hxorth
  exact hxorth

theorem projectivePureSpinorAnnihilator_isMaximalNeutralTotallyNull
    (p : ℙ ℝ Spinor) (hp : p ∈ ProjectivePureSpinor) :
    IsMaximalNeutralTotallyNull
      (projectivePureSpinorAnnihilator p) := by
  induction p using Projectivization.ind with
  | h ψ hψ =>
      rw [projectivePureSpinorAnnihilator_mk]
      exact pureSpinor_annihilator_isMaximalNeutralTotallyNull
        ((projectivePureSpinor_mk_iff ψ hψ).mp hp)

theorem vacuum_neutralAnnihilator_isMaximalNeutralTotallyNull :
    IsMaximalNeutralTotallyNull (neutralAnnihilator (1 : Spinor)) :=
  pureSpinor_annihilator_isMaximalNeutralTotallyNull vacuum_isPureSpinor

theorem projective_vacuum_isPureSpinor :
    Projectivization.mk ℝ (1 : Spinor) one_ne_zero ∈ ProjectivePureSpinor := by
  exact projectivePureSpinor_mk_iff (1 : Spinor) one_ne_zero |>.2 vacuum_isPureSpinor

end InfoGeometry.Clifford.SplitClifford55ProjectivePureSpinor
