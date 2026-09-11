import Mathlib.Data.Real.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import InfoGeometry.Clifford.BudinichSpinorsNullVectors
import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# Exterior-algebra spinor operators for the split neutral carrier

The spinor carrier here is the exterior algebra on a five-dimensional real
space.  Wedge and contraction are the native creation and annihilation
operators; their square-zero and CAR identities are inherited from Mathlib's
exterior/Clifford API.  No matrix realization is used.
-/

noncomputable section

namespace InfoGeometry.Clifford.SplitClifford55ExteriorSpinor

abbrev V5 := InfoGeometry.Algebra.FiniteSpin.Vec5R
abbrev Spinor := ExteriorAlgebra ℝ V5
abbrev SpinorEnd := Module.End ℝ Spinor

def basisVector (i : Fin 5) : V5 := Pi.single i 1

def dualBasisVector (i : Fin 5) : Module.Dual ℝ V5 := LinearMap.proj i

@[simp] theorem dualBasisVector_apply (i j : Fin 5) :
    dualBasisVector i (basisVector j) = if i = j then 1 else 0 := by
  simp [dualBasisVector, basisVector, Pi.single_apply]

def wedge (v : V5) : SpinorEnd :=
  Algebra.lmul ℝ Spinor (ExteriorAlgebra.ι ℝ v)

def contract (φ : Module.Dual ℝ V5) : SpinorEnd :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V5)) φ

abbrev NeutralSpace := V5 × Module.Dual ℝ V5

@[simp] theorem wedge_apply (v : V5) (ψ : Spinor) :
    wedge v ψ = ExteriorAlgebra.ι ℝ v * ψ := rfl

@[simp] theorem contract_wedge (φ : Module.Dual ℝ V5) (v : V5) (ψ : Spinor) :
    contract φ (wedge v ψ) = φ v • ψ - wedge v (contract φ ψ) := by
  exact CliffordAlgebra.contractLeft_ι_mul
    (Q := (0 : QuadraticForm ℝ V5)) φ v ψ

@[simp] theorem wedge_sq (v : V5) : wedge v * wedge v = 0 := by
  ext ψ
  change ExteriorAlgebra.ι ℝ v * (ExteriorAlgebra.ι ℝ v * ψ) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

@[simp] theorem contract_sq (φ : Module.Dual ℝ V5) :
    contract φ * contract φ = 0 := by
  ext ψ
  exact CliffordAlgebra.contractLeft_contractLeft
    (Q := (0 : QuadraticForm ℝ V5)) φ ψ

theorem contract_wedge_add_wedge_contract
    (φ : Module.Dual ℝ V5) (v : V5) :
    contract φ * wedge v + wedge v * contract φ =
      (φ v) • (1 : SpinorEnd) := by
  ext ψ
  simp only [LinearMap.add_apply, Module.End.mul_apply, wedge_apply]
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V5)) φ
      (ExteriorAlgebra.ι ℝ v * ψ) +
      ExteriorAlgebra.ι ℝ v * contract φ ψ =
        (φ v • (1 : SpinorEnd)) ψ
  rw [CliffordAlgebra.contractLeft_ι_mul]
  simp only [contract]
  abel

theorem wedge_add_swap (v u : V5) :
    wedge v * wedge u + wedge u * wedge v = 0 := by
  ext ψ
  change ExteriorAlgebra.ι ℝ v * (ExteriorAlgebra.ι ℝ u * ψ) +
      ExteriorAlgebra.ι ℝ u * (ExteriorAlgebra.ι ℝ v * ψ) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap,
    zero_mul]

theorem contract_add_swap (φ ψ : Module.Dual ℝ V5) :
    contract φ * contract ψ + contract ψ * contract φ = 0 := by
  ext ξ
  change CliffordAlgebra.contractLeft φ (CliffordAlgebra.contractLeft ψ ξ) +
      CliffordAlgebra.contractLeft ψ (CliffordAlgebra.contractLeft φ ξ) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  simp

def neutralAction (w : V5 × Module.Dual ℝ V5) : SpinorEnd :=
  wedge w.1 + contract w.2

def gammaPlus (i : Fin 5) : SpinorEnd :=
  neutralAction (basisVector i, dualBasisVector i)

def gammaMinus (i : Fin 5) : SpinorEnd :=
  neutralAction (basisVector i, -dualBasisVector i)

theorem neutralAction_sq (w : V5 × Module.Dual ℝ V5) :
    neutralAction w * neutralAction w =
      (w.2 w.1) • (1 : SpinorEnd) := by
  simp only [neutralAction, add_mul, mul_add, wedge_sq, contract_sq,
    zero_add, add_zero]
  exact contract_wedge_add_wedge_contract w.2 w.1

def neutralPairing (w z : V5 × Module.Dual ℝ V5) : ℝ :=
  (w.2 z.1 + z.2 w.1) / 2

noncomputable def neutralActionMap : NeutralSpace →ₗ[ℝ] SpinorEnd where
  toFun w := neutralAction w
  map_add' w z := by
    rcases w with ⟨v, φ⟩
    rcases z with ⟨u, ψ⟩
    ext ξ
    change (ExteriorAlgebra.ι ℝ (v + u) * ξ +
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V5)) (φ + ψ) ξ) =
      (ExteriorAlgebra.ι ℝ v * ξ +
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V5)) φ ξ) +
        (ExteriorAlgebra.ι ℝ u * ξ +
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V5)) ψ ξ)
    rw [map_add, map_add]
    simp only [add_mul, LinearMap.add_apply]
    abel
  map_smul' a w := by
    rcases w with ⟨v, φ⟩
    ext ξ
    change (ExteriorAlgebra.ι ℝ (a • v) * ξ +
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V5)) (a • φ) ξ) =
      a • (ExteriorAlgebra.ι ℝ v * ξ +
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ V5)) φ ξ)
    rw [map_smul, map_smul]
    simp only [smul_mul_assoc, smul_add, LinearMap.smul_apply]

theorem neutralAction_anticommutator (w z : V5 × Module.Dual ℝ V5) :
    neutralAction w * neutralAction z + neutralAction z * neutralAction w =
      (2 * neutralPairing w z) • (1 : SpinorEnd) := by
  rcases w with ⟨v, φ⟩
  rcases z with ⟨u, ψ⟩
  calc
    neutralAction (v, φ) * neutralAction (u, ψ) +
          neutralAction (u, ψ) * neutralAction (v, φ) =
        (wedge v * wedge u + wedge u * wedge v) +
          (contract φ * wedge u + wedge u * contract φ) +
          (contract ψ * wedge v + wedge v * contract ψ) +
          (contract φ * contract ψ + contract ψ * contract φ) := by
            simp only [neutralAction, add_mul, mul_add]
            abel
    _ = (2 * neutralPairing (v, φ) (u, ψ)) • (1 : SpinorEnd) := by
      rw [wedge_add_swap, contract_add_swap,
        contract_wedge_add_wedge_contract φ u]
      have hcross := contract_wedge_add_wedge_contract ψ v
      rw [hcross]
      simp only [neutralPairing, zero_add, add_zero]
      rw [← add_smul]
      congr 1
      ring_nf

theorem neutralAction_basisVector_sq (i : Fin 5) :
    neutralAction (basisVector i, dualBasisVector i) *
        neutralAction (basisVector i, dualBasisVector i) =
      (1 : ℝ) • (1 : SpinorEnd) := by
  simpa [dualBasisVector_apply] using
    neutralAction_sq (basisVector i, dualBasisVector i)

theorem neutralAction_basisVector_opposite_sq (i : Fin 5) :
    neutralAction (basisVector i, -dualBasisVector i) *
        neutralAction (basisVector i, -dualBasisVector i) =
      (-1 : ℝ) • (1 : SpinorEnd) := by
  simpa [dualBasisVector_apply] using
    neutralAction_sq (basisVector i, -dualBasisVector i)

@[simp] theorem gammaPlus_sq (i : Fin 5) :
    gammaPlus i * gammaPlus i = (1 : ℝ) • (1 : SpinorEnd) := by
  exact neutralAction_basisVector_sq i

@[simp] theorem gammaMinus_sq (i : Fin 5) :
    gammaMinus i * gammaMinus i = (-1 : ℝ) • (1 : SpinorEnd) := by
  exact neutralAction_basisVector_opposite_sq i

theorem gammaPlus_anticommutator (i j : Fin 5) :
    gammaPlus i * gammaPlus j + gammaPlus j * gammaPlus i =
      (if i = j then (2 : ℝ) else 0) • (1 : SpinorEnd) := by
  simpa [gammaPlus, neutralPairing, dualBasisVector_apply, eq_comm] using
    neutralAction_anticommutator
      (basisVector i, dualBasisVector i)
      (basisVector j, dualBasisVector j)

theorem gammaMinus_anticommutator (i j : Fin 5) :
    gammaMinus i * gammaMinus j + gammaMinus j * gammaMinus i =
      (if i = j then (-2 : ℝ) else 0) • (1 : SpinorEnd) := by
  by_cases h : i = j
  · subst j
    simpa [gammaMinus, neutralPairing, dualBasisVector_apply] using
      neutralAction_anticommutator
        (basisVector i, -dualBasisVector i)
        (basisVector i, -dualBasisVector i)
  · simpa [gammaMinus, neutralPairing, dualBasisVector_apply, h, Ne.symm h]
      using neutralAction_anticommutator
        (basisVector i, -dualBasisVector i)
        (basisVector j, -dualBasisVector j)

theorem gammaPlus_gammaMinus_anticommutator (i j : Fin 5) :
    gammaPlus i * gammaMinus j + gammaMinus j * gammaPlus i = 0 := by
  simpa [gammaPlus, gammaMinus, neutralPairing, dualBasisVector_apply, eq_comm]
    using neutralAction_anticommutator
      (basisVector i, dualBasisVector i)
      (basisVector j, -dualBasisVector j)

/-! ## Pure-spinor annihilator interface -/

noncomputable def neutralEvaluation (ψ : Spinor) : NeutralSpace →ₗ[ℝ] Spinor :=
  ((LinearMap.applyₗ (R := ℝ) (M := Spinor) (M₂ := Spinor)) ψ).comp
    neutralActionMap

noncomputable def neutralAnnihilator (ψ : Spinor) : Submodule ℝ NeutralSpace :=
  InfoGeometry.Clifford.BudinichSpinorsNullVectors.spinorAnnihilator
    neutralActionMap ψ

@[simp] theorem mem_neutralAnnihilator_iff (ψ : Spinor) (w : NeutralSpace) :
    w ∈ neutralAnnihilator ψ ↔ neutralAction w ψ = 0 := by
  change neutralAction w ψ = 0 ↔ neutralAction w ψ = 0
  rfl

def IsPureSpinor (ψ : Spinor) : Prop :=
  ψ ≠ 0 ∧ Module.finrank ℝ (neutralAnnihilator ψ) = 5

theorem neutralAnnihilator_zero_mem (w : NeutralSpace) :
    w ∈ neutralAnnihilator 0 := by
  rw [mem_neutralAnnihilator_iff]
  simp

theorem dual_mem_vacuum_neutralAnnihilator
    (φ : Module.Dual ℝ V5) :
    (0, φ) ∈ neutralAnnihilator (1 : Spinor) := by
  rw [mem_neutralAnnihilator_iff]
  simp [neutralAction, contract]

def dualVacuumEmbedding : Module.Dual ℝ V5 →ₗ[ℝ] NeutralSpace where
  toFun φ := (0, φ)
  map_add' φ ψ := by simp
  map_smul' c φ := by simp

theorem dualVacuumEmbedding_injective :
    Function.Injective dualVacuumEmbedding := by
  intro φ ψ h
  exact congrArg Prod.snd h

theorem dualVacuumEmbedding_range_le :
    LinearMap.range dualVacuumEmbedding ≤ neutralAnnihilator (1 : Spinor) := by
  rintro _ ⟨φ, rfl⟩
  exact dual_mem_vacuum_neutralAnnihilator φ

theorem dualVacuumEmbedding_range_finrank :
    Module.finrank ℝ (LinearMap.range dualVacuumEmbedding) = 5 := by
  rw [LinearMap.finrank_range_of_inj dualVacuumEmbedding_injective,
    Subspace.dual_finrank_eq]
  simp [V5]

theorem vacuum_neutralAnnihilator_finrank_ge_five :
    5 ≤ Module.finrank ℝ (neutralAnnihilator (1 : Spinor)) := by
  calc
    5 = Module.finrank ℝ (LinearMap.range dualVacuumEmbedding) :=
      dualVacuumEmbedding_range_finrank.symm
    _ ≤ Module.finrank ℝ (neutralAnnihilator (1 : Spinor)) :=
      Submodule.finrank_mono dualVacuumEmbedding_range_le

theorem vacuum_neutralAnnihilator_eq_dualVacuumEmbedding_range :
    neutralAnnihilator (1 : Spinor) = LinearMap.range dualVacuumEmbedding := by
  ext w
  rcases w with ⟨v, φ⟩
  constructor
  · intro hw
    rw [mem_neutralAnnihilator_iff] at hw
    have hv : ExteriorAlgebra.ι ℝ v = 0 := by
      simpa [neutralAction, contract] using hw
    have hv0 : v = 0 := (ExteriorAlgebra.ι_eq_zero_iff v).mp hv
    subst v
    exact ⟨φ, rfl⟩
  · rintro ⟨ψ, hψ⟩
    have hv : v = 0 := by
      symm
      simpa [dualVacuumEmbedding] using congrArg Prod.fst hψ
    subst v
    exact dual_mem_vacuum_neutralAnnihilator φ

theorem vacuum_neutralAnnihilator_finrank :
    Module.finrank ℝ (neutralAnnihilator (1 : Spinor)) = 5 := by
  rw [vacuum_neutralAnnihilator_eq_dualVacuumEmbedding_range]
  exact dualVacuumEmbedding_range_finrank

theorem vacuum_isPureSpinor : IsPureSpinor (1 : Spinor) := by
  exact ⟨one_ne_zero, vacuum_neutralAnnihilator_finrank⟩

theorem neutralAction_satisfiesRealCliffordRelation :
    InfoGeometry.Clifford.BudinichSpinorsNullVectors.SatisfiesRealCliffordRelation
      neutralPairing neutralActionMap := by
  intro w z ψ
  have h := neutralAction_anticommutator w z
  simpa [Module.End.mul_apply] using congrArg (fun T : SpinorEnd => T ψ) h

/-! ## The universal Clifford representation -/

noncomputable def neutralCliffordRep :
    CliffordAlgebra
        (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
          (E := V5)) →ₐ[ℝ] SpinorEnd :=
  CliffordAlgebra.lift _
    ⟨neutralActionMap, by
      intro w
      simpa [InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_apply]
        using neutralAction_sq w⟩

@[simp] theorem neutralCliffordRep_ι (w : NeutralSpace) :
    neutralCliffordRep
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V5)) w) =
      neutralAction w := by
  exact CliffordAlgebra.lift_ι_apply _ _ w

theorem neutralCliffordRep_ι_sq (w : NeutralSpace) :
    neutralCliffordRep
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V5)) w) *
        neutralCliffordRep
        (CliffordAlgebra.ι
          (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
            (E := V5)) w) =
      (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled w) •
        (1 : SpinorEnd) := by
  simpa only [neutralCliffordRep_ι,
    InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled_apply]
    using neutralAction_sq w

theorem neutralCliffordRep_ι_anticommutator (w z : NeutralSpace) :
    neutralCliffordRep
          (CliffordAlgebra.ι
            (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
              (E := V5)) w) *
        neutralCliffordRep
          (CliffordAlgebra.ι
            (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
              (E := V5)) z) +
      neutralCliffordRep
          (CliffordAlgebra.ι
            (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
              (E := V5)) z) *
        neutralCliffordRep
          (CliffordAlgebra.ι
            (InfoGeometry.Clifford.NeutralPhaseSpaceCore.canonicalNeutralFormUnscaled
              (E := V5)) w) =
      (2 * neutralPairing w z) • (1 : SpinorEnd) := by
  simpa only [neutralCliffordRep_ι] using neutralAction_anticommutator w z

theorem neutralAnnihilator_totallyNull {ψ : Spinor} (hψ : ψ ≠ 0) :
    InfoGeometry.Clifford.BudinichSpinorsNullVectors.IsTotallyNull
      neutralPairing (neutralAnnihilator ψ) := by
  exact
    InfoGeometry.Clifford.BudinichSpinorsNullVectors.annihilator_totallyNull_of_realClifford
      neutralAction_satisfiesRealCliffordRelation hψ

theorem pureSpinor_annihilator_is_five_dimensional_totallyNull
    {ψ : Spinor} (hψ : IsPureSpinor ψ) :
    InfoGeometry.Clifford.BudinichSpinorsNullVectors.IsTotallyNull
        neutralPairing (neutralAnnihilator ψ) ∧
      Module.finrank ℝ (neutralAnnihilator ψ) = 5 := by
  exact ⟨neutralAnnihilator_totallyNull hψ.1, hψ.2⟩

theorem neutralSpace_finrank : Module.finrank ℝ NeutralSpace = 10 := by
  simp [NeutralSpace, V5, Module.finrank_prod]

theorem pureSpinor_annihilator_finrank_eq_half_neutralSpace
    {ψ : Spinor} (hψ : IsPureSpinor ψ) :
    2 * Module.finrank ℝ (neutralAnnihilator ψ) =
      Module.finrank ℝ NeutralSpace := by
  rw [hψ.2, neutralSpace_finrank]

end InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
