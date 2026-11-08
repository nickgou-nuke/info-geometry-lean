import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
import InfoGeometry.Spectral.Algebra.ChainComplex

/-!
# Exterior-degree behavior of the Cl(5,5) spinor contraction

The neutral spinor carrier is the exterior algebra on five modes.  Its native
Clifford contraction is square-zero and lowers the exterior degree on wedge
words.  These are the concrete differential and filtration-compatibility
facts needed before constructing an exact couple from this carrier.
-/

namespace InfoGeometry.Clifford.Cl55ExteriorContractionGrading

open InfoGeometry.Clifford.SplitClifford55ExteriorSpinor
open InfoGeometry.Spectral.Algebra

abbrev V := V5
abbrev Spinor := SplitClifford55ExteriorSpinor.Spinor

/-- The degree-lowering differential associated to a covector. -/
abbrev differential (φ : Module.Dual ℝ V) : Module.End ℝ Spinor :=
  contract φ

/-- The Clifford contraction is a genuine square-zero differential. -/
@[simp] theorem differential_sq (φ : Module.Dual ℝ V) :
    (differential φ).comp (differential φ) = 0 := by
  exact contract_sq φ

/-- The Koszul homotopy identity: contraction followed by exterior
multiplication, plus exterior multiplication followed by contraction, is
scalar multiplication by the covector evaluated on the inserted vector. -/
theorem contraction_wedge_homotopy (φ : Module.Dual ℝ V) (v : V)
    (x : Spinor) :
    differential φ (ExteriorAlgebra.ι ℝ v * x) +
        ExteriorAlgebra.ι ℝ v * differential φ x = φ v • x := by
  change CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm ℝ V)) φ (ExteriorAlgebra.ι ℝ v * x) +
    ExteriorAlgebra.ι ℝ v *
      CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm ℝ V)) φ x = φ v • x
  rw [CliffordAlgebra.contractLeft_ι_mul]
  module

/-- A covector-vector pair with evaluation one gives an explicit contracting
homotopy for the spinor differential. -/
theorem contraction_homotopy_of_pairing_one
    (φ : Module.Dual ℝ V) (v : V) (hφv : φ v = 1) (x : Spinor) :
    differential φ (ExteriorAlgebra.ι ℝ v * x) +
        ExteriorAlgebra.ι ℝ v * differential φ x = x := by
  rw [contraction_wedge_homotopy, hφv, one_smul]

/-- Contracting a homogeneous wedge word of degree `n + 1` lands in exterior
degree `n`. This is the degree-compatibility theorem for the five-mode spinor. -/
theorem differential_ιMulti_succ_mem
    (φ : Module.Dual ℝ V) (n : ℕ) (v : Fin (n + 1) → V) :
    differential φ (ExteriorAlgebra.ιMulti ℝ (n + 1) v) ∈ ⋀[ℝ]^n V := by
  induction n with
  | zero =>
      change CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm ℝ V)) φ
          (ExteriorAlgebra.ιMulti ℝ (0 + 1) v) ∈ ⋀[ℝ]^0 V
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        ExteriorAlgebra.ιMulti_zero_apply,
        CliffordAlgebra.contractLeft_ι_mul]
      simpa [differential, contract, CliffordAlgebra.contractLeft_one] using
        ((⋀[ℝ]^0 V).smul_mem (φ (v 0)) (by
          exact SetLike.GradedOne.one_mem))
  | succ n ih =>
      change CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm ℝ V)) φ
          (ExteriorAlgebra.ιMulti ℝ (n + 1 + 1) v) ∈ ⋀[ℝ]^(n + 1) V
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        CliffordAlgebra.contractLeft_ι_mul]
      have htail : ExteriorAlgebra.ιMulti ℝ (n + 1)
          (Matrix.vecTail v) ∈ ⋀[ℝ]^(n + 1) V := by
        apply ExteriorAlgebra.ιMulti_range
        exact ⟨Matrix.vecTail v, rfl⟩
      have hcontract : differential φ
          (ExteriorAlgebra.ιMulti ℝ (n + 1)
            (Matrix.vecTail v)) ∈ ⋀[ℝ]^n V :=
        ih (Matrix.vecTail v)
      have hhead : ExteriorAlgebra.ι ℝ (v 0) ∈ ⋀[ℝ]^1 V := by
        simpa only [pow_one] using
          (LinearMap.mem_range_self
            (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] Spinor) (v 0))
      have hmul : ExteriorAlgebra.ι ℝ (v 0) *
          differential φ (ExteriorAlgebra.ιMulti ℝ (n + 1)
            (Matrix.vecTail v)) ∈ ⋀[ℝ]^(n + 1) V := by
        simpa [Nat.add_comm] using
          (SetLike.GradedMonoid.toGradedMul.mul_mem
            (i := 1) (j := n) hhead hcontract)
      exact (⋀[ℝ]^(n + 1) V).sub_mem
        ((⋀[ℝ]^(n + 1) V).smul_mem (φ (v 0)) htail) hmul

/-- Contraction maps every homogeneous degree-`n+1` submodule into degree `n`.
The fixed-degree `ιMulti` spanning theorem extends the wedge-word calculation
to all homogeneous elements. -/
theorem differential_maps_exteriorDegree (φ : Module.Dual ℝ V) (n : ℕ) :
    ∀ x ∈ (⋀[ℝ]^(n + 1) V : Submodule ℝ Spinor),
      differential φ x ∈ ⋀[ℝ]^n V := by
  intro x hx
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree
    (R := ℝ) (M := V) (n := n + 1)] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact differential_ιMulti_succ_mem φ n v
  | zero => simpa using (⋀[ℝ]^n V).zero_mem
  | add x y _ _ hx hy =>
      simpa only [map_add] using (⋀[ℝ]^n V).add_mem hx hy
  | smul c x _ hx =>
      simpa only [map_smul] using (⋀[ℝ]^n V).smul_mem c hx

/-- The degree-`n+1` to degree-`n` restriction of Clifford contraction. -/
noncomputable def differentialComponent (φ : Module.Dual ℝ V) (n : ℕ) :
    (⋀[ℝ]^(n + 1) V) →ₗ[ℝ] (⋀[ℝ]^n V) :=
  ((differential φ).comp (⋀[ℝ]^(n + 1) V).subtype).codRestrict
    (⋀[ℝ]^n V) (fun x => differential_maps_exteriorDegree φ n x.1 x.2)

@[simp] theorem differentialComponent_apply
    (φ : Module.Dual ℝ V) (n : ℕ) (x : ⋀[ℝ]^(n + 1) V) :
    ((differentialComponent φ n x : ⋀[ℝ]^n V) : Spinor) =
      differential φ x :=
  rfl

/-- Exterior multiplication by a mode, restricted from degree `n` to degree
`n+1`. This is the homotopy operator paired with contraction. -/
noncomputable def wedgeComponent (v : V) (n : ℕ) :
    (⋀[ℝ]^n V) →ₗ[ℝ] (⋀[ℝ]^(n + 1) V) :=
  (LinearMap.mulLeft ℝ (ExteriorAlgebra.ι ℝ v)).comp
    (⋀[ℝ]^n V).subtype |>.codRestrict (⋀[ℝ]^(n + 1) V)
      (fun x => by
        have hv : ExteriorAlgebra.ι ℝ v ∈ ⋀[ℝ]^1 V := by
          simpa only [pow_one] using
            (LinearMap.mem_range_self
              (ExteriorAlgebra.ι ℝ : V →ₗ[ℝ] Spinor) v)
        simpa [Nat.add_comm] using
          (SetLike.GradedMonoid.toGradedMul.mul_mem
            (i := 1) (j := n) hv x.2))

@[simp] theorem wedgeComponent_apply
    (v : V) (n : ℕ) (x : ⋀[ℝ]^n V) :
    ((wedgeComponent v n x : ⋀[ℝ]^(n + 1) V) : Spinor) =
      ExteriorAlgebra.ι ℝ v * x :=
  rfl

/-- The contracting-homotopy identity holds on every positive exterior degree.
Thus any covector admitting a unit-pairing vector makes the positive-degree
part of the contraction complex exact. -/
theorem component_homotopy_identity
    (φ : Module.Dual ℝ V) (v : V) (hφv : φ v = 1) (n : ℕ)
    (x : ⋀[ℝ]^(n + 1) V) :
    differentialComponent φ (n + 1) (wedgeComponent v (n + 1) x) +
      wedgeComponent v n (differentialComponent φ n x) = x := by
  apply Subtype.ext
  change differential φ (ExteriorAlgebra.ι ℝ v * (x : Spinor)) +
      ExteriorAlgebra.ι ℝ v * differential φ (x : Spinor) = (x : Spinor)
  exact contraction_homotopy_of_pairing_one φ v hφv (x : Spinor)

/-- Consecutive homogeneous restrictions compose to zero, inherited from the
square-zero Clifford contraction on the whole spinor. -/
theorem differentialComponent_comp_zero
    (φ : Module.Dual ℝ V) (n : ℕ) :
    (differentialComponent φ n).comp
      (differentialComponent φ (n + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change differential φ (differential φ (x : Spinor)) = 0
  have h := LinearMap.congr_fun (differential_sq φ) (x : Spinor)
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply,
    differentialComponent_apply] using h

/-- A unit-pairing vector makes the degreewise contraction complex exact at
every positive exterior degree. This is the concrete Koszul exactness
statement, not merely square-zero of the differential. -/
theorem differentialComponent_exact
    (φ : Module.Dual ℝ V) (v : V) (hφv : φ v = 1) (n : ℕ) :
    LinearMap.ker (differentialComponent φ n) =
      LinearMap.range (differentialComponent φ (n + 1)) := by
  ext x
  constructor
  · intro hx
    have h := component_homotopy_identity φ v hφv n x
    have hdx : differentialComponent φ n x = 0 :=
      LinearMap.mem_ker.mp hx
    rw [hdx, map_zero] at h
    have h' : differentialComponent φ (n + 1)
        (wedgeComponent v (n + 1) x) = x := by
      simpa only [add_zero] using h
    exact ⟨wedgeComponent v (n + 1) x, h'⟩
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change differential φ (differential φ (y : Spinor)) = 0
    exact LinearMap.congr_fun (differential_sq φ) (y : Spinor)

/-- Every nonzero covector on the five-mode real carrier has a unit-pairing
vector, so its homogeneous Koszul complex is exact in all positive degrees. -/
theorem differentialComponent_exact_of_ne_zero
    (φ : Module.Dual ℝ V) (hφ : φ ≠ 0) (n : ℕ) :
    LinearMap.ker (differentialComponent φ n) =
      LinearMap.range (differentialComponent φ (n + 1)) := by
  have htop : LinearMap.range φ = ⊤ :=
    Module.Dual.range_eq_top_of_ne_zero hφ
  have hone : 1 ∈ LinearMap.range φ := by rw [htop]; exact Submodule.mem_top
  obtain ⟨v, hv⟩ := hone
  exact differentialComponent_exact φ v hv n

/-- The genuine five-mode Koszul chain complex on the homogeneous spinor
degrees, with the Mathlib Clifford contraction as its differential. -/
noncomputable def contractionChainComplex (φ : Module.Dual ℝ V) :
    ModuleChainComplex.Carrier ℝ :=
  ModuleChainComplex.of ℝ
    (fun n => ModuleCat.of ℝ (⋀[ℝ]^n V))
    (fun n => ModuleCat.ofHom (differentialComponent φ n))
    (by
      intro n
      rw [← ModuleCat.ofHom_comp]
      exact congrArg (ModuleCat.ofHom) (differentialComponent_comp_zero φ n))

/-- The increasing degree-cutoff filtration on the Koszul chain complex:
`F_p C_n` is the whole degree-`n` term for `n ≤ p` and zero otherwise. -/
def degreeCutoffFiltration (p n : ℕ) : Submodule ℝ (⋀[ℝ]^n V) :=
  if n ≤ p then ⊤ else ⊥

/-- The cutoff filtration is increasing in its filtration index. -/
theorem degreeCutoffFiltration_mono (p n : ℕ) :
    degreeCutoffFiltration p n ≤ degreeCutoffFiltration (p + 1) n := by
  by_cases h : n ≤ p
  · have h' : n ≤ p + 1 := by omega
    simp [degreeCutoffFiltration, h, h']
  · simp [degreeCutoffFiltration, h]

/-- The Clifford contraction preserves every filtration level of the
degree-cutoff filtration. -/
theorem differential_preserves_degreeCutoff
    (φ : Module.Dual ℝ V) (p n : ℕ)
    (x : ⋀[ℝ]^(n + 1) V)
    (hx : x ∈ degreeCutoffFiltration p (n + 1)) :
    differentialComponent φ n x ∈ degreeCutoffFiltration p n := by
  by_cases h : n + 1 ≤ p
  · have hn : n ≤ p := by omega
    simp [degreeCutoffFiltration, hn]
  · have hx0 : x = 0 := by
      simpa [degreeCutoffFiltration, h] using hx
    subst x
    simp [degreeCutoffFiltration]

/-- The canonical inclusion between adjacent filtration levels, degreewise. -/
noncomputable def degreeCutoffInclusion (p n : ℕ) :
    degreeCutoffFiltration p n →ₗ[ℝ] degreeCutoffFiltration (p + 1) n :=
  (degreeCutoffFiltration p n).subtype.codRestrict
    (degreeCutoffFiltration (p + 1) n)
    (fun x => degreeCutoffFiltration_mono p n x.2)

@[simp] theorem degreeCutoffInclusion_apply
    (p n : ℕ) (x : degreeCutoffFiltration p n) :
    ((degreeCutoffInclusion p n x : degreeCutoffFiltration (p + 1) n) :
      ⋀[ℝ]^n V) = x := rfl

end InfoGeometry.Clifford.Cl55ExteriorContractionGrading
