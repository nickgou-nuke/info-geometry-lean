import InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeCompHaus
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Flow transport of finite-stage observation ranges

The scalar inverse-limit flow induces a homeomorphism between the observation
range over an orbit closure and the observation range over its transported
closure.  The map is multiplication by `Real.exp t`; the inverse is the
negative-time map.  No global compactness of the inverse limit is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowHomeomorph

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimit
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeTopCat
open InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitSymbolicLatentFlow
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Topology

abbrev carrier :=
  (limit readoutDiagram).carrier

abbrev flow := scalarDilationSymbolicLatentFlow

variable [T2Space carrier]

def transportedRangePoint
    (ρ : carrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (z : stageObservationRange ρ n X) :
    stageObservationRange (flow.act t ρ) n X := by
  let y : SymbolicLatentModularOrbitClosure flow ρ :=
    Classical.choose z.property
  have hy : orbitClosureStageObservationTopCatHom ρ n X y = z.1 :=
    Classical.choose_spec z.property
  refine ⟨Real.exp t * z.1, ?_⟩
  refine ⟨⟨flow.act t y.1, by
    rw [← flow.actHomeomorph_image_orbitClosure t ρ]
    exact ⟨y.1, y.2, rfl⟩⟩, ?_⟩
  change orbitClosureStageObservationTopCatHom (flow.act t ρ) n X
      (⟨flow.act t y.1, by
        rw [← flow.actHomeomorph_image_orbitClosure t ρ]
        exact ⟨y.1, y.2, rfl⟩⟩) =
    Real.exp t * z.1
  rw [orbitClosureStageObservation_scalar_covariance]
  exact congrArg (fun r : ℝ => Real.exp t * r) hy

theorem transportedRangePoint_val
    (ρ : carrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (z : stageObservationRange ρ n X) :
    (transportedRangePoint ρ n X t z).val = Real.exp t * z.val := by
  rfl

def inverseTransportedRangePoint
    (ρ : carrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (z : stageObservationRange (flow.act t ρ) n X) :
    stageObservationRange ρ n X := by
  let y : SymbolicLatentModularOrbitClosure flow (flow.act t ρ) :=
    Classical.choose z.property
  have hy : orbitClosureStageObservationTopCatHom (flow.act t ρ) n X y = z.1 :=
    Classical.choose_spec z.property
  have hzero : flow.act (-t) (flow.act t ρ) = ρ := by
    calc
      flow.act (-t) (flow.act t ρ) = flow.act (-t + t) ρ :=
        (flow.add_apply (-t) t ρ).symm
      _ = ρ := by rw [neg_add_cancel, flow.zero_apply]
  have hy_mem : flow.act (-t) y.1 ∈ flow.orbitClosure ρ := by
    have hmem : flow.act (-t) y.1 ∈
        flow.orbitClosure (flow.act (-t) (flow.act t ρ)) := by
      rw [← flow.actHomeomorph_image_orbitClosure (-t) (flow.act t ρ)]
      exact ⟨y.1, y.2, rfl⟩
    simpa only [hzero] using hmem
  refine ⟨Real.exp (-t) * z.1, ?_⟩
  refine ⟨⟨flow.act (-t) y.1, hy_mem⟩, ?_⟩
  change orbitClosureStageObservationTopCatHom ρ n X
      (⟨flow.act (-t) y.1, hy_mem⟩) =
    Real.exp (-t) * z.1
  let y' : SymbolicLatentModularOrbitClosure flow ρ :=
    ⟨flow.act (-t) y.1, hy_mem⟩
  have hback :
      (⟨flow.act t y'.1, by
        rw [← flow.actHomeomorph_image_orbitClosure t ρ]
        exact ⟨y'.1, y'.2, rfl⟩⟩ :
        SymbolicLatentModularOrbitClosure flow (flow.act t ρ)) = y := by
    apply Subtype.ext
    change flow.act t (flow.act (-t) y.1) = y.1
    rw [← flow.add_apply, add_neg_cancel, flow.zero_apply]
  have hcov := orbitClosureStageObservation_scalar_covariance ρ n t X y'
  rw [hback, hy] at hcov
  have hcov' : z.1 = Real.exp t *
      orbitClosureStageObservationTopCatHom ρ n X y' := by
    simpa [smul_eq_mul] using hcov
  calc
    orbitClosureStageObservationTopCatHom ρ n X y' =
        Real.exp (-t) *
          (Real.exp t * orbitClosureStageObservationTopCatHom ρ n X y') := by
            rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
              one_mul]
    _ = Real.exp (-t) * z.1 := by rw [← hcov']

theorem inverseTransportedRangePoint_val
    (ρ : carrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (z : stageObservationRange (flow.act t ρ) n X) :
    (inverseTransportedRangePoint ρ n X t z).val = Real.exp (-t) * z.val := by
  rfl

noncomputable def stageObservationRangeFlowHomeomorph
    (ρ : carrier) (n : ℕ) (X : MatStage n) (t : ℝ) :
    stageObservationRange ρ n X ≃ₜ
      stageObservationRange (flow.act t ρ) n X where
  toFun := transportedRangePoint ρ n X t
  invFun := inverseTransportedRangePoint ρ n X t
  left_inv := by
    intro z
    apply Subtype.ext
    rw [inverseTransportedRangePoint_val, transportedRangePoint_val]
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_mul]
  right_inv := by
    intro z
    apply Subtype.ext
    rw [transportedRangePoint_val, inverseTransportedRangePoint_val]
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      one_mul]
  continuous_toFun := by
    let f : stageObservationRange ρ n X →
        stageObservationRange (flow.act t ρ) n X := fun z =>
      ⟨Real.exp t * z.1, (transportedRangePoint ρ n X t z).property⟩
    have hf : Continuous f := by
      exact (continuous_const.mul continuous_subtype_val).subtype_mk
        (fun z => (transportedRangePoint ρ n X t z).property)
    have hfun : f = transportedRangePoint ρ n X t := by
      funext z
      apply Subtype.ext
      rfl
    rw [← hfun]
    exact hf
  continuous_invFun := by
    have hinv_mem (z : stageObservationRange (flow.act t ρ) n X) :
        Real.exp (-t) * z.1 ∈ stageObservationRange ρ n X := by
      have hz := (inverseTransportedRangePoint ρ n X t z).property
      rw [inverseTransportedRangePoint_val ρ n X t z] at hz
      exact hz
    let f : stageObservationRange (flow.act t ρ) n X →
        stageObservationRange ρ n X := fun z =>
      ⟨Real.exp (-t) * z.1,
        hinv_mem z⟩
    have hf : Continuous f := by
      exact (continuous_const.mul continuous_subtype_val).subtype_mk
        hinv_mem
    have hfun : f = inverseTransportedRangePoint ρ n X t := by
      funext z
      apply Subtype.ext
      exact (inverseTransportedRangePoint_val ρ n X t z).symm
    rw [← hfun]
    exact hf

@[simp] theorem stageObservationRangeFlowHomeomorph_apply
    (ρ : carrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (z : stageObservationRange ρ n X) :
    stageObservationRangeFlowHomeomorph ρ n X t z =
      transportedRangePoint ρ n X t z := rfl

theorem stageObservationRangeFlowHomeomorph_inverse_apply
    (ρ : carrier) (n : ℕ) (X : MatStage n) (t : ℝ)
    (z : stageObservationRange (flow.act t ρ) n X) :
    (stageObservationRangeFlowHomeomorph ρ n X t).symm z =
      inverseTransportedRangePoint ρ n X t z := rfl

@[simp] theorem stageObservationRangeFlowHomeomorph_zero_apply
    (ρ : carrier) (n : ℕ) (X : MatStage n)
    (z : stageObservationRange ρ n X) :
    (stageObservationRangeFlowHomeomorph ρ n X 0 z).1 = z.1 := by
  change (transportedRangePoint ρ n X 0 z).val = z.val
  rw [transportedRangePoint_val]
  simp

theorem stageObservationRangeFlowHomeomorph_trans_apply
    (ρ : carrier) (n : ℕ) (X : MatStage n) (s t : ℝ)
    (z : stageObservationRange ρ n X) :
    ((stageObservationRangeFlowHomeomorph ρ n X t).trans
        (stageObservationRangeFlowHomeomorph (flow.act t ρ) n X s) z).1 =
      (stageObservationRangeFlowHomeomorph ρ n X (s + t) z).1 := by
  change (stageObservationRangeFlowHomeomorph (flow.act t ρ) n X s
      (stageObservationRangeFlowHomeomorph ρ n X t z)).val =
    (transportedRangePoint ρ n X (s + t) z).val
  rw [stageObservationRangeFlowHomeomorph_apply,
    stageObservationRangeFlowHomeomorph_apply, transportedRangePoint_val,
    transportedRangePoint_val]
  calc
    Real.exp s * (Real.exp t * z.1) =
        (Real.exp s * Real.exp t) * z.1 := by ring
    _ = Real.exp (s + t) * z.1 := by rw [← Real.exp_add]

end InfoGeometry.Canonical.RealUHFCompatibleReadoutInverseLimitStageObservationRangeFlowHomeomorph
end
