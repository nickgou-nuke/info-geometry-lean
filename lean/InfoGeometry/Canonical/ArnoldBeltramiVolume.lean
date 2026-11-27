/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ArnoldBeltramiFlow
import InfoGeometry.Canonical.SmoothVolumePreservingGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Volume-preserving Beltrami flow and finite-region helicity

The explicit particle flow preserves Lebesgue measure by the skew-product
theorem: after splitting off the third coordinate, it translates the horizontal
fibre. Its smooth homeomorphisms form a faithful one-parameter subgroup of the
native smooth measure-preserving automorphism group.

The helicity integral below is over an explicit finite rectangular cell. The
cell is not claimed to be invariant, and no torus quotient or finite whole-space
energy is inferred from this calculation.
-/

noncomputable section

namespace InfoGeometry.Canonical.ArnoldBeltramiFlow

open MeasureTheory
open InfoGeometry.Canonical.NavierStokesShearReconstruction

/-- The smooth particle flow, packaged as a homeomorphism with its actual inverse. -/
def flowHomeomorph (s t : ℝ) : Space ≃ₜ Space where
  toEquiv := flowEquiv s t
  continuous_toFun := (contDiff_flow s t).continuous
  continuous_invFun := (contDiff_flow s (-t)).continuous

@[simp] theorem flowHomeomorph_apply (s t : ℝ) (x : Space) :
    flowHomeomorph s t x = flow s t x := rfl

@[simp] theorem flowHomeomorph_symm_apply (s t : ℝ) (x : Space) :
    (flowHomeomorph s t).symm x = flow s (-t) x := rfl

/-- Actual preservation of three-dimensional Lebesgue measure, for every parameter. -/
theorem measurePreserving_flow (s t : ℝ) :
    MeasurePreserving (flow s t) (volume : Measure Space) volume := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have he : MeasurePreserving e volume volume :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  let g : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
    fun z v => ![t * Real.cos z, -s * t * Real.sin z] + v
  have hgm : Measurable (Function.uncurry g) := by
    apply Continuous.measurable
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [g, Function.uncurry] <;> fun_prop
  have hg : ∀ᵐ z ∂(volume : Measure ℝ),
      Measure.map (g z) (volume : Measure (Fin 2 → ℝ)) = volume := by
    exact ae_of_all _ fun z =>
      (measurePreserving_add_left (volume : Measure (Fin 2 → ℝ))
        ![t * Real.cos z, -s * t * Real.sin z]).map_eq
  have hskew := (MeasurePreserving.id (volume : Measure ℝ)).skew_product hgm hg
  have hconj := (MeasurePreserving.symm e he).comp (hskew.comp he)
  have hfun : e.symm ∘ (fun p : ℝ × (Fin 2 → ℝ) => (p.1, g p.1 p.2)) ∘ e =
      flow s t := by
    funext x
    apply e.injective
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;>
        simp [e, g, flow, MeasurableEquiv.piFinSuccAbove,
          Fin.insertNthEquiv, Fin.removeNth, Fin.succAbove,
          Matrix.vecHead, Matrix.vecTail, add_comm, sub_eq_add_neg]
  simpa only [id_eq, hfun] using hconj

/-- A genuine one-parameter subgroup of smooth volume-preserving automorphisms. -/
def flowHom (s : ℝ) :
    Multiplicative ℝ →* smoothVolumePreservingSubgroup (volume : Measure Space) where
  toFun t := ⟨flowHomeomorph s t.toAdd,
    contDiff_flow s t.toAdd, contDiff_flow s (-t.toAdd), measurePreserving_flow s t.toAdd⟩
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    exact flow_zero s x
  map_mul' t r := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    exact (flow_add s t.toAdd r.toAdd x).symm

/-- Time is not collapsed: the first coordinate at the origin recovers it. -/
theorem flowHom_injective (s : ℝ) : Function.Injective (flowHom s) := by
  intro t r h
  have hx := congrArg (fun g : smoothVolumePreservingSubgroup (volume : Measure Space) =>
    g.val (0 : Space) 0) h
  change t.toAdd = r.toAdd
  simpa [flowHom, flowHomeomorph, flowEquiv, flow] using hx

/-- A finite rectangular cell of side length `2π`; no quotient is implicit. -/
def periodicCell : Set Space := Set.Icc (0 : Space) (fun _ => 2 * Real.pi)

theorem volume_periodicCell : volume.real periodicCell = (2 * Real.pi) ^ 3 := by
  change (volume (Set.Icc (0 : Space) (fun _ => 2 * Real.pi))).toReal = _
  rw [Real.volume_Icc_pi_toReal (by
    intro i
    exact le_of_lt (mul_pos (by norm_num) Real.pi_pos))]
  simp [pow_succ]

/-- The integral uses actual curl and the native Lebesgue integral. -/
theorem helicity_integral_periodicCell (s : ℝ) :
    (∫ x in periodicCell, ∑ i, velocity s x i * curl (velocity s) x i) =
      (2 * Real.pi) ^ 3 * s := by
  simp_rw [helicity_density_velocity]
  rw [setIntegral_const, volume_periodicCell]
  rfl

end InfoGeometry.Canonical.ArnoldBeltramiFlow
