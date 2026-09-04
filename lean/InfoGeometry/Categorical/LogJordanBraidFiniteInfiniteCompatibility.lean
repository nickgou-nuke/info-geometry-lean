import Mathlib
import InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation

/-!
# Finite/infinite Hadjiivanov braid compatibility

The infinite Hadjiivanov representation is constructed generatorwise from
upper-tail actions on the tensor-power colimit.  This file closes the remaining
finite-stage readback gap: every finite braid element, not only every Artin
generator, intertwines with the canonical stage inclusion.

The proof deliberately does not revisit the colimit construction.  For a fixed
finite stage, the braid elements satisfying the intertwining equation form a
subgroup.  The existing `Braid.generated_by` theorem then reduces the result to
the already-proved generator readback.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidFiniteInfiniteCompatibility

open CategoryTheory
open Braid

open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
open InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
open InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation

/-- Pointwise finite-stage intertwining predicate for a braid element.

The orientation follows the actual colimit maps: first act on the finite tensor
stage and then include, or first include and then act by the global `B_∞`
automorphism. -/
def BraidElementCompatible
    (n : ℕ) (g : braid_group (n + 2)) : Prop :=
  ∀ v : tensorPowerObj standardJordanObject (n + 2),
    (stageInclusion n).hom
        (standardHadjiivanovBraidProjectHom n g v) =
      (hadjiivanovBraidGroupInfHom
          (finiteToInfiniteGroupHom (n + 1) g)).hom
        ((stageInclusion n).hom v)

private theorem compatible_one (n : ℕ) :
    BraidElementCompatible n 1 := by
  intro v
  simp [BraidElementCompatible]

private theorem compatible_mul
    (n : ℕ) {g h : braid_group (n + 2)}
    (hg : BraidElementCompatible n g)
    (hh : BraidElementCompatible n h) :
    BraidElementCompatible n (g * h) := by
  intro v
  unfold BraidElementCompatible at hg hh ⊢
  simp only [map_mul, LinearEquiv.mul_apply, ModuleCat.comp_apply]
  calc
    (stageInclusion n).hom
        (standardHadjiivanovBraidProjectHom n h
          (standardHadjiivanovBraidProjectHom n g v)) =
      (hadjiivanovBraidGroupInfHom
          (finiteToInfiniteGroupHom (n + 1) h)).hom
        ((stageInclusion n).hom
          (standardHadjiivanovBraidProjectHom n g v)) :=
      hh (standardHadjiivanovBraidProjectHom n g v)
    _ =
      (hadjiivanovBraidGroupInfHom
          (finiteToInfiniteGroupHom (n + 1) h)).hom
        ((hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) g)).hom
          ((stageInclusion n).hom v)) := by
      rw [hg v]

private theorem compatible_inv
    (n : ℕ) {g : braid_group (n + 2)}
    (hg : BraidElementCompatible n g) :
    BraidElementCompatible n g⁻¹ := by
  intro v
  unfold BraidElementCompatible at hg ⊢
  have h := hg (standardHadjiivanovBraidProjectHom n g⁻¹ v)
  have h' := congrArg
    (fun w =>
      (hadjiivanovBraidGroupInfHom
          (finiteToInfiniteGroupHom (n + 1) g⁻¹)).hom w) h
  simpa [map_inv, LinearEquiv.inv_apply_apply] using h'.symm

/-- The already-owned global generator readback gives compatibility for every
finite Artin generator. -/
private theorem compatible_sigma
    (n : ℕ) (i : Fin (n + 1)) :
    BraidElementCompatible n (σ' (n + 1) i) := by
  intro v
  unfold BraidElementCompatible
  rw [standardHadjiivanovBraidProject_sigma]
  rw [finiteToInfiniteGroupHom_sigma]
  rw [hadjiivanovBraidGroupInfHom_sigma]
  have h := hadjiivanovBraidGroupInf_sigma_stage i.1 n (by omega)
  have hv := congrArg (fun f => f.hom v) h
  simpa [ModuleCat.comp_apply] using hv.symm

/-- Master finite-stage compatibility theorem.

For every `g ∈ B_{n+2}`, the finite Hadjiivanov action on `J^{⊗(n+2)}` and the
global `B_∞` action on the tensor-power colimit agree after the canonical stage
inclusion. -/
theorem hadjiivanov_finite_infinite_compatibility
    (n : ℕ) (g : braid_group (n + 2)) :
    BraidElementCompatible n g := by
  let H : Subgroup (braid_group (n + 2)) where
    carrier := {g | BraidElementCompatible n g}
    one_mem := compatible_one n
    mul_mem := by
      intro a b ha hb
      exact compatible_mul n ha hb
    inv_mem := by
      intro a ha
      exact compatible_inv n ha
  have hgen : ∀ i : Fin (n + 1), σ' (n + 1) i ∈ H := by
    intro i
    exact compatible_sigma n i
  exact Braid.generated_by (n + 1) H hgen g

/-- Categorical morphism form of the master theorem.  This is the exact
finite-to-infinite representation square used by the Hadjiivanov capstone. -/
theorem hadjiivanov_finite_infinite_compatibility_hom
    (n : ℕ) (g : braid_group (n + 2)) :
    ModuleCat.ofHom
          (standardHadjiivanovBraidProjectHom n g).toLinearMap ≫
        stageInclusion n =
      stageInclusion n ≫
        (hadjiivanovBraidGroupInfHom
          (finiteToInfiniteGroupHom (n + 1) g)).hom := by
  ext v
  exact hadjiivanov_finite_infinite_compatibility n g v

end InfoGeometry.Categorical.LogJordanBraidFiniteInfiniteCompatibility