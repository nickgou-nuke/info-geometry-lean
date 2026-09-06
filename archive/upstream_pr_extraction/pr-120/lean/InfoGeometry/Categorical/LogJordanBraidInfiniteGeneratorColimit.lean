import Mathlib
import InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
import InfoGeometry.Categorical.HadjiivanovRMatrixBraid

/-!
# Infinite Hadjiivanov braid generators on the tensor-power colimit

A fixed Artin generator `σ_i` is only present from the finite braid stage
`B_{i+2}` onward.  Rather than defining any artificial action on earlier
stages, this file follows the repository's existing upper-tail colimit pattern:

1. restrict the stabilized tensor-power diagram to the tail beginning at stage
   `i`;
2. use the already-proved finite-stage stabilization theorem to package the
   `i`th checked-R slice as a natural automorphism of that tail;
3. descend the natural automorphism with Mathlib's `colim` functor;
4. use finality of the shift functor `n ↦ i+n` to identify the tail colimit with
   the full tensor-power colimit.

No new quotient or infinite tensor carrier is introduced.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidInfiniteGeneratorColimit

open CategoryTheory
open CategoryTheory.Limits
open Braid

open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
open InfoGeometry.Categorical.LogJordanTensorPowerStabilization
open InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge

/-- Shift of the natural-number index category by a fixed finite prefix. -/
def natTailFunctor (m : ℕ) : ℕ ⥤ ℕ :=
  (show Monotone (fun n : ℕ => m + n) by omega).functor

/-- Truncated subtraction is left adjoint to the finite-prefix shift. -/
def natTailLeftFunctor (m : ℕ) : ℕ ⥤ ℕ :=
  (show Monotone (fun n : ℕ => n - m) by omega).functor

/-- Order-theoretic adjunction underlying finite-tail cofinality. -/
theorem natTail_galois (m : ℕ) :
    GaloisConnection (fun n : ℕ => n - m) (fun n : ℕ => m + n) := by
  intro a b
  omega

/-- The tail shift is a right adjoint and hence a final functor. -/
def natTailAdjunction (m : ℕ) :
    natTailLeftFunctor m ⊣ natTailFunctor m :=
  (natTail_galois m).adjunction

noncomputable instance natTailFunctor_final (m : ℕ) :
    (natTailFunctor m).Final :=
  Functor.final_of_adjunction (natTailAdjunction m)

/-- The tensor-power module diagram with the first `m` finite stages removed. -/
def tailTensorPowerModuleDiagram (m : ℕ) : ℕ ⥤ ModuleCat ℂ :=
  natTailFunctor m ⋙ standardTensorPowerModuleDiagram

/-- The fixed infinite generator index `i`, viewed at tail stage `k`. -/
def tailGeneratorIndex (i k : ℕ) : Fin (i + k + 1) :=
  ⟨i, by omega⟩

/-- The `i`th finite checked-R slice on tail stage `k`. -/
abbrev tailGeneratorEquiv (i k : ℕ) :=
  standardTensorPowerGenerator (i + k) (tailGeneratorIndex i k)

/-- The stagewise `i`th checked-R actions form a natural endomorphism of the
upper-tail module diagram. -/
def tailGeneratorNatTrans (i : ℕ) :
    tailTensorPowerModuleDiagram i ⟶ tailTensorPowerModuleDiagram i :=
  NatTrans.ofSequence
    (app := fun k => ModuleCat.ofHom (tailGeneratorEquiv i k).toLinearMap)
    (naturality := by
      intro k
      apply ModuleCat.hom_ext
      ext v
      let idx : Fin (i + k + 1) := tailGeneratorIndex i k
      have h := appendPrimaryBonding_braid_compat (i + k)
        (σ' (i + k + 1) idx)
      have hv := LinearMap.congr_fun h v
      simpa [tailTensorPowerModuleDiagram, natTailFunctor,
        tailGeneratorEquiv, tailGeneratorIndex, ModuleCat.comp_apply,
        standardHadjiivanovBraidProject_sigma] using hv.symm)

/-- The inverse checked-R slices are natural on the same upper tail. -/
def tailGeneratorInvNatTrans (i : ℕ) :
    tailTensorPowerModuleDiagram i ⟶ tailTensorPowerModuleDiagram i :=
  NatTrans.ofSequence
    (app := fun k =>
      ModuleCat.ofHom (tailGeneratorEquiv i k).symm.toLinearMap)
    (naturality := by
      intro k
      apply ModuleCat.hom_ext
      ext v
      let idx : Fin (i + k + 1) := tailGeneratorIndex i k
      have h := appendPrimaryBonding_braid_compat (i + k)
        ((σ' (i + k + 1) idx)⁻¹)
      have hv := LinearMap.congr_fun h v
      simpa [tailTensorPowerModuleDiagram, natTailFunctor,
        tailGeneratorEquiv, tailGeneratorIndex, ModuleCat.comp_apply,
        standardHadjiivanovBraidProject_sigma] using hv.symm)

/-- Natural automorphism of the upper-tail tensor-power diagram. -/
def tailGeneratorNatIso (i : ℕ) :
    tailTensorPowerModuleDiagram i ≅ tailTensorPowerModuleDiagram i where
  hom := tailGeneratorNatTrans i
  inv := tailGeneratorInvNatTrans i
  hom_inv_id := by
    ext k
    apply ModuleCat.hom_ext
    ext v
    simp [tailGeneratorNatTrans, tailGeneratorInvNatTrans,
      tailGeneratorEquiv]
  inv_hom_id := by
    ext k
    apply ModuleCat.hom_ext
    ext v
    simp [tailGeneratorNatTrans, tailGeneratorInvNatTrans,
      tailGeneratorEquiv]

/-- Automorphism induced by the `i`th checked-R generator on the tail colimit. -/
def tailGeneratorColimitAut (i : ℕ) :
    Aut (colimit (tailTensorPowerModuleDiagram i)) :=
  (colim : (ℕ ⥤ ModuleCat ℂ) ⥤ ModuleCat ℂ).mapIso
    (tailGeneratorNatIso i)

/-- Removing a finite prefix does not change the sequential tensor-power
colimit.  This is Mathlib's final-functor colimit isomorphism. -/
def tailToGlobalColimitIso (i : ℕ) :
    colimit (tailTensorPowerModuleDiagram i) ≅ StandardTensorPowerColimit := by
  simpa [tailTensorPowerModuleDiagram] using
    (Functor.Final.colimitIso (natTailFunctor i)
      standardTensorPowerModuleDiagram)

/-- Canonical action of the infinite Artin generator `σ_i` on the single global
Hadjiivanov tensor-power colimit. -/
def infiniteGeneratorAut (i : ℕ) : Aut StandardTensorPowerColimit :=
  (tailToGlobalColimitIso i).conjAut (tailGeneratorColimitAut i)

/-- At every stage where `σ_i` exists, the global colimit automorphism reads
back as the already-proved finite checked-R slice. -/
theorem infiniteGeneratorAut_stage
    (i k : ℕ) :
    stageInclusion (i + k) ≫ (infiniteGeneratorAut i).hom =
      ModuleCat.ofHom (tailGeneratorEquiv i k).toLinearMap ≫
        stageInclusion (i + k) := by
  change
    colimit.ι standardTensorPowerModuleDiagram (i + k) ≫
        ((tailToGlobalColimitIso i).conjAut
          (tailGeneratorColimitAut i)).hom =
      ModuleCat.ofHom (tailGeneratorEquiv i k).toLinearMap ≫
        colimit.ι standardTensorPowerModuleDiagram (i + k)
  rw [Iso.conjAut_hom, Iso.conj]
  simp only [Category.assoc]
  rw [Functor.Final.ι_colimitIso_inv (natTailFunctor i)
    standardTensorPowerModuleDiagram k]
  rw [show (tailGeneratorColimitAut i).hom =
      colim.map (tailGeneratorNatTrans i) by rfl]
  rw [colimit.ι_map]
  rw [Functor.Final.ι_colimitIso_hom (natTailFunctor i)
    standardTensorPowerModuleDiagram k]
  rfl

/-- Readback at an arbitrary sufficiently late finite stage. -/
theorem infiniteGeneratorAut_stage_of_le
    (i n : ℕ) (h : i ≤ n) :
    stageInclusion n ≫ (infiniteGeneratorAut i).hom =
      ModuleCat.ofHom
          (standardTensorPowerGenerator n ⟨i, by omega⟩).toLinearMap ≫
        stageInclusion n := by
  have hstage := infiniteGeneratorAut_stage i (n - i)
  simpa [Nat.add_sub_of_le h, tailGeneratorEquiv, tailGeneratorIndex] using hstage

end InfoGeometry.Categorical.LogJordanBraidInfiniteGeneratorColimit
