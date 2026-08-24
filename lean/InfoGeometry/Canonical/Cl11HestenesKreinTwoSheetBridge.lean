import InfoGeometry.Canonical.HestenesKreinFiniteStageCompatibility
import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import Mathlib.Tactic.FinCases

/-!
# Hestenes--Krein two-sheet structure on the native Cl(1,1) dyadic tower

This owner uses the existing concrete bonding maps

`A ↦ A ⊗ I₂`

from `Cl11TensorTower` / `Cl11MarkovJonesEngine`.  No new inductive system is
chosen.  We shift the indexing by one so every stage contains the distinguished
first `Cl(1,1)` tensor factor carrying the two-sheet Hestenes data.

The stage-1 atoms are:

* `η = γ₀`, the sheet-exchange involution;
* `f₊ = (1 + Γ)/2` and `f₋ = (1 - Γ)/2`, the two local chiral projectors.

They are transported through the already existing finite embedding maps.  Left
multiplication by these transported elements gives natural transformations on
the real module diagram.  The pointwise Hestenes laws instantiate
`HestenesKreinFiniteStageCompatibility.Datum`, which then reuses the existing
filtered-colimit descent.

No analytic completion or new UHF/Clifford tower is introduced here.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge

open CategoryTheory CategoryTheory.Limits
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11MarkovJonesEngine
open InfoGeometry.Meta.MarkovJonesInduction
open InfoGeometry.Canonical.HestenesKreinFiniteStageCompatibility
open InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge

/-- Positive-depth stage: stage `n` is the existing matrix stage `n+1`. -/
abbrev Stage (n : ℕ) := MatStage (n + 1)

/-- Existing iterated Cl(1,1) embedding, with the index shifted by one. -/
noncomputable def stageMapAlg (m n : ℕ) (h : m ≤ n) :
    Stage m →ₐ[ℝ] Stage n :=
  Nat.leRecOn h
    (C := fun n => Stage m →ₐ[ℝ] Stage n)
    (fun {k} ih => (stageEmbed (k + 1)).comp ih)
    (AlgHom.id ℝ (Stage m))

@[simp] theorem stageMapAlg_refl (m : ℕ) :
    stageMapAlg m m le_rfl = AlgHom.id ℝ (Stage m) := by
  simpa [stageMapAlg] using
    (Nat.leRecOn_self
      (C := fun n => Stage m →ₐ[ℝ] Stage n)
      (next := fun {k} ih => (stageEmbed (k + 1)).comp ih)
      (x := AlgHom.id ℝ (Stage m)))

@[simp] theorem stageMapAlg_succ
    (m n : ℕ) (h : m ≤ n) :
    stageMapAlg m (n + 1) (Nat.le_trans h (Nat.le_succ n)) =
      (stageEmbed (n + 1)).comp (stageMapAlg m n h) := by
  unfold stageMapAlg
  rw [Nat.leRecOn_trans h (Nat.le_succ n)]
  rw [Nat.leRecOn_succ']

/-- Composition law for the shifted existing tower maps. -/
theorem stageMapAlg_apply_trans
    (m n k : ℕ) (hmn : m ≤ n) (hnk : n ≤ k) (x : Stage m) :
    stageMapAlg m k (hmn.trans hnk) x =
      stageMapAlg n k hnk (stageMapAlg m n hmn x) := by
  refine Nat.le_induction
    (m := n)
    (P := fun t ht =>
      stageMapAlg m t (Nat.le_trans hmn ht) x =
        stageMapAlg n t ht (stageMapAlg m n hmn x))
    ?_ ?_ k hnk
  · simp
  · intro t hnt ih
    rw [stageMapAlg_succ m t (Nat.le_trans hmn hnt),
      stageMapAlg_succ n t hnt]
    exact congrArg (fun y => stageEmbed (t + 1) y) ih

/-- The native real `ModuleCat` diagram underlying the positive-depth
Cl(1,1) tensor tower. -/
def moduleDiagram : ℕ ⥤ ModuleCat ℝ where
  obj n := ModuleCat.of ℝ (Stage n)
  map {m n} f := ModuleCat.ofHom
    (stageMapAlg m n (leOfHom f)).toLinearMap
  map_id n := by
    apply ModuleCat.hom_ext
    change (stageMapAlg n n le_rfl).toLinearMap = LinearMap.id
    rw [stageMapAlg_refl]
    rfl
  map_comp {m n k} f g := by
    apply ModuleCat.hom_ext
    ext x
    change stageMapAlg m k (leOfHom (f ≫ g)) x =
      stageMapAlg n k (leOfHom g) (stageMapAlg m n (leOfHom f) x)
    simpa using
      (stageMapAlg_apply_trans m n k (leOfHom f) (leOfHom g) x)

/-! ## Stage-1 two-sheet atoms -/

/-- Sheet exchange on the distinguished first Cl(1,1) factor. -/
def etaBase : Stage 0 := gamma_0

/-- Positive local sheet projector. -/
def fPlusBase : Stage 0 := chiralProjPlus 1

/-- Negative local sheet projector. -/
def fMinusBase : Stage 0 := chiralProjMinus 1

@[simp] theorem etaBase_sq : etaBase * etaBase = (1 : Stage 0) := by
  ext i j
  rcases i with ⟨i0, i1⟩
  rcases j with ⟨j0, j1⟩
  fin_cases i0 <;> fin_cases j0 <;> fin_cases i1 <;> fin_cases j1 <;>
    norm_num [etaBase, gamma_0, TowerMatrix.kronPow, gamma_0_base,
      InfoGeometry.Clifford.Cl11Matrix.J1, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

@[simp] theorem fPlusBase_idempotent :
    fPlusBase * fPlusBase = fPlusBase := by
  ext i j
  rcases i with ⟨i0, i1⟩
  rcases j with ⟨j0, j1⟩
  fin_cases i0 <;> fin_cases j0 <;> fin_cases i1 <;> fin_cases j1 <;>
    norm_num [fPlusBase, chiralProjPlus, globalChirality,
      TowerMatrix.kronPow, gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

@[simp] theorem fMinusBase_idempotent :
    fMinusBase * fMinusBase = fMinusBase := by
  ext i j
  rcases i with ⟨i0, i1⟩
  rcases j with ⟨j0, j1⟩
  fin_cases i0 <;> fin_cases j0 <;> fin_cases i1 <;> fin_cases j1 <;>
    norm_num [fMinusBase, chiralProjMinus, globalChirality,
      TowerMatrix.kronPow, gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

@[simp] theorem fPlusBase_fMinusBase_zero :
    fPlusBase * fMinusBase = 0 := by
  ext i j
  rcases i with ⟨i0, i1⟩
  rcases j with ⟨j0, j1⟩
  fin_cases i0 <;> fin_cases j0 <;> fin_cases i1 <;> fin_cases j1 <;>
    norm_num [fPlusBase, fMinusBase, chiralProjPlus, chiralProjMinus,
      globalChirality, TowerMatrix.kronPow, gamma_chiral_base,
      gamma_0_base, gamma_1_base, InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

@[simp] theorem etaBase_fPlusBase_etaBase :
    etaBase * fPlusBase * etaBase = fMinusBase := by
  ext i j
  rcases i with ⟨i0, i1⟩
  rcases j with ⟨j0, j1⟩
  fin_cases i0 <;> fin_cases j0 <;> fin_cases i1 <;> fin_cases j1 <;>
    norm_num [etaBase, fPlusBase, fMinusBase, gamma_0,
      chiralProjPlus, chiralProjMinus, globalChirality,
      TowerMatrix.kronPow, gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-! ## Transported two-sheet elements -/

/-- The stagewise sheet exchange transported from the first Cl(1,1) factor. -/
def etaElem (n : ℕ) : Stage n :=
  stageMapAlg 0 n (Nat.zero_le n) etaBase

/-- Stagewise positive sheet projector. -/
def fPlusElem (n : ℕ) : Stage n :=
  stageMapAlg 0 n (Nat.zero_le n) fPlusBase

/-- Stagewise negative sheet projector. -/
def fMinusElem (n : ℕ) : Stage n :=
  stageMapAlg 0 n (Nat.zero_le n) fMinusBase

@[simp] theorem etaElem_sq (n : ℕ) :
    etaElem n * etaElem n = (1 : Stage n) := by
  rw [← map_mul, etaBase_sq, map_one]

@[simp] theorem fPlusElem_idempotent (n : ℕ) :
    fPlusElem n * fPlusElem n = fPlusElem n := by
  rw [← map_mul, fPlusBase_idempotent]

@[simp] theorem fMinusElem_idempotent (n : ℕ) :
    fMinusElem n * fMinusElem n = fMinusElem n := by
  rw [← map_mul, fMinusBase_idempotent]

@[simp] theorem fPlusElem_fMinusElem_zero (n : ℕ) :
    fPlusElem n * fMinusElem n = 0 := by
  rw [← map_mul, fPlusBase_fMinusBase_zero, map_zero]

@[simp] theorem etaElem_fPlusElem_etaElem (n : ℕ) :
    etaElem n * fPlusElem n * etaElem n = fMinusElem n := by
  rw [← map_mul, ← map_mul, etaBase_fPlusBase_etaBase]

/-- Existing tower transitions carry each Hestenes element to its next-stage
representative. -/
theorem stageMap_etaElem {m n : ℕ} (h : m ≤ n) :
    stageMapAlg m n h (etaElem m) = etaElem n := by
  unfold etaElem
  exact (stageMapAlg_apply_trans 0 m n (Nat.zero_le m) h etaBase).symm

theorem stageMap_fPlusElem {m n : ℕ} (h : m ≤ n) :
    stageMapAlg m n h (fPlusElem m) = fPlusElem n := by
  unfold fPlusElem
  exact (stageMapAlg_apply_trans 0 m n (Nat.zero_le m) h fPlusBase).symm

theorem stageMap_fMinusElem {m n : ℕ} (h : m ≤ n) :
    stageMapAlg m n h (fMinusElem m) = fMinusElem n := by
  unfold fMinusElem
  exact (stageMapAlg_apply_trans 0 m n (Nat.zero_le m) h fMinusBase).symm

/-- Left multiplication by a stage element as a real-linear endomorphism. -/
def leftMul {n : ℕ} (a : Stage n) : Module.End ℝ (Stage n) where
  toFun x := a * x
  map_add' x y := by simp [mul_add]
  map_smul' r x := by
    simp [Algebra.smul_def, mul_assoc, Algebra.commutes]

/-- Stagewise sheet-exchange natural transformation. -/
def etaNat : moduleDiagram ⟶ moduleDiagram where
  app n := ModuleCat.ofHom (leftMul (etaElem n))
  naturality := by
    intro m n f
    apply ModuleCat.hom_ext
    ext x
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    change stageMapAlg m n (leOfHom f) (etaElem m * x) =
      etaElem n * stageMapAlg m n (leOfHom f) x
    rw [map_mul, stageMap_etaElem]

/-- Positive-sheet projector natural transformation. -/
def fPlusNat : moduleDiagram ⟶ moduleDiagram where
  app n := ModuleCat.ofHom (leftMul (fPlusElem n))
  naturality := by
    intro m n f
    apply ModuleCat.hom_ext
    ext x
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    change stageMapAlg m n (leOfHom f) (fPlusElem m * x) =
      fPlusElem n * stageMapAlg m n (leOfHom f) x
    rw [map_mul, stageMap_fPlusElem]

/-- Negative-sheet projector natural transformation. -/
def fMinusNat : moduleDiagram ⟶ moduleDiagram where
  app n := ModuleCat.ofHom (leftMul (fMinusElem n))
  naturality := by
    intro m n f
    apply ModuleCat.hom_ext
    ext x
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
    change stageMapAlg m n (leOfHom f) (fMinusElem m * x) =
      fMinusElem n * stageMapAlg m n (leOfHom f) x
    rw [map_mul, stageMap_fMinusElem]

/-- Concrete instantiation of the finite-stage compatibility contract on the
native Cl(1,1) dyadic tower. -/
def finiteStageDatum :
    HestenesKreinFiniteStageCompatibility.Datum moduleDiagram where
  eta := etaNat
  fPlus := fPlusNat
  fMinus := fMinusNat
  eta_sq := by
    intro n
    ext x
    simp [etaNat, leftMul, etaElem_sq, mul_assoc]
  eta_fPlus_eta := by
    intro n
    ext x
    simp [etaNat, fPlusNat, fMinusNat, leftMul,
      etaElem_fPlusElem_etaElem, mul_assoc]
  fPlus_idempotent := by
    intro n
    ext x
    simp [fPlusNat, leftMul, fPlusElem_idempotent, mul_assoc]
  fMinus_idempotent := by
    intro n
    ext x
    simp [fMinusNat, leftMul, fMinusElem_idempotent, mul_assoc]
  fPlus_fMinus_zero := by
    intro n
    ext x
    simp [fPlusNat, fMinusNat, leftMul, fPlusElem_fMinusElem_zero,
      mul_assoc]

/-- The existing bilingual colimit descent specialized to the concrete Cl11
sheet projectors. -/
def bilingualDatum := finiteStageDatum.toBilingualDatum

/-- Categorical filtered-colimit carrier of the concrete real Cl11 module
diagram. -/
abbrev ColimitCarrier :=
  HestenesKreinBilingualFilteredColimitBridge.ColimitCarrier moduleDiagram

/-- The descended sheet-exchange endomorphism. -/
def colimitEta : Module.End ℝ ColimitCarrier :=
  (colim.map etaNat).hom

/-- Stage readback for the descended sheet exchange. -/
theorem colimitEta_on_stage (n : ℕ) (x : Stage n) :
    colimitEta ((colimit.ι moduleDiagram n).hom x) =
      (colimit.ι moduleDiagram n).hom (etaElem n * x) := by
  have h := colimit.ι_map etaNat n
  exact congrArg (fun f => f x) h

/-- The colimit sheet exchange remains an involution. -/
theorem colimitEta_sq :
    colimitEta * colimitEta = (1 : Module.End ℝ ColimitCarrier) := by
  apply LinearMap.ext
  intro y
  induction y using ModuleCat.FilteredColimits.inductionOn with
  | _ n x =>
      rw [Module.End.mul_apply, colimitEta_on_stage, colimitEta_on_stage]
      simp [etaElem_sq, mul_assoc]

/-- The two descended sheet projectors commute by the existing bilingual
filtered-colimit theorem. -/
theorem colimit_sheet_projectors_commute :
    leftColimit bilingualDatum * rightColimit bilingualDatum =
      rightColimit bilingualDatum * leftColimit bilingualDatum :=
  HestenesKreinFiniteStageCompatibility.Datum.colimit_sheet_projectors_commute
    finiteStageDatum

/-- Existing stage-readback theorem for the two descended projectors. -/
theorem colimit_sheet_stage_readback (n : ℕ) (x : Stage n) :
    ((leftColimit bilingualDatum) ((colimit.ι moduleDiagram n).hom x),
      (rightColimit bilingualDatum) ((colimit.ι moduleDiagram n).hom x)) =
      ((colimit.ι moduleDiagram n).hom (fPlusElem n * x),
        (colimit.ι moduleDiagram n).hom (fMinusElem n * x)) := by
  simpa [finiteStageDatum, fPlusNat, fMinusNat, leftMul] using
    HestenesKreinFiniteStageCompatibility.Datum.colimit_sheet_stage_readback
      finiteStageDatum n x

end InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
