import InfoGeometry.Canonical.HestenesKreinFiniteStageCompatibility
import InfoGeometry.Clifford.Cl11MarkovJonesEngine
import InfoGeometry.Categorical.TwoSheetKreinFilteredColimit
import InfoGeometry.Clifford.SplitCliffordTransformKernel
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
open scoped Kronecker
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
    apply LinearMap.ext
    intro x
    change Stage m at x
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
  simpa [etaBase, gamma_0, InfoGeometry.Clifford.TowerMatrix.Jn] using
    (InfoGeometry.Clifford.TowerMatrix.Jn_sq gamma_0_base
      modularReflectionBase_sq 1)

@[simp] theorem fPlusBase_idempotent :
    fPlusBase * fPlusBase = fPlusBase := by
  have hΓ : globalChirality 1 * globalChirality 1 = (1 : Stage 0) := by
    simpa [globalChirality, InfoGeometry.Clifford.TowerMatrix.Jn] using
      (InfoGeometry.Clifford.TowerMatrix.Jn_sq gamma_chiral_base modularSignBase_sq 1)
  change InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus
      (globalChirality 1) *
      InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus
        (globalChirality 1) =
    InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus
      (globalChirality 1)
  exact
    (InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus_sq
      (globalChirality 1) hΓ)

@[simp] theorem fMinusBase_idempotent :
    fMinusBase * fMinusBase = fMinusBase := by
  have hΓ : globalChirality 1 * globalChirality 1 = (1 : Stage 0) := by
    simpa [globalChirality, InfoGeometry.Clifford.TowerMatrix.Jn] using
      (InfoGeometry.Clifford.TowerMatrix.Jn_sq gamma_chiral_base modularSignBase_sq 1)
  change InfoGeometry.Clifford.SplitCliffordTransformKernel.peirceMinus
      (globalChirality 1) *
      InfoGeometry.Clifford.SplitCliffordTransformKernel.peirceMinus
        (globalChirality 1) =
    InfoGeometry.Clifford.SplitCliffordTransformKernel.peirceMinus
      (globalChirality 1)
  exact
    (InfoGeometry.Clifford.SplitCliffordTransformKernel.peirceMinus_sq
      (globalChirality 1) hΓ)

@[simp] theorem fPlusBase_fMinusBase_zero :
    fPlusBase * fMinusBase = 0 := by
  have hΓ : globalChirality 1 * globalChirality 1 = (1 : Stage 0) := by
    simpa [globalChirality, InfoGeometry.Clifford.TowerMatrix.Jn] using
      (InfoGeometry.Clifford.TowerMatrix.Jn_sq gamma_chiral_base modularSignBase_sq 1)
  change InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus
      (globalChirality 1) *
      InfoGeometry.Clifford.SplitCliffordTransformKernel.peirceMinus
        (globalChirality 1) = 0
  exact
    (InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus_mul_minus
      (globalChirality 1) hΓ)

@[simp] theorem etaBase_fPlusBase_etaBase :
    etaBase * fPlusBase * etaBase = fMinusBase := by
  have hΓ : globalChirality 1 * globalChirality 1 = (1 : Stage 0) := by
    simpa [globalChirality, InfoGeometry.Clifford.TowerMatrix.Jn] using
      (InfoGeometry.Clifford.TowerMatrix.Jn_sq gamma_chiral_base modularSignBase_sq 1)
  have hanti : etaBase * globalChirality 1 = -(globalChirality 1 * etaBase) := by
    change ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ gamma_0_base) *
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ gamma_chiral_base) =
      -(((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ gamma_chiral_base) *
        ((1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ gamma_0_base))
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ =>
      (1 : Matrix (Fin 1) (Fin 1) ℝ) ⊗ₖ M)
      modularReflectionBase_modularSignBase_anticomm
    convert h using 1 <;>
      ext i j <;>
      simp [one_mul, modularReflectionBase, modularSignBase,
        gamma_chiral_base, Matrix.kroneckerMap, neg_mul, map_neg]
  have hconj : etaBase * globalChirality 1 * etaBase = -globalChirality 1 := by
    calc
      etaBase * globalChirality 1 * etaBase =
          -(globalChirality 1 * etaBase) * etaBase := by rw [hanti]
      _ = -((globalChirality 1 * etaBase) * etaBase) := by rw [neg_mul]
      _ = -(globalChirality 1 * (etaBase * etaBase)) := by
        exact congrArg Neg.neg (mul_assoc (globalChirality 1) etaBase etaBase)
      _ = -globalChirality 1 := by rw [etaBase_sq, mul_one]
  change etaBase *
      InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus
        (globalChirality 1) * etaBase =
    InfoGeometry.Clifford.SplitCliffordTransformKernel.peirceMinus
      (globalChirality 1)
  simp only [InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus,
    InfoGeometry.Clifford.SplitCliffordTransformKernel.peirceMinus,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub,
    smul_smul, one_smul, hconj]
  simp [sub_eq_add_neg, neg_smul]

theorem etaBase_fMinusBase_etaBase :
    etaBase * fMinusBase * etaBase = fPlusBase := by
  have hη : etaBase * etaBase = (1 : Stage 0) := etaBase_sq
  calc
    etaBase * fMinusBase * etaBase =
        etaBase * (etaBase * fPlusBase * etaBase) * etaBase := by
          rw [etaBase_fPlusBase_etaBase]
    _ = (etaBase * etaBase) * fPlusBase * (etaBase * etaBase) := by
          simp only [mul_assoc]
    _ = fPlusBase := by rw [hη, one_mul, mul_one]

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
  let φ := stageMapAlg 0 n (Nat.zero_le n)
  calc
    etaElem n * etaElem n = φ (etaBase * etaBase) := by
      exact (φ.map_mul etaBase etaBase).symm
    _ = φ 1 := by rw [etaBase_sq]
    _ = 1 := φ.map_one

@[simp] theorem fPlusElem_idempotent (n : ℕ) :
    fPlusElem n * fPlusElem n = fPlusElem n := by
  let φ := stageMapAlg 0 n (Nat.zero_le n)
  calc
    fPlusElem n * fPlusElem n = φ (fPlusBase * fPlusBase) := by
      exact (φ.map_mul fPlusBase fPlusBase).symm
    _ = φ fPlusBase := by rw [fPlusBase_idempotent]

@[simp] theorem fMinusElem_idempotent (n : ℕ) :
    fMinusElem n * fMinusElem n = fMinusElem n := by
  let φ := stageMapAlg 0 n (Nat.zero_le n)
  calc
    fMinusElem n * fMinusElem n = φ (fMinusBase * fMinusBase) := by
      exact (φ.map_mul fMinusBase fMinusBase).symm
    _ = φ fMinusBase := by rw [fMinusBase_idempotent]

@[simp] theorem fPlusElem_fMinusElem_zero (n : ℕ) :
    fPlusElem n * fMinusElem n = 0 := by
  let φ := stageMapAlg 0 n (Nat.zero_le n)
  calc
    fPlusElem n * fMinusElem n = φ (fPlusBase * fMinusBase) := by
      exact (φ.map_mul fPlusBase fMinusBase).symm
    _ = φ 0 := by rw [fPlusBase_fMinusBase_zero]
    _ = 0 := φ.map_zero

@[simp] theorem fPlusElem_add_fMinusElem (n : ℕ) :
    fPlusElem n + fMinusElem n = (1 : Stage n) := by
  let φ := stageMapAlg 0 n (Nat.zero_le n)
  calc
    fPlusElem n + fMinusElem n = φ (fPlusBase + fMinusBase) := by
      change φ fPlusBase + φ fMinusBase = φ (fPlusBase + fMinusBase)
      exact (φ.map_add fPlusBase fMinusBase).symm
    _ = φ 1 := by
      rw [show fPlusBase + fMinusBase = (1 : Stage 0) by
        change
          InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus
              (globalChirality 1) +
            InfoGeometry.Clifford.SplitCliffordTransformKernel.peirceMinus
              (globalChirality 1) = 1
        exact InfoGeometry.Clifford.SplitCliffordTransformKernel.peircePlus_add_minus _]
    _ = 1 := φ.map_one

@[simp] theorem fMinusElem_fPlusElem_zero (n : ℕ) :
    fMinusElem n * fPlusElem n = 0 := by
  have hsub : (1 : Stage n) - fPlusElem n = fMinusElem n := by
    rw [sub_eq_iff_eq_add]
    simpa [add_comm] using (fPlusElem_add_fMinusElem n).symm
  rw [← hsub, sub_mul, one_mul, fPlusElem_idempotent, sub_self]

theorem finite_peirce_decomposition (n : ℕ) (a : Stage n) :
    a = fPlusElem n * a * fPlusElem n +
      fPlusElem n * a * fMinusElem n +
      fMinusElem n * a * fPlusElem n +
      fMinusElem n * a * fMinusElem n := by
  have h := fPlusElem_add_fMinusElem n
  calc
    a = (fPlusElem n + fMinusElem n) * a *
        (fPlusElem n + fMinusElem n) := by rw [h, one_mul, mul_one]
    _ = fPlusElem n * a * fPlusElem n +
        fPlusElem n * a * fMinusElem n +
        fMinusElem n * a * fPlusElem n +
        fMinusElem n * a * fMinusElem n := by
      simp only [add_mul, mul_add]
      module

@[simp] theorem etaElem_fPlusElem_etaElem (n : ℕ) :
    etaElem n * fPlusElem n * etaElem n = fMinusElem n := by
  let φ := stageMapAlg 0 n (Nat.zero_le n)
  calc
    etaElem n * fPlusElem n * etaElem n =
        φ (etaBase * fPlusBase) * φ etaBase := by
      change φ etaBase * φ fPlusBase * φ etaBase =
        φ (etaBase * fPlusBase) * φ etaBase
      exact congrArg (fun z => z * φ etaBase)
        (φ.map_mul etaBase fPlusBase).symm
    _ = φ ((etaBase * fPlusBase) * etaBase) := by
      exact (φ.map_mul (etaBase * fPlusBase) etaBase).symm
    _ = φ fMinusBase := by rw [etaBase_fPlusBase_etaBase]

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

theorem etaElem_fMinusElem_etaElem (n : ℕ) :
    etaElem n * fMinusElem n * etaElem n = fPlusElem n := by
  let φ := stageMapAlg 0 n (Nat.zero_le n)
  calc
    etaElem n * fMinusElem n * etaElem n =
        φ (etaBase * fMinusBase) * φ etaBase := by
          change φ etaBase * φ fMinusBase * φ etaBase =
            φ (etaBase * fMinusBase) * φ etaBase
          exact congrArg (fun z => z * φ etaBase)
            (φ.map_mul etaBase fMinusBase).symm
    _ = φ ((etaBase * fMinusBase) * etaBase) := by
          exact (φ.map_mul (etaBase * fMinusBase) etaBase).symm
    _ = fPlusElem n := by
      rw [etaBase_fMinusBase_etaBase]
      change φ fPlusBase = φ fPlusBase
      rfl

/-- Left multiplication by a stage element as a real-linear endomorphism. -/
def leftMul {n : ℕ} (a : Stage n) :
    Module.End ℝ (↑(moduleDiagram.obj n)) where
  toFun x := by
    change Stage n at x
    exact a * x
  map_add' x y := by
    change Stage n at x y
    change a * (x + y) = a * x + a * y
    simp [mul_add]
  map_smul' r x := by
    change Stage n at x
    simp only [id_eq]
    change a * (r • x) = r • (a * x)
    simp only [Algebra.smul_def]
    calc
      a * ((algebraMap ℝ (Stage n) r) * x) =
          (a * algebraMap ℝ (Stage n) r) * x := by rw [mul_assoc]
      _ = (algebraMap ℝ (Stage n) r * a) * x := by
        rw [Algebra.commutes]
      _ = (algebraMap ℝ (Stage n) r) * (a * x) := by rw [mul_assoc]

/-- Stagewise sheet-exchange natural transformation. -/
def etaNat : moduleDiagram ⟶ moduleDiagram where
  app n := ModuleCat.ofHom (leftMul (etaElem n))
  naturality := by
    intro m n f
    ext x
    change Stage m at x
    dsimp [moduleDiagram, leftMul] at x ⊢
    change (etaElem n : Stage n) *
        (stageMapAlg m n (leOfHom f) (x : Stage m) : Stage n) =
      stageMapAlg m n (leOfHom f) (etaElem m * (x : Stage m))
    calc
      (etaElem n : Stage n) * stageMapAlg m n (leOfHom f) x =
          stageMapAlg m n (leOfHom f) (etaElem m) *
            stageMapAlg m n (leOfHom f) x := by rw [stageMap_etaElem]
      _ = stageMapAlg m n (leOfHom f) (etaElem m * x) := by
        exact (stageMapAlg m n (leOfHom f)).map_mul _ _ |>.symm

/-- Positive-sheet projector natural transformation. -/
def fPlusNat : moduleDiagram ⟶ moduleDiagram where
  app n := ModuleCat.ofHom (leftMul (fPlusElem n))
  naturality := by
    intro m n f
    ext x
    change Stage m at x
    dsimp [moduleDiagram, leftMul] at x ⊢
    change (fPlusElem n : Stage n) *
        (stageMapAlg m n (leOfHom f) (x : Stage m) : Stage n) =
      stageMapAlg m n (leOfHom f) (fPlusElem m * (x : Stage m))
    calc
      (fPlusElem n : Stage n) * stageMapAlg m n (leOfHom f) x =
          stageMapAlg m n (leOfHom f) (fPlusElem m) *
            stageMapAlg m n (leOfHom f) x := by rw [stageMap_fPlusElem]
      _ = stageMapAlg m n (leOfHom f) (fPlusElem m * x) := by
        exact (stageMapAlg m n (leOfHom f)).map_mul _ _ |>.symm

/-- Negative-sheet projector natural transformation. -/
def fMinusNat : moduleDiagram ⟶ moduleDiagram where
  app n := ModuleCat.ofHom (leftMul (fMinusElem n))
  naturality := by
    intro m n f
    ext x
    change Stage m at x
    dsimp [moduleDiagram, leftMul] at x ⊢
    change (fMinusElem n : Stage n) *
        (stageMapAlg m n (leOfHom f) (x : Stage m) : Stage n) =
      stageMapAlg m n (leOfHom f) (fMinusElem m * (x : Stage m))
    calc
      (fMinusElem n : Stage n) * stageMapAlg m n (leOfHom f) x =
          stageMapAlg m n (leOfHom f) (fMinusElem m) *
            stageMapAlg m n (leOfHom f) x := by rw [stageMap_fMinusElem]
      _ = stageMapAlg m n (leOfHom f) (fMinusElem m * x) := by
        exact (stageMapAlg m n (leOfHom f)).map_mul _ _ |>.symm

/-- Concrete instantiation of the finite-stage compatibility contract on the
native Cl(1,1) dyadic tower. -/
def finiteStageDatum :
    HestenesKreinFiniteStageCompatibility.Datum moduleDiagram where
  eta := etaNat
  fPlus := fPlusNat
  fMinus := fMinusNat
  eta_sq := by
    intro n
    apply LinearMap.ext
    intro x
    change Stage n at x
    change etaElem n * (etaElem n * (x : Stage n)) = (x : Stage n)
    rw [← mul_assoc, etaElem_sq, one_mul]
  eta_fPlus_eta := by
    intro n
    apply LinearMap.ext
    intro x
    change Stage n at x
    change etaElem n * (fPlusElem n * (etaElem n * (x : Stage n))) =
      fMinusElem n * (x : Stage n)
    rw [← mul_assoc, ← mul_assoc, etaElem_fPlusElem_etaElem]
  fPlus_idempotent := by
    intro n
    apply LinearMap.ext
    intro x
    change Stage n at x
    change fPlusElem n * (fPlusElem n * (x : Stage n)) = fPlusElem n * (x : Stage n)
    rw [← mul_assoc, fPlusElem_idempotent]
  fMinus_idempotent := by
    intro n
    apply LinearMap.ext
    intro x
    change Stage n at x
    change fMinusElem n * (fMinusElem n * (x : Stage n)) = fMinusElem n * (x : Stage n)
    rw [← mul_assoc, fMinusElem_idempotent]
  fPlus_fMinus_zero := by
    intro n
    apply LinearMap.ext
    intro x
    change Stage n at x
    change fPlusElem n * (fMinusElem n * (x : Stage n)) = 0
    rw [← mul_assoc, fPlusElem_fMinusElem_zero, zero_mul]

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
  have hη : etaNat ≫ etaNat = 𝟙 moduleDiagram := by
    ext n x
    change Stage n at x
    change etaElem n * (etaElem n * (x : Stage n)) = (x : Stage n)
    rw [← mul_assoc, etaElem_sq, one_mul]
  simpa [colimitEta, InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd]
    using InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd_involutive
      (F := moduleDiagram) etaNat hη

/-- The stagewise Krein exchange law is an equality of natural
transformations, hence descends through the existing categorical colimit. -/
theorem etaNat_fPlusNat_etaNat_eq_fMinusNat :
    etaNat ≫ fPlusNat ≫ etaNat = fMinusNat := by
  ext n x
  have h := congrArg
    (fun T : Module.End ℝ (Stage n) => T (x : Stage n))
    (finiteStageDatum.eta_fPlus_eta n)
  simpa [ModuleCat.comp_apply, etaNat, fPlusNat, fMinusNat, leftMul,
    Module.End.mul_apply] using h

/-- The descended Krein involution exchanges the positive sheet with the
negative sheet. -/
theorem colimitEta_fPlus_colimitEta_eq_fMinus :
    colimitEta * leftColimit bilingualDatum * colimitEta =
      rightColimit bilingualDatum := by
  simpa [colimitEta, leftColimit, rightColimit,
    InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd] using
    InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd_exchange
      etaNat fPlusNat fMinusNat etaNat_fPlusNat_etaNat_eq_fMinusNat

/-- The reverse stagewise exchange also descends through the filtered colimit. -/
theorem etaNat_fMinusNat_etaNat_eq_fPlusNat :
    etaNat ≫ fMinusNat ≫ etaNat = fPlusNat := by
  ext n x
  have h := congrArg
    (fun T : Module.End ℝ (Stage n) => T (x : Stage n))
    (finiteStageDatum.eta_fMinus_eta n)
  simpa [ModuleCat.comp_apply, etaNat, fPlusNat, fMinusNat, leftMul,
    Module.End.mul_apply] using h

/-- The descended Krein involution exchanges the negative sheet back with the
positive sheet. -/
theorem colimitEta_fMinus_colimitEta_eq_fPlus :
    colimitEta * rightColimit bilingualDatum * colimitEta =
      leftColimit bilingualDatum := by
  simpa [colimitEta, leftColimit, rightColimit,
    InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd] using
    InfoGeometry.Categorical.TwoSheetKreinFilteredColimit.colimitEnd_exchange
      etaNat fMinusNat fPlusNat etaNat_fMinusNat_etaNat_eq_fPlusNat

/-- Stage readback for the positive-sheet conjugation. -/
theorem colimitEta_leftColimit_on_stage (n : ℕ) (x : Stage n) :
    (colimitEta * leftColimit bilingualDatum * colimitEta)
        ((colimit.ι moduleDiagram n).hom x) =
      (colimit.ι moduleDiagram n).hom (fMinusElem n * x) := by
  rw [colimitEta_fPlus_colimitEta_eq_fMinus]
  exact rightColimit_on_stage bilingualDatum n x

/-- Stage readback for the negative-sheet conjugation. -/
theorem colimitEta_rightColimit_on_stage (n : ℕ) (x : Stage n) :
    (colimitEta * rightColimit bilingualDatum * colimitEta)
        ((colimit.ι moduleDiagram n).hom x) =
      (colimit.ι moduleDiagram n).hom (fPlusElem n * x) := by
  rw [colimitEta_fMinus_colimitEta_eq_fPlus]
  exact leftColimit_on_stage bilingualDatum n x


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

private theorem leftColimit_on_stage (n : ℕ) (x : Stage n) :
    (leftColimit bilingualDatum) ((colimit.ι moduleDiagram n).hom x) =
      (colimit.ι moduleDiagram n).hom (fPlusElem n * x) := by
  exact congrArg Prod.fst (colimit_sheet_stage_readback n x)

theorem colimit_left_idempotent :
    leftColimit bilingualDatum * leftColimit bilingualDatum =
      leftColimit bilingualDatum := by
  have hnat : fPlusNat ≫ fPlusNat = fPlusNat := by
    ext n x
    have h := congrArg
      (fun T : Module.End ℝ (Stage n) => T (x : Stage n))
      (finiteStageDatum.fPlus_idempotent n)
    simpa [ModuleCat.comp_apply, fPlusNat, leftMul, Module.End.mul_apply]
      using h
  have hcat :
      colim.map fPlusNat ≫ colim.map fPlusNat = colim.map fPlusNat := by
    rw [← colim.map_comp, hnat]
  simpa [leftColimit, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hcat

theorem colimit_right_idempotent :
    rightColimit bilingualDatum * rightColimit bilingualDatum =
      rightColimit bilingualDatum := by
  have hnat : fMinusNat ≫ fMinusNat = fMinusNat := by
    ext n x
    have h := congrArg
      (fun T : Module.End ℝ (Stage n) => T (x : Stage n))
      (finiteStageDatum.fMinus_idempotent n)
    simpa [ModuleCat.comp_apply, fMinusNat, leftMul, Module.End.mul_apply]
      using h
  have hcat :
      colim.map fMinusNat ≫ colim.map fMinusNat = colim.map fMinusNat := by
    rw [← colim.map_comp, hnat]
  simpa [rightColimit, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hcat

theorem colimit_left_right_zero :
    leftColimit bilingualDatum * rightColimit bilingualDatum = 0 := by
  have hnat : fMinusNat ≫ fPlusNat = 0 := by
    ext n x
    have h := congrArg
      (fun T : Module.End ℝ (Stage n) => T (x : Stage n))
      (finiteStageDatum.fPlus_fMinus_zero n)
    simpa [ModuleCat.comp_apply, fMinusNat, fPlusNat, leftMul,
      Module.End.mul_apply] using h
  have hcat :
      colim.map fMinusNat ≫ colim.map fPlusNat = 0 := by
    rw [← colim.map_comp, hnat, colim.map_zero]
  simpa [leftColimit, rightColimit, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hcat

theorem colimit_right_left_zero :
    rightColimit bilingualDatum * leftColimit bilingualDatum = 0 := by
  have hnat : fPlusNat ≫ fMinusNat = 0 := by
    ext n x
    have h := congrArg
      (fun T : Module.End ℝ (Stage n) => T (x : Stage n))
      (finiteStageDatum.fMinus_fPlus_zero n)
    simpa [ModuleCat.comp_apply, fPlusNat, fMinusNat, leftMul,
      Module.End.mul_apply] using h
  have hcat :
      colim.map fPlusNat ≫ colim.map fMinusNat = 0 := by
    rw [← colim.map_comp, hnat, colim.map_zero]
  simpa [rightColimit, leftColimit, Module.End.mul_apply] using
    congrArg ModuleCat.Hom.hom hcat

theorem colimit_sheet_projectors_sum :
    leftColimit bilingualDatum + rightColimit bilingualDatum =
      (1 : Module.End ℝ ColimitCarrier) := by
  have hnat : fPlusNat + fMinusNat = 𝟙 moduleDiagram := by
    ext n x
    change Stage n at x
    change fPlusElem n * x + fMinusElem n * x = x
    rw [← add_mul, fPlusElem_add_fMinusElem, one_mul]
  have hcat :
      colim.map fPlusNat + colim.map fMinusNat = 𝟙 _ := by
    rw [← colim.map_add, hnat, colim.map_id]
  simpa [leftColimit, rightColimit] using
    congrArg ModuleCat.Hom.hom hcat

end InfoGeometry.Canonical.Cl11HestenesKreinTwoSheetBridge
