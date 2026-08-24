import InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge

/-!
# Finite-stage Hestenes/Krein sheet compatibility for filtered module diagrams

This owner does not choose a filtered tower.  Instead it records the exact
finite-stage structure that any concrete diagram `F : ℕ ⥤ ModuleCat ℝ` must
preserve before the existing bilingual filtered-colimit bridge can be used.

The stage operators are natural transformations

* `eta`    — sheet-exchange/Krein involution;
* `fPlus`  — positive-sheet projector;
* `fMinus` — negative-sheet projector.

Naturality is the transition-map compatibility.  The pointwise algebraic laws
are

`eta² = 1`, `eta fPlus eta = fMinus`, `fPlus² = fPlus`,
`fMinus² = fMinus`, and `fPlus fMinus = 0`.

The reverse orthogonality `fMinus fPlus = 0` is derived, not stored.  Hence the
two sheet projectors commute and instantiate the already-existing
`HestenesKreinBilingualFilteredColimitBridge.Datum` without introducing a new
colimit construction.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinFiniteStageCompatibility

open CategoryTheory
open InfoGeometry.Canonical.HestenesKreinBilingualFilteredColimitBridge

variable {F : ℕ ⥤ ModuleCat ℝ}

/-- Finite-stage Hestenes sheet data compatible with every transition map of
`F`.  Compatibility is encoded natively by naturality of the three natural
transformations. -/
structure Datum (F : ℕ ⥤ ModuleCat ℝ) where
  eta : F ⟶ F
  fPlus : F ⟶ F
  fMinus : F ⟶ F
  eta_sq : ∀ j : ℕ,
    (eta.app j).hom * (eta.app j).hom = 1
  eta_fPlus_eta : ∀ j : ℕ,
    (eta.app j).hom * (fPlus.app j).hom * (eta.app j).hom =
      (fMinus.app j).hom
  fPlus_idempotent : ∀ j : ℕ,
    (fPlus.app j).hom * (fPlus.app j).hom = (fPlus.app j).hom
  fMinus_idempotent : ∀ j : ℕ,
    (fMinus.app j).hom * (fMinus.app j).hom = (fMinus.app j).hom
  fPlus_fMinus_zero : ∀ j : ℕ,
    (fPlus.app j).hom * (fMinus.app j).hom = 0

namespace Datum

variable (D : Datum F)

/-- Naturality of `eta` is exactly preservation of the sheet involution by a
transition morphism. -/
theorem eta_transition {j k : ℕ} (f : j ⟶ k) :
    F.map f ≫ D.eta.app k = D.eta.app j ≫ F.map f :=
  D.eta.naturality f

/-- Naturality of the positive-sheet projector. -/
theorem fPlus_transition {j k : ℕ} (f : j ⟶ k) :
    F.map f ≫ D.fPlus.app k = D.fPlus.app j ≫ F.map f :=
  D.fPlus.naturality f

/-- Naturality of the negative-sheet projector. -/
theorem fMinus_transition {j k : ℕ} (f : j ⟶ k) :
    F.map f ≫ D.fMinus.app k = D.fMinus.app j ≫ F.map f :=
  D.fMinus.naturality f

/-- Conjugation by the involution also sends the negative projector back to
the positive projector. -/
theorem eta_fMinus_eta (j : ℕ) :
    (D.eta.app j).hom * (D.fMinus.app j).hom * (D.eta.app j).hom =
      (D.fPlus.app j).hom := by
  let e : Module.End ℝ (F.obj j) := (D.eta.app j).hom
  let p : Module.End ℝ (F.obj j) := (D.fPlus.app j).hom
  let m : Module.End ℝ (F.obj j) := (D.fMinus.app j).hom
  have he : e * e = 1 := D.eta_sq j
  have hswap : e * p * e = m := D.eta_fPlus_eta j
  calc
    e * m * e = e * (e * p * e) * e := by rw [hswap]
    _ = (e * e) * p * (e * e) := by simp only [mul_assoc]
    _ = p := by rw [he, one_mul, mul_one]

/-- The unstored reverse orthogonality follows from sheet exchange and
`fPlus fMinus = 0`. -/
theorem fMinus_fPlus_zero (j : ℕ) :
    (D.fMinus.app j).hom * (D.fPlus.app j).hom = 0 := by
  let e : Module.End ℝ (F.obj j) := (D.eta.app j).hom
  let p : Module.End ℝ (F.obj j) := (D.fPlus.app j).hom
  let m : Module.End ℝ (F.obj j) := (D.fMinus.app j).hom
  have he : e * e = 1 := D.eta_sq j
  have hswap : e * p * e = m := D.eta_fPlus_eta j
  have hpm : p * m = 0 := D.fPlus_fMinus_zero j
  have hep : e * p = m * e := by
    calc
      e * p = (e * p) * 1 := by rw [mul_one]
      _ = (e * p) * (e * e) := by rw [he]
      _ = (e * p * e) * e := by simp only [mul_assoc]
      _ = m * e := by rw [hswap]
  calc
    m * p = (e * p * e) * p := by rw [hswap]
    _ = e * p * (e * p) := by simp only [mul_assoc]
    _ = e * p * (m * e) := by rw [hep]
    _ = e * (p * m) * e := by simp only [mul_assoc]
    _ = 0 := by rw [hpm, mul_zero, zero_mul]

/-- The two sheet projectors commute pointwise; in fact both mixed products
vanish. -/
theorem sheet_projectors_commute (j : ℕ) :
    (D.fPlus.app j).hom * (D.fMinus.app j).hom =
      (D.fMinus.app j).hom * (D.fPlus.app j).hom := by
  rw [D.fPlus_fMinus_zero j, D.fMinus_fPlus_zero j]

/-- The finite-stage sheet data instantiate the already existing bilingual
filtered-colimit bridge.  No new colimit carrier or descent construction is
introduced here. -/
def toBilingualDatum :
    HestenesKreinBilingualFilteredColimitBridge.Datum (F := F) where
  left := D.fPlus
  right := D.fMinus
  commute := by
    ext j
    apply ModuleCat.hom_ext
    ext x
    have hpm := congrArg
      (fun T : Module.End ℝ (F.obj j) => T x)
      (D.fPlus_fMinus_zero j)
    have hmp := congrArg
      (fun T : Module.End ℝ (F.obj j) => T x)
      (D.fMinus_fPlus_zero j)
    simpa [ModuleCat.comp_apply, Module.End.mul_apply] using hmp.trans hpm.symm

/-- Colimit-level left/right commutation is inherited from the existing
bilingual filtered-colimit owner after finite-stage compatibility has been
supplied. -/
theorem colimit_sheet_projectors_commute :
    leftColimit D.toBilingualDatum * rightColimit D.toBilingualDatum =
      rightColimit D.toBilingualDatum * leftColimit D.toBilingualDatum :=
  colimit_left_right_commute D.toBilingualDatum

/-- Stage readback for the descended sheet projectors is exactly the existing
bilingual stage-readback theorem. -/
theorem colimit_sheet_stage_readback (j : ℕ) (x : F.obj j) :
    ((leftColimit D.toBilingualDatum) ((CategoryTheory.Limits.colimit.ι F j).hom x),
      (rightColimit D.toBilingualDatum) ((CategoryTheory.Limits.colimit.ι F j).hom x)) =
      ((CategoryTheory.Limits.colimit.ι F j).hom ((D.fPlus.app j).hom x),
        (CategoryTheory.Limits.colimit.ι F j).hom ((D.fMinus.app j).hom x)) :=
  colimit_bilingual_stage_readback D.toBilingualDatum j x

end Datum

end InfoGeometry.Canonical.HestenesKreinFiniteStageCompatibility
