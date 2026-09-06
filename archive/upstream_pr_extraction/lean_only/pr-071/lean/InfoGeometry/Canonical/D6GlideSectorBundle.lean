import InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
import InfoGeometry.Canonical.D6SixModeAction

/-!
# The six-sector D6 family of finite Klein quotients

The full `D6` action permutes six glide sectors.  Each sector has the genuine
finite Klein quotient from `D6HexTiledKleinBottleQuotient`; the construction
does not identify one fixed fiber with a full `D6`-invariant Klein quotient.
-/

namespace InfoGeometry.Canonical.D6GlideSectorBundle

open InfoGeometry.Canonical.D6SixModeAction
open InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient

abbrev SectorPoint := D6Index × TorusCell

def sectorRel (p q : SectorPoint) : Prop :=
  p.1 = q.1 ∧ kleinOrbitRel p.2 q.2

theorem sectorRel_refl (p : SectorPoint) : sectorRel p p := by
  exact ⟨rfl, kleinOrbitRel_refl _⟩

theorem sectorRel_symm {p q : SectorPoint} :
    sectorRel p q → sectorRel q p := by
  rintro ⟨hs, hq⟩
  exact ⟨hs.symm, kleinOrbitRel_symm hq⟩

theorem sectorRel_trans {p q r : SectorPoint} :
    sectorRel p q → sectorRel q r → sectorRel p r := by
  rintro ⟨hpq, hqr⟩ ⟨hqr', hrr⟩
  exact ⟨hpq.trans hqr', kleinOrbitRel_trans hqr hrr⟩

instance sectorSetoid : Setoid SectorPoint where
  r := sectorRel
  iseqv :=
    { refl := sectorRel_refl
      symm := sectorRel_symm
      trans := sectorRel_trans }

abbrev D6KleinSectorBundle := Quotient sectorSetoid

noncomputable instance sectorRelDecidable : DecidableRel sectorRel :=
  Classical.decRel _

noncomputable instance sectorBundleFintype : Fintype D6KleinSectorBundle :=
  by
    classical
    exact Quotient.fintype sectorSetoid

theorem sectorBundle_card_le :
    Fintype.card D6KleinSectorBundle ≤ Fintype.card SectorPoint := by
  letI : DecidableRel ((· ≈ ·) : SectorPoint → SectorPoint → Prop) :=
    Classical.decRel _
  simpa only [D6KleinSectorBundle] using
    (Fintype.card_quotient_le sectorSetoid)

theorem sectorBundle_card_pos : 0 < Fintype.card D6KleinSectorBundle := by
  exact Fintype.card_pos_iff.mpr inferInstance

def sectorMap (s : D6Index) (p : TorusCell) : D6KleinSectorBundle :=
  Quotient.mk' (s, p)

instance sectorBundleNonempty : Nonempty D6KleinSectorBundle :=
  ⟨sectorMap 0 (0, 0)⟩

def sectorRotate (k : D6Index) (p : SectorPoint) : SectorPoint :=
  (p.1 + k, p.2)

def sectorReflect (p : SectorPoint) : SectorPoint :=
  (-p.1, p.2)

theorem sectorRotate_respects (k : D6Index) {p q : SectorPoint} :
    sectorRel p q → sectorRel (sectorRotate k p) (sectorRotate k q) := by
  rintro ⟨hs, hq⟩
  exact ⟨by simpa [sectorRotate] using congrArg (fun x => x + k) hs,
    hq⟩

theorem sectorReflect_respects {p q : SectorPoint} :
    sectorRel p q → sectorRel (sectorReflect p) (sectorReflect q) := by
  rintro ⟨hs, hq⟩
  exact ⟨by simpa [sectorReflect] using congrArg Neg.neg hs,
    hq⟩

def quotientSectorRotate (k : D6Index) : D6KleinSectorBundle → D6KleinSectorBundle :=
  Quotient.map (sectorRotate k) (fun _ _ h => sectorRotate_respects k h)

def quotientSectorReflect : D6KleinSectorBundle → D6KleinSectorBundle :=
  Quotient.map sectorReflect (fun _ _ h => sectorReflect_respects h)

theorem sectorMap_glide (s : D6Index) (p : TorusCell) :
    sectorMap s (glide p) = sectorMap s p := by
  apply Quotient.sound
  exact ⟨rfl, kleinOrbitRel_symm (Or.inr (Or.inl rfl))⟩

theorem quotientSectorRotate_glide (k s : D6Index) (p : TorusCell) :
    quotientSectorRotate k (sectorMap s (glide p)) =
      quotientSectorRotate k (sectorMap s p) := by
  rw [sectorMap_glide]

theorem quotientSectorReflect_glide (s : D6Index) (p : TorusCell) :
    quotientSectorReflect (sectorMap s (glide p)) =
      quotientSectorReflect (sectorMap s p) := by
  rw [sectorMap_glide]

theorem quotientSectorRotate_map (k s : D6Index) (p : TorusCell) :
    quotientSectorRotate k (sectorMap s p) = sectorMap (s + k) p := rfl

theorem quotientSectorReflect_map (s : D6Index) (p : TorusCell) :
    quotientSectorReflect (sectorMap s p) = sectorMap (-s) p := rfl

theorem quotientSectorRotate_add
    (k l : D6Index) (q : D6KleinSectorBundle) :
    quotientSectorRotate (k + l) q =
      quotientSectorRotate l (quotientSectorRotate k q) := by
  refine Quotient.inductionOn q ?_
  intro p
  rcases p with ⟨s, p⟩
  simp [quotientSectorRotate, sectorRotate, add_assoc]

theorem quotientSectorReflect_involutive (q : D6KleinSectorBundle) :
    quotientSectorReflect (quotientSectorReflect q) = q := by
  refine Quotient.inductionOn q ?_
  intro p
  rcases p with ⟨s, p⟩
  simp [quotientSectorReflect, sectorReflect]

theorem quotientSectorReflect_conjugates_rotate (k : D6Index)
    (q : D6KleinSectorBundle) :
    quotientSectorReflect (quotientSectorRotate k
      (quotientSectorReflect q)) =
      quotientSectorRotate (-k) q := by
  refine Quotient.inductionOn q ?_
  intro p
  rcases p with ⟨s, p⟩
  simp [quotientSectorReflect, quotientSectorRotate, sectorReflect,
    sectorRotate, add_comm]

theorem quotientSectorRotate_zero (q : D6KleinSectorBundle) :
    quotientSectorRotate 0 q = q := by
  refine Quotient.inductionOn q ?_
  intro p
  simp [quotientSectorRotate, sectorRotate]

def quotientSectorRotateEquiv (k : D6Index) :
    D6KleinSectorBundle ≃ D6KleinSectorBundle where
  toFun := quotientSectorRotate k
  invFun := quotientSectorRotate (-k)
  left_inv := by
    intro q
    rw [← quotientSectorRotate_add k (-k) q]
    simp [quotientSectorRotate_zero]
  right_inv := by
    intro q
    rw [← quotientSectorRotate_add (-k) k q]
    simp [quotientSectorRotate_zero]

def quotientSectorReflectEquiv :
    D6KleinSectorBundle ≃ D6KleinSectorBundle where
  toFun := quotientSectorReflect
  invFun := quotientSectorReflect
  left_inv := quotientSectorReflect_involutive
  right_inv := quotientSectorReflect_involutive

end InfoGeometry.Canonical.D6GlideSectorBundle
