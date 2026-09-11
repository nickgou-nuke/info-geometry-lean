import InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.D6SixModeAction

/-!
# Klein sector labels and the native `G₂` coordinate-root carrier

The `Fin 2` coordinate records the two short/long root sectors and the
`ZMod 6` coordinate records the cyclic position.  The target is the existing
coordinate-root carrier; no new root enumeration is introduced.
-/

namespace InfoGeometry.Exceptional.G2KleinRootLabelBridge

open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Canonical.D6SixModeAction

abbrev KleinRootLabel := D6Index × Fin 2

def finTwoSector (b : Fin 2) : Bool := b = 1

noncomputable def kleinRootLabel (x : KleinRootLabel) : G2CoordinateRoot :=
  signedRootCyclotomicEquiv.symm (finTwoSector x.2, x.1)

def kleinRootLabelRotate (k : D6Index) (x : KleinRootLabel) :
    KleinRootLabel := (x.1 + k, x.2)

def kleinRootLabelReflect (x : KleinRootLabel) : KleinRootLabel :=
  (-x.1, x.2)

/-! The throat transition is a sheet flip, not the Weyl reflection above.
It keeps the cyclic position and exchanges the two sector labels. -/

def kleinRootLabelThroatFlipLabel (x : KleinRootLabel) : KleinRootLabel :=
  (x.1, 1 - x.2)

theorem kleinRootLabelThroatFlipLabel_involutive (x : KleinRootLabel) :
    kleinRootLabelThroatFlipLabel (kleinRootLabelThroatFlipLabel x) = x := by
  rcases x with ⟨k, b⟩
  simp [kleinRootLabelThroatFlipLabel]

theorem kleinRootLabelThroatFlip_position (x : KleinRootLabel) :
    (kleinRootLabelThroatFlipLabel x).1 = x.1 :=
  rfl

theorem kleinRootLabelThroatFlip_sector (x : KleinRootLabel) :
    (kleinRootLabelThroatFlipLabel x).2 = 1 - x.2 :=
  rfl

/-! The same throat transition, transported to the actual coordinate-root
carrier.  The cyclic label is fixed and only the two sheets are exchanged. -/

noncomputable def throatFlipFun (x : G2CoordinateRoot) : G2CoordinateRoot :=
  signedRootCyclotomicEquiv.symm
    (!((signedRootCyclotomicEquiv x).1), (signedRootCyclotomicEquiv x).2)

theorem throatFlipFun_involutive (x : G2CoordinateRoot) :
    throatFlipFun (throatFlipFun x) = x := by
  apply signedRootCyclotomicEquiv.injective
  simp [throatFlipFun]

noncomputable def kleinRootLabelThroatFlip : G2CoordinateRoot ≃ G2CoordinateRoot :=
  Equiv.ofBijective throatFlipFun ⟨
    (fun a b h => by
      rw [← throatFlipFun_involutive a, ← throatFlipFun_involutive b]
      exact congrArg throatFlipFun h),
    (fun y => ⟨throatFlipFun y, throatFlipFun_involutive y⟩)⟩

theorem kleinRootLabelThroatFlip_apply (x : G2CoordinateRoot) :
    kleinRootLabelThroatFlip x = signedRootCyclotomicEquiv.symm
      (!((signedRootCyclotomicEquiv x).1), (signedRootCyclotomicEquiv x).2) :=
  rfl

theorem kleinRootLabel_throatFlip_compatibility (x : KleinRootLabel) :
    kleinRootLabel (kleinRootLabelThroatFlipLabel x) =
      kleinRootLabelThroatFlip (kleinRootLabel x) := by
  rcases x with ⟨k, b⟩
  fin_cases b <;>
    simp [kleinRootLabel, kleinRootLabelThroatFlipLabel,
      kleinRootLabelThroatFlip_apply, finTwoSector]

theorem kleinRootLabelThroatFlip_involutive (x : G2CoordinateRoot) :
    kleinRootLabelThroatFlip (kleinRootLabelThroatFlip x) = x := by
  exact throatFlipFun_involutive x

noncomputable def cyclotomicSheetFlip : Root ≃ Root where
  toFun := fun x => (!x.1, x.2)
  invFun := fun x => (!x.1, x.2)
  left_inv x := by
    rcases x with ⟨b, k⟩
    cases b <;> rfl
  right_inv x := by
    rcases x with ⟨b, k⟩
    cases b <;> rfl

theorem cyclotomicSheetFlip_conjugates_s1 (x : Root) :
    cyclotomicSheetFlip (cyclotomicS1Perm x) =
      cyclotomicS2Perm (cyclotomicSheetFlip x) := by
  rcases x with ⟨b, k⟩
  cases b <;> rfl

theorem cyclotomicSheetFlip_conjugates_s2 (x : Root) :
    cyclotomicSheetFlip (cyclotomicS2Perm x) =
      cyclotomicS1Perm (cyclotomicSheetFlip x) := by
  rcases x with ⟨b, k⟩
  cases b <;> rfl

theorem kleinRootLabelThroatFlip_conjugates_s1 (x : G2CoordinateRoot) :
    kleinRootLabelThroatFlip (s1Root x) =
      s2Root (kleinRootLabelThroatFlip x) := by
  apply signedRootCyclotomicEquiv.injective
  change signedRootCyclotomicEquiv (throatFlipFun (s1Root x)) =
    signedRootCyclotomicEquiv (s2Root (throatFlipFun x))
  unfold throatFlipFun
  rw [signedRootCyclotomicEquiv_s1, signedRootCyclotomicEquiv_s2]
  simp only [Equiv.apply_symm_apply]
  change cyclotomicSheetFlip (cyclotomicS1Perm (signedRootCyclotomicEquiv x)) =
    cyclotomicS2Perm (cyclotomicSheetFlip (signedRootCyclotomicEquiv x))
  exact cyclotomicSheetFlip_conjugates_s1 _

theorem kleinRootLabelThroatFlip_conjugates_s2 (x : G2CoordinateRoot) :
    kleinRootLabelThroatFlip (s2Root x) =
      s1Root (kleinRootLabelThroatFlip x) := by
  apply signedRootCyclotomicEquiv.injective
  change signedRootCyclotomicEquiv (throatFlipFun (s2Root x)) =
    signedRootCyclotomicEquiv (s1Root (throatFlipFun x))
  unfold throatFlipFun
  rw [signedRootCyclotomicEquiv_s2, signedRootCyclotomicEquiv_s1]
  simp only [Equiv.apply_symm_apply]
  change cyclotomicSheetFlip (cyclotomicS2Perm (signedRootCyclotomicEquiv x)) =
    cyclotomicS1Perm (cyclotomicSheetFlip (signedRootCyclotomicEquiv x))
  exact cyclotomicSheetFlip_conjugates_s2 _

theorem kleinRootLabel_well_defined (x : KleinRootLabel) :
    kleinRootLabel x ∈ (Finset.univ : Finset G2CoordinateRoot) := by
  exact Finset.mem_univ _

theorem kleinRootLabel_rotate (k : D6Index) (x : KleinRootLabel) :
    signedRootCyclotomicEquiv (kleinRootLabel (kleinRootLabelRotate k x)) =
      InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.rotation k
        (signedRootCyclotomicEquiv (kleinRootLabel x)) := by
  simp [kleinRootLabel, kleinRootLabelRotate,
    InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.rotation]

theorem kleinRootLabel_reflect (x : KleinRootLabel) :
    signedRootCyclotomicEquiv (kleinRootLabel (kleinRootLabelReflect x)) =
      InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.reflection
        (signedRootCyclotomicEquiv (kleinRootLabel x)) := by
  simp [kleinRootLabel, kleinRootLabelReflect,
    InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.reflection]

theorem g2RootStar_kleinInvolution (x : KleinRootLabel) :
    kleinRootLabel (kleinRootLabelReflect (kleinRootLabelReflect x)) =
      kleinRootLabel x := by
  simp [kleinRootLabelReflect]

/-! A small V₄ shadow on the label carrier.  Its two generators are kept
    separate from the Weyl action: one reverses the cyclic coordinate and the
    other flips the two sheets at the throat. -/

abbrev KleinRootLabelV4 := Bool × Bool

def kleinRootLabelV4Action (g : KleinRootLabelV4) (x : KleinRootLabel) :
    KleinRootLabel :=
  (if g.1 then -x.1 else x.1,
    if g.2 then 1 - x.2 else x.2)

theorem kleinRootLabelV4Action_second_eq_throatFlip (x : KleinRootLabel) :
    kleinRootLabelV4Action (false, true) x =
      kleinRootLabelThroatFlipLabel x := by
  rfl

theorem g2RootStar_kleinV4_throat_compatibility (x : KleinRootLabel) :
    kleinRootLabel (kleinRootLabelV4Action (false, true) x) =
      kleinRootLabelThroatFlip (kleinRootLabel x) := by
  rw [kleinRootLabelV4Action_second_eq_throatFlip,
    kleinRootLabel_throatFlip_compatibility]

theorem kleinRootLabelV4Action_first_involutive (g : KleinRootLabelV4)
    (x : KleinRootLabel) :
    kleinRootLabelV4Action (g.1, false)
        (kleinRootLabelV4Action (g.1, false) x) = x := by
  rcases x with ⟨k, b⟩
  cases g.1 <;> simp [kleinRootLabelV4Action]

theorem kleinRootLabelV4Action_second_involutive (g : KleinRootLabelV4)
    (x : KleinRootLabel) :
    kleinRootLabelV4Action (false, g.2)
        (kleinRootLabelV4Action (false, g.2) x) = x := by
  rcases x with ⟨k, b⟩
  cases g.2 <;> simp [kleinRootLabelV4Action]

theorem kleinRootLabelV4Action_generators_commute
    (x : KleinRootLabel) :
    kleinRootLabelV4Action (true, false)
        (kleinRootLabelV4Action (false, true) x) =
      kleinRootLabelV4Action (false, true)
        (kleinRootLabelV4Action (true, false) x) := by
  rcases x with ⟨k, b⟩
  simp [kleinRootLabelV4Action]

theorem g2RootStar_kleinV4_generators_commute (x : KleinRootLabel) :
    kleinRootLabel
        (kleinRootLabelV4Action (true, false)
          (kleinRootLabelV4Action (false, true) x)) =
      kleinRootLabel
        (kleinRootLabelV4Action (false, true)
          (kleinRootLabelV4Action (true, false) x)) := by
  exact congrArg kleinRootLabel (kleinRootLabelV4Action_generators_commute x)

end InfoGeometry.Exceptional.G2KleinRootLabelBridge
