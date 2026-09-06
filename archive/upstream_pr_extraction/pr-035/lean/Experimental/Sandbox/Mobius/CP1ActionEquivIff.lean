import Experimental.Sandbox.Mobius.CP1ActionInverse

namespace Experimental.Sandbox.Mobius

lemma actCP1_reflects_equiv
    (M : InfoGeometry.MobiusTransform) {p q : InfoGeometry.CP1}
    (h : InfoGeometry.CP1.equiv (M.actCP1 p) (M.actCP1 q)) :
    InfoGeometry.CP1.equiv p q := by
  have hmid : InfoGeometry.CP1.equiv
      ((InfoGeometry.inv M).actCP1 (M.actCP1 p))
      ((InfoGeometry.inv M).actCP1 (M.actCP1 q)) :=
    actCP1_preserves_equiv (InfoGeometry.inv M) h
  have hp : InfoGeometry.CP1.equiv
      ((InfoGeometry.inv M).actCP1 (M.actCP1 p)) p :=
    inv_actCP1_after_actCP1_equiv M p
  have hq : InfoGeometry.CP1.equiv
      ((InfoGeometry.inv M).actCP1 (M.actCP1 q)) q :=
    inv_actCP1_after_actCP1_equiv M q
  exact cp1_equiv_trans (cp1_equiv_symm hp) (cp1_equiv_trans hmid hq)

lemma actCP1_equiv_iff
    (M : InfoGeometry.MobiusTransform) (p q : InfoGeometry.CP1) :
    InfoGeometry.CP1.equiv (M.actCP1 p) (M.actCP1 q) ↔
      InfoGeometry.CP1.equiv p q := by
  constructor
  · exact actCP1_reflects_equiv M
  · intro h
    exact actCP1_preserves_equiv M h

lemma actCP1_not_equiv_of_not_equiv
    (M : InfoGeometry.MobiusTransform) {p q : InfoGeometry.CP1}
    (h : ¬ InfoGeometry.CP1.equiv p q) :
    ¬ InfoGeometry.CP1.equiv (M.actCP1 p) (M.actCP1 q) := by
  intro hM
  exact h (actCP1_reflects_equiv M hM)

end Experimental.Sandbox.Mobius
