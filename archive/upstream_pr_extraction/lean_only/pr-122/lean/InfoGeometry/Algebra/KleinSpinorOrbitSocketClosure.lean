import InfoGeometry.Algebra.KleinSpinorOrbit
import InfoGeometry.Algebra.SplitJordanSpinor
import Mathlib.Tactic

/-! Finite Klein-spinor stabilizer equations and explicit stabilizer families. -/

open InfoGeometry.Clifford.Arxiv160309063
open InfoGeometry.Algebra.KleinSpinorOrbit
open InfoGeometry.Algebra.SplitJordanSpinor

namespace InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure

theorem generic_representative_complete_proved :
    ∀ (M : CsMatrix2), Stabilizes M genericRep ↔
      M.aa = Cs.one ∧ M.ba = Cs.zero :=
  fun M => stabilizes_generic_iff M

theorem null_representative_complete_proved :
    ∀ (M : CsMatrix2), Stabilizes M nullRep ↔
      M.aa.re + M.aa.im = 1 ∧ M.ba.re + M.ba.im = 0 := by
  intro M
  have hiff := stabilizes_null_iff M
  constructor
  · intro hstab
    have ⟨ha, hb⟩ := hiff.mp hstab
    exact ⟨(Cs.mul_E_eq_E_iff M.aa).mp ha,
      (Cs.mul_E_eq_zero_iff M.ba).mp hb⟩
  · intro ⟨haa, hba⟩
    exact hiff.mpr ⟨(Cs.mul_E_eq_E_iff M.aa).mpr haa,
      (Cs.mul_E_eq_zero_iff M.ba).mpr hba⟩

theorem generic_stabilizer_description_proved :
    ∀ (b : Cs.Cs), CsMatrix2.DetOne (CsMatrix2.genericUnipotent b) ∧
      Stabilizes (CsMatrix2.genericUnipotent b) genericRep :=
  genericUnipotent_stabilizes

theorem null_stabilizer_description_proved :
    ∀ (t : ℚ), Stabilizes (CsMatrix2.nullEbarFamily t) nullRep :=
  nullEbarFamily_stabilizes

end InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure
