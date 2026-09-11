import InfoGeometry.Algebra.KleinSpinorOrbit
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.SplitJordanSpinor
import Mathlib.Tactic

/-!
# Finite Klein spinor stabilizer socket lemmas

This file supplies concrete split-complex stabilizer equations related to the
weak `KleinSpinorOrbitStratification` boundary socket from `SplitJordanSpinor`.

Despite the historical theorem names below, these lemmas do **not** prove full
orbit classification/completeness or dimension counts.  They prove raw
coordinate stabilizer equivalences and explicit determinant-one stabilizer
families for the representatives already defined in `KleinSpinorOrbit.lean`.
-/

open InfoGeometry.Clifford.Arxiv160309063
open InfoGeometry.Algebra.KleinSpinorOrbit
open InfoGeometry.Algebra.SplitJordanSpinor

namespace InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure

/-- Generic representative `(1,0)` raw stabilizer equation for `C_s²`. -/
theorem generic_representative_complete_proved :
    ∀ (M : CsMatrix2), Stabilizes M genericRep ↔ M.aa = Cs.one ∧ M.ba = Cs.zero :=
  fun M => stabilizes_generic_iff M

/-- Null representative `(E,0)` raw stabilizer scalar equations for `C_s²`. -/
theorem null_representative_complete_proved :
    ∀ (M : CsMatrix2), Stabilizes M nullRep ↔ M.aa.re + M.aa.im = 1 ∧ M.ba.re + M.ba.im = 0 := by
  intro M
  have hiff := stabilizes_null_iff M
  constructor
  · intro hstab
    have ⟨ha, hb⟩ := hiff.mp hstab
    have hsum_aa := (Cs.mul_E_eq_E_iff M.aa).mp ha
    have hsum_ba := (Cs.mul_E_eq_zero_iff M.ba).mp hb
    exact ⟨hsum_aa, hsum_ba⟩
  · intro ⟨hsum_aa, hsum_ba⟩
    have ha := (Cs.mul_E_eq_E_iff M.aa).mpr hsum_aa
    have hb := (Cs.mul_E_eq_zero_iff M.ba).mpr hsum_ba
    exact hiff.mpr ⟨ha, hb⟩

/-- Explicit determinant-one upper-unipotent generic stabilizer family. -/
theorem generic_stabilizer_description_proved :
    ∀ (b : Cs.Cs), CsMatrix2.DetOne (CsMatrix2.genericUnipotent b) ∧
      Stabilizes (CsMatrix2.genericUnipotent b) genericRep :=
  genericUnipotent_stabilizes

/-- Explicit lower `Ebar` null stabilizer family. -/
theorem null_stabilizer_description_proved :
    ∀ (t : ℚ), Stabilizes (CsMatrix2.nullEbarFamily t) nullRep :=
  nullEbarFamily_stabilizes

end InfoGeometry.Algebra.KleinSpinorOrbitSocketClosure
