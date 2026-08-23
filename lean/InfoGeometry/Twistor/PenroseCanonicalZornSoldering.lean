import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import InfoGeometry.Twistor.PenroseTwistor
import InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

/-!
# Penrose realification to the canonical circular Zorn carrier

This is a carrier soldering only.  The realification of `Fin 4 → ℂ` is put in
the repository's established circular Peirce coordinates and then transported
through its native basis equivalence to the canonical Zorn carrier.  No norm
or multiplication compatibility is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.PenroseCanonicalZornSoldering

open InfoGeometry.Twistor.PenroseTwistor
open InfoGeometry.Lie.SplitOctonionCircularPeirceBasis

abbrev RealPeirceCarrier := Fin 8 → ℝ
abbrev CanonicalZorn := CZ

noncomputable def penroseRealPeirceEquiv :
    TwistorCarrier ≃ₗ[ℝ] RealPeirceCarrier where
  toFun z := ![(z 0).re, (z 1).re, (z 2).re, (z 3).re,
    (z 0).im, (z 1).im, (z 2).im, (z 3).im]
  invFun x := fun i =>
    ⟨x ⟨i.val, by omega⟩, x ⟨i.val + 4, by omega⟩⟩
  left_inv := by
    intro z
    funext i
    apply Complex.ext
    · fin_cases i <;> simp
    · fin_cases i <;> simp
  right_inv := by
    intro x
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro z w
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro r z
    funext i
    fin_cases i <;> simp

noncomputable def penroseCanonicalZornEquiv :
    TwistorCarrier ≃ₗ[ℝ] CanonicalZorn :=
  penroseRealPeirceEquiv.trans circularPeirceBasis.equivFun.symm

@[simp] theorem penroseRealPeirceEquiv_apply (z : TwistorCarrier) :
    penroseRealPeirceEquiv z =
      ![(z 0).re, (z 1).re, (z 2).re, (z 3).re,
        (z 0).im, (z 1).im, (z 2).im, (z 3).im] := rfl

@[simp] theorem penroseCanonicalZornEquiv_circularBasis (i : Fin 8) :
    penroseCanonicalZornEquiv
        (penroseRealPeirceEquiv.symm (Pi.single i 1)) =
      circularPeirceBasis i := by
  unfold penroseCanonicalZornEquiv
  simp

theorem penroseCanonicalZornEquiv_readback (z : TwistorCarrier) :
    penroseRealPeirceEquiv.symm
        (circularPeirceBasis.equivFun (penroseCanonicalZornEquiv z)) = z := by
  change penroseRealPeirceEquiv.symm
      (circularPeirceBasis.equivFun
        (penroseRealPeirceEquiv.trans circularPeirceBasis.equivFun.symm z)) = z
  rw [LinearEquiv.trans_apply, circularPeirceBasis.equivFun.apply_symm_apply]
  exact penroseRealPeirceEquiv.symm_apply_apply z

end InfoGeometry.Twistor.PenroseCanonicalZornSoldering
