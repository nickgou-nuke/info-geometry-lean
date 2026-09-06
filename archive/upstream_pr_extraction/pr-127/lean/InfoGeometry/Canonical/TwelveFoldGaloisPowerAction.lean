import InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets
import InfoGeometry.Canonical.TwelveFoldExplicitOperators

/-!
# The finite Galois power dictionary for the twelvefold operator

The coefficient-field automorphism is represented here only by its induced
power on the cyclic exponent group.  The statements below transport that
arithmetic to the already constructed matrix powers; they do not assert a
semilinear action on `Mat23C`.
-/

namespace InfoGeometry.Canonical.TwelveFoldGaloisPowerAction

open InfoGeometry.Canonical.TwelveFoldExplicitOperators
open InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets
open InfoGeometry.Canonical.TwoSheetThreeColorWeyl

noncomputable section

def transportedMasterPower (u : C12ˣ) (k : C12) :
    TwelveFoldExplicitOperators.Mat23C :=
  masterTwelve ^ (galoisPower u k).val

theorem sigma5_transports_quartic_generator :
    transportedMasterPower sigma5 3 = omegaHat := by
  dsimp [transportedMasterPower]
  rw [sigma5_fixes_quartic_exponent]
  exact masterTwelve_cube

theorem sigma5_transports_colour_generator :
    transportedMasterPower sigma5 8 = masterTwelve ^ 4 := by
  dsimp [transportedMasterPower]
  rw [sigma5_inverts_colour_exponent]
  rw [show ZMod.val (4 : C12) = 4 by decide]

theorem sigma5_transports_triality_generator :
    transportedMasterPower sigma5 2 = masterTwelve ^ 10 := by
  dsimp [transportedMasterPower]
  rw [sigma5_inverts_triality_exponent]
  rw [show ZMod.val (10 : C12) = 10 by decide]

theorem sigma7_transports_quartic_generator :
    transportedMasterPower sigma7 3 = masterTwelve ^ 9 := by
  dsimp [transportedMasterPower]
  rw [sigma7_inverts_quartic_exponent]
  rw [show ZMod.val (9 : C12) = 9 by decide]

theorem sigma7_fixes_colour_generator :
    transportedMasterPower sigma7 8 = sixShift := by
  dsimp [transportedMasterPower]
  rw [sigma7_fixes_colour_exponent]
  rw [show ZMod.val (8 : C12) = 8 by decide]
  exact masterTwelve_eight

theorem sigma7_fixes_triality_generator :
    transportedMasterPower sigma7 2 = sixTriality := by
  dsimp [transportedMasterPower]
  rw [sigma7_fixes_triality_exponent]
  rw [show ZMod.val (2 : C12) = 2 by decide]
  exact masterTwelve_sq

theorem sigma11_transports_quartic_generator :
    transportedMasterPower sigma11 3 = masterTwelve ^ 9 := by
  dsimp [transportedMasterPower]
  rw [sigma11_inverts_quartic_exponent]
  rw [show ZMod.val (9 : C12) = 9 by decide]

theorem sigma11_transports_colour_generator :
    transportedMasterPower sigma11 8 = masterTwelve ^ 4 := by
  dsimp [transportedMasterPower]
  rw [sigma11_inverts_colour_exponent]
  rw [show ZMod.val (4 : C12) = 4 by decide]

theorem sigma11_transports_triality_generator :
    transportedMasterPower sigma11 2 = masterTwelve ^ 10 := by
  dsimp [transportedMasterPower]
  rw [sigma11_inverts_triality_exponent]
  rw [show ZMod.val (10 : C12) = 10 by decide]

theorem every_galois_unit_transports_parity :
    ∀ u : C12ˣ, transportedMasterPower u 6 = sixParity := by
  intro u
  dsimp [transportedMasterPower]
  rw [every_galois_unit_fixes_parity_exponent]
  rw [show ZMod.val (6 : C12) = 6 by decide]
  exact masterTwelve_six

end
end InfoGeometry.Canonical.TwelveFoldGaloisPowerAction
