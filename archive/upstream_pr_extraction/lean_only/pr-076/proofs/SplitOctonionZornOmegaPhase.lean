import proofs.SplitOctonionSixSectorBridge

/-!
# Quartic sheet phase inside the complex Zorn carrier

All products are explicitly parenthesized.  The conjugation action below means
`(Ωχ * lane) * Ωχ⁻¹`; no associativity of the ambient split-octonion product is
used or asserted.
-/

noncomputable section
namespace SplitOctonionZornOmegaPhase

open SplitOctonionChiralClosure
open SplitOctonionCircularChiralClosure

/-- Complex quarter-phase attached to the two Peirce poles. -/
def omegaChi : SplitOctonionChiralClosure.Zorn := add uP (smul Complex.I uM)

/-- Its inverse in the associative diagonal Peirce subalgebra. -/
def omegaChiInv : SplitOctonionChiralClosure.Zorn :=
  add uP (smul (-Complex.I) uM)

theorem omegaZornExt {X Y : SplitOctonionChiralClosure.Zorn}
    (ha : X.a = Y.a) (hu : X.u = Y.u)
    (hv : X.v = Y.v) (hb : X.b = Y.b) : X = Y :=
  SplitOctonionBraidSU3.zorn_ext ha hu hv hb

macro "omega_zorn_coords" : tactic =>
  `(tactic| (apply omegaZornExt <;>
    simp [omegaChi, omegaChiInv, mul, add, sub, smul, uP, uM, sP, sM,
      uPlus, uMinus, sigmaPlus, sigmaMinus, kreinParity, ell, one,
      SplitOctonionBraidSU3.zornMul, SplitOctonionBraidSU3.zornAdd,
      SplitOctonionBraidSU3.zornSub, SplitOctonionBraidSU3.zornSmul,
      SplitOctonionBraidSU3.ell,
      SplitOctonionBraidSU3.dot3, SplitOctonionBraidSU3.cross3] <;>
    try funext i <;> try fin_cases i <;> simp <;> ring))

theorem omegaChi_sq : mul omegaChi omegaChi = parity := by
  omega_zorn_coords

theorem omegaChi_four :
    mul (mul omegaChi omegaChi) (mul omegaChi omegaChi) = unit := by
  omega_zorn_coords

theorem omegaChi_mul_inv : mul omegaChi omegaChiInv = unit := by
  omega_zorn_coords

theorem omegaChi_inv_mul : mul omegaChiInv omegaChi = unit := by
  omega_zorn_coords

/-- Positive lanes acquire the negative quarter phase. -/
theorem omegaChi_conjugates_plus (u : SplitOctonionChiralClosure.Vec3) :
    mul (mul omegaChi (sP u)) omegaChiInv = smul (-Complex.I) (sP u) := by
  omega_zorn_coords

/-- Negative lanes acquire the positive quarter phase. -/
theorem omegaChi_conjugates_minus (u : SplitOctonionChiralClosure.Vec3) :
    mul (mul omegaChi (sM u)) omegaChiInv = smul Complex.I (sM u) := by
  omega_zorn_coords

theorem omegaChi_conjugates_six_directions
    (a : SplitOctonionSixSectorBridge.Color3) :
    mul (mul omegaChi (SplitOctonionSixSectorBridge.plusLane a)) omegaChiInv =
        smul (-Complex.I) (SplitOctonionSixSectorBridge.plusLane a) ∧
    mul (mul omegaChi (SplitOctonionSixSectorBridge.minusLane a)) omegaChiInv =
        smul Complex.I (SplitOctonionSixSectorBridge.minusLane a) :=
  ⟨omegaChi_conjugates_plus _, omegaChi_conjugates_minus _⟩

theorem zorn_quartic_sheet_phase_packet :
    mul omegaChi omegaChi = parity ∧
    mul parity parity = unit ∧
    mul omegaChi omegaChiInv = unit ∧
    mul omegaChiInv omegaChi = unit ∧
    (∀ u, mul (mul omegaChi (sP u)) omegaChiInv =
      smul (-Complex.I) (sP u)) ∧
    (∀ u, mul (mul omegaChi (sM u)) omegaChiInv =
      smul Complex.I (sM u)) := by
  refine ⟨omegaChi_sq, ?_, omegaChi_mul_inv, omegaChi_inv_mul,
    omegaChi_conjugates_plus, omegaChi_conjugates_minus⟩
  omega_zorn_coords

end SplitOctonionZornOmegaPhase
end noncomputable section
