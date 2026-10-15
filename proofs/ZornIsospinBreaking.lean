import Mathlib
import proofs.FureyZornFermionBridge
import proofs.ZornAssociatorSplitOctonion

noncomputable section
namespace ZornIsospinBreaking

open FureyZornFermionBridge

/-- A model label for the upper diagonal idempotent; no particle-state
identification is part of this definition. -/
def ProtonProjector : ZornOPParavector.Zorn := leptonProjectorPlus
/-- A model label for the lower diagonal idempotent; no particle-state
identification is part of this definition. -/
def NeutronProjector : ZornOPParavector.Zorn := leptonProjectorMinus

/-- 
The symbol `TPlus` names the upper triplet lane in this finite algebraic model;
it is not itself a beta-decay operator representation.
-/
def TPlus (u : ColorTriplet) : ZornOPParavector.Zorn := quarkTripletLane u

/-- 
The symbol `TMinus` names the lower anti-triplet lane in this finite model;
no physical transition interpretation is assumed.
-/
def TMinus (v : ColorTriplet) : ZornOPParavector.Zorn := antiquarkTripletLane v

/-- The modeled upper triplet lane is square-zero in the Zorn algebra. This
is algebraic nilpotence, not a beta-decay or mass-shell conservation theorem. -/
theorem triplet_lane_square_zero (u : ColorTriplet) :
    ZornOPParavector.SquareZero (TPlus u) := by
  simpa [TPlus, quarkTripletLane] using ZornOPParavector.Nup_sq u

/-- The same upper lane has zero Zorn norm, a separate scalar readout from
its square-zero product identity. -/
theorem triplet_lane_zorn_norm_eq_zero (u : ColorTriplet) :
    ZornOPParavector.zornDet (TPlus u) = 0 := by
  simp [TPlus, quarkTripletLane, ZornOPParavector.Nup,
    ZornOPParavector.zornDet, SplitOctonionBraidSU3.zornNorm,
    SplitOctonionBraidSU3.dot3, Fin.sum_univ_three]

/-- The associator is an algebraic obstruction in the split-octonion carrier.
No identification with the physical isospin-breaking parameter `δ_C` is made. -/
def IsospinBreakingObstruction (A B C : ZornAssociatorSplitOctonion.Zorn) : ZornAssociatorSplitOctonion.Zorn :=
  ZornAssociatorSplitOctonion.associator A B C

/-- This particular finite Zorn carrier has a nonzero associator witness.
It does not imply a CKM unitarity relation or a nonzero physical `δ_C`. -/
theorem zorn_associator_has_nonzero_witness :
    ∃ A B C : ZornAssociatorSplitOctonion.Zorn, IsospinBreakingObstruction A B C ≠ 0 := by
  use ZornAssociatorSplitOctonion.U ZornAssociatorSplitOctonion.e₁
  use ZornAssociatorSplitOctonion.L ZornAssociatorSplitOctonion.e₁
  use ZornAssociatorSplitOctonion.U ZornAssociatorSplitOctonion.e₂
  exact ZornAssociatorSplitOctonion.associator_U₁_L₁_U₂_nonzero

end ZornIsospinBreaking
end noncomputable section
