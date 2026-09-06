import InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2

namespace InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoSylowPCAutomorphisms
open InfoGeometry.Algebra.Zorn.G2TwoPCRecovery
open InfoGeometry.Algebra.Zorn.G2TwoSylowSubgroup
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2

/-!
The sequential recovery factor is the ordered PC word whose exponents are
the bits extracted by the same peeling procedure.  This is the interface
needed before classifying the residual factor by the concrete Weyl subgroup.
-/
theorem fullPeel_pcWord_factorization (f : SplitOctF2Aut) :
    G2TwoSylowSubgroup.pcWord (extractAllBits f) * fullPeel f = f := by
  change
    (if extractBit0 f then pc1Aut else 1) *
      (if extractBit1 f then pc2Aut else 1) *
      (if extractBit2 f then pc3Aut else 1) *
      (if extractBit3 f then pc4Aut else 1) *
      (if extractBit4 f then pc5Aut else 1) *
      (if extractBit5 f then pc6Aut else 1) * fullPeel f = f
  exact fullPeel_pc_factorization f

/-! On the already classified unipotent subgroup, the residual is exactly the
identity.  This is the precise theorem supplied by the six PC pivots; it does
not assert Weyl membership for arbitrary carrier elements. -/

theorem fullPeel_pcWord_eq_one (e : PCWordExp) :
    fullPeel (G2TwoSylowSubgroup.pcWord e) = 1 := by
  have h := fullPeel_pcWord_factorization
    (G2TwoSylowSubgroup.pcWord e)
  rw [extractAllBits_pcWord] at h
  apply mul_left_cancel (a := G2TwoSylowSubgroup.pcWord e)
  simpa using h

/-! A right-handed peel is obtained from the already verified left-handed
peel by applying it to the inverse.  This is forced by the group law and does
not introduce a second coordinate convention. -/

def rightPeel (f : SplitOctF2Aut) : SplitOctF2Aut :=
  (fullPeel (f⁻¹))⁻¹

def rightPeelFactor (f : SplitOctF2Aut) : SplitOctF2Aut :=
  G2TwoSylowSubgroup.pcWord (extractAllBits (f⁻¹))

theorem rightPeel_reconstruction (f : SplitOctF2Aut) :
    f * rightPeelFactor f = rightPeel f := by
  have h := fullPeel_pcWord_factorization (f⁻¹)
  have hinv :
      (fullPeel (f⁻¹))⁻¹ *
        (G2TwoSylowSubgroup.pcWord (extractAllBits (f⁻¹)))⁻¹ = f := by
    simpa [mul_inv_rev] using congrArg Inv.inv h
  change f * G2TwoSylowSubgroup.pcWord (extractAllBits (f⁻¹)) =
    (fullPeel (f⁻¹))⁻¹
  calc
    f * G2TwoSylowSubgroup.pcWord (extractAllBits (f⁻¹)) =
        ((fullPeel (f⁻¹))⁻¹ *
          (G2TwoSylowSubgroup.pcWord (extractAllBits (f⁻¹)))⁻¹) *
          G2TwoSylowSubgroup.pcWord (extractAllBits (f⁻¹)) := by
      rw [hinv]
    _ = (fullPeel (f⁻¹))⁻¹ := by simp [mul_assoc]

def doublePeel (f : SplitOctF2Aut) : SplitOctF2Aut :=
  fullPeel (rightPeel f)

theorem doublePeel_left_reconstruction (f : SplitOctF2Aut) :
    G2TwoSylowSubgroup.pcWord (extractAllBits (rightPeel f)) *
        doublePeel f = rightPeel f := by
  exact fullPeel_pcWord_factorization (rightPeel f)

theorem doublePeel_reconstruction (f : SplitOctF2Aut) :
    G2TwoSylowSubgroup.pcWord (extractAllBits (rightPeel f)) *
        doublePeel f * (rightPeelFactor f)⁻¹ = f := by
  have hleft := doublePeel_left_reconstruction f
  have hright := rightPeel_reconstruction f
  calc
    G2TwoSylowSubgroup.pcWord (extractAllBits (rightPeel f)) *
        doublePeel f * (rightPeelFactor f)⁻¹ =
        rightPeel f * (rightPeelFactor f)⁻¹ := by
          rw [hleft]
    _ = (f * rightPeelFactor f) * (rightPeelFactor f)⁻¹ := by
          rw [hright]
    _ = f := by simp

theorem factorization_of_fullPeel_eq_weyl
    (f : SplitOctF2Aut) (k : ZMod 6) (b : Bool)
    (h : fullPeel f = weylNF k b) :
    ∃ e : PCWordExp,
      f = G2TwoSylowSubgroup.pcWord e * weylNF k b := by
  refine ⟨extractAllBits f, ?_⟩
  rw [← h]
  exact (fullPeel_pcWord_factorization f).symm


end InfoGeometry.Algebra.Zorn.G2PCRecoveryFactorization
