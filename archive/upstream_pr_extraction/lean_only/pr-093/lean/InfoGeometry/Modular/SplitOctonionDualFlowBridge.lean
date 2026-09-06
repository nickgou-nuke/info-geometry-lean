import InfoGeometry.Lie.G2FromSplitOctonions

/-! Pointwise dual-flow commutator identities for the nonassociative
split-octonion product.  This deliberately does not claim that the bare
commutator is itself a derivation. -/

noncomputable section

namespace InfoGeometry.Modular.SplitOctonionDualFlowBridge

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication
open InfoGeometry.OperatorAlgebra.SplitOctonions.DerivationData
open InfoGeometry.Lie.G2FromSplitOctonions

def commZ (K X : SplitOct) : SplitOct := subZ (mulZ K X) (mulZ X K)

lemma subZ_eq_addZ_negZ (X Y : SplitOct) :
    subZ X Y = addZ X (negZ Y) := by
  ext <;> simp [subZ, addZ, negZ, sub_eq_add_neg]

lemma IsDeriv.map_subZ {D : DerivSpace} (hD : IsDeriv D) (X Y : SplitOct) :
    D (subZ X Y) = subZ (D X) (D Y) := by
  rcases hD with ⟨hadd, hneg, hmul⟩
  rw [subZ_eq_addZ_negZ, hadd, hneg, ← subZ_eq_addZ_negZ]

theorem derivation_commZ_comm {D : DerivSpace} (hD : IsDeriv D) (K X : SplitOct) :
    subZ (D (commZ K X)) (commZ K (D X)) = commZ (D K) X := by
  rw [commZ, IsDeriv.map_subZ hD]
  rw [hD.2.2 K X, hD.2.2 X K]
  ext <;> simp [commZ, subZ, addZ, mulZ] <;> ring

theorem derivation_commZ_comm_of_invariant {D : DerivSpace} (hD : IsDeriv D)
    (K : SplitOct) (hK : D K = zeroZ) (X : SplitOct) :
    subZ (D (commZ K X)) (commZ K (D X)) = zeroZ := by
  rw [derivation_commZ_comm hD K X, hK]
  cases X
  simp [commZ, subZ, mulZ, zeroZ]

theorem rot01_commZ_comm (K X : SplitOct) :
    subZ (rot01Derivation (commZ K X)) (commZ K (rot01Derivation X)) =
      commZ (rot01Derivation K) X :=
  derivation_commZ_comm D01_deriv K X

end InfoGeometry.Modular.SplitOctonionDualFlowBridge

end noncomputable section
