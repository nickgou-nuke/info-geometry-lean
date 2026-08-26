import InfoGeometry.Algebra.Zorn.G2OneCellQuotientTransport

namespace InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity

open InfoGeometry.Algebra.Zorn.G2CASFactorizationCarrier
open InfoGeometry.Algebra.Zorn.G2CanonicalPCCollector
open InfoGeometry.Algebra.Zorn.G2FlagOrbitPartitionCertificate
open InfoGeometry.Algebra.Zorn.G2FlagWordCertificate
open InfoGeometry.Algebra.Zorn.G2TwoPCNormalForm

/-! The residual word is the canonical PC-exponent normal form of the left
factor.  Faithfulness on each cell remains an explicit algebraic interface;
it is not manufactured by enumerating the representative table. -/

def ValidFactorWord (w : FactorWord) : Prop :=
  ∀ t ∈ w, t.2 = 1 ∨ t.2 = -1

def factorTokenExponent (t : FactorToken) : PCExponent :=
  fun j => if t.1 = j then t.2 else 0

def factorWordExponent : FactorWord → PCExponent
  | [] => G2TwoPCNormalForm.zeroPC
  | t :: w => G2TwoPCNormalForm.pcCombine (factorTokenExponent t)
      (factorWordExponent w)

def residualWord (k : Fin 12) (i : Fin 189) : PCExponent :=
  factorWordExponent (leftFactorWord k i)

theorem residualWord_injective_on_cell
    (hresidual : ∀ k : Fin 12, ∀ i j : Fin 189,
      i ∈ orbitCells k → j ∈ orbitCells k →
      residualWord k i = residualWord k j → i = j) :
    ∀ k : Fin 12, ∀ i j : Fin 189,
      i ∈ orbitCells k → j ∈ orbitCells k →
      residualWord k i = residualWord k j → i = j := by
  exact hresidual

end InfoGeometry.Algebra.Zorn.G2QuotientResidualInjectivity
