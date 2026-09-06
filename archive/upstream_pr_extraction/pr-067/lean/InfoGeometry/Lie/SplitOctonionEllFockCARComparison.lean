import InfoGeometry.Lie.SplitOctonionEllCrossChannel
import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators
import InfoGeometry.Physics.SplitCliffordAlgebras

/-!
# Relation-level split-octonion/Fock CAR comparison

This file packages the already-proved relations on the two different
carriers.  It deliberately constructs no map between the nonassociative
split-octonion carrier and the associative Clifford algebra.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionEllFockCARComparison

open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionEllCrossChannel
open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Physics

abbrev ZornCarrier := CanonicalZorn
abbrev FockCarrier := Cl55

def zornCARPair (a : Fin 3) : SplitClifford.CARPair ZornCarrier where
  ann := rootMinus a
  cre := rootPlus a
  ann_sq := rootMinus_sq a
  cre_sq := rootPlus_sq a
  anti := by
    simpa [add_comm, add_left_comm, add_assoc] using root_anticommutator a

def fockCARPair (a : Fin 3) : SplitClifford.CARPair FockCarrier where
  ann := chiralMinus55 a
  cre := chiralPlus55 a
  ann_sq := chiralMinus55_sq a
  cre_sq := chiralPlus55_sq a
  anti := by
    simpa using chiralMinus55_plus55_anticommutator a a

theorem zornCARPair_mixed (a : Fin 3) :
    (zornCARPair a).ann * (zornCARPair a).cre +
        (zornCARPair a).cre * (zornCARPair a).ann = 1 := by
  exact (zornCARPair a).anti

theorem fockCARPair_mixed (a : Fin 3) :
    (fockCARPair a).ann * (fockCARPair a).cre +
        (fockCARPair a).cre * (fockCARPair a).ann = 1 := by
  exact (fockCARPair a).anti

end InfoGeometry.Lie.SplitOctonionEllFockCARComparison
