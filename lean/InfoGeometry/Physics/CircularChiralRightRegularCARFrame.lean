import InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.OperatorZornSoldering
import InfoGeometry.Algebra.CyclotomicOperatorProjectors

/-!
# Concrete circular chiral CAR frame

The circular root channels are represented on the native split-octonion
carrier by right multiplication.  The associative shell is `EndCZ`; no
associativity of the split-octonion carrier is assumed.
-/

namespace InfoGeometry.Physics.CircularChiralRightRegularCARFrame

noncomputable section

open InfoGeometry.Canonical
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Lie.SplitOctonionEllCircularPeirceBasis
open InfoGeometry.Lie.SplitOctonionCircularZ3Grading
open InfoGeometry.Lie.SplitOctonionEllCircularCAR
open InfoGeometry.Lie.SplitOctonionEllPolarization

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

def circularRightRegularPacket : ChiralSigmaOperatorPacket EndCZ where
  uPlus := rightRegular InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus
  uMinus := rightRegular InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus
  sigmaPlus := fun i => rightRegular (rootPlus i)
  sigmaMinus := fun i => rightRegular (rootMinus i)

theorem circularRightRegular_packet_CAR (i : Fin 3) :
    (rightRegularCARPair i).ann * (rightRegularCARPair i).cre +
        (rightRegularCARPair i).cre * (rightRegularCARPair i).ann =
      (1 : EndCZ) := by
  exact rightRegular_root_CAR i

theorem circularRightRegular_packet_nilpotent_plus (i : Fin 3) :
    rightRegular (rootPlus i) * rightRegular (rootPlus i) = 0 := by
  exact rightRegular_rootPlus_sq i

theorem circularRightRegular_packet_nilpotent_minus (i : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootMinus i) = 0 := by
  exact rightRegular_rootMinus_sq i

theorem circularRightRegular_packet_isNilpotent_plus (i : Fin 3) :
    InfoGeometry.Algebra.CyclotomicOperatorProjectors.IsNilpotent
      (rightRegular (rootPlus i)) 2 := by
  change rightRegular (rootPlus i) ^ 2 = 0
  simpa [pow_two] using circularRightRegular_packet_nilpotent_plus i

theorem circularRightRegular_packet_isNilpotent_minus (i : Fin 3) :
    InfoGeometry.Algebra.CyclotomicOperatorProjectors.IsNilpotent
      (rightRegular (rootMinus i)) 2 := by
  change rightRegular (rootMinus i) ^ 2 = 0
  simpa [pow_two] using circularRightRegular_packet_nilpotent_minus i

theorem circularRightRegular_endpoint_orientation (i : Fin 3) :
    rightRegular (rootPlus i) InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus = rootPlus i ∧
      rightRegular (rootPlus i) InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus = 0 ∧
      rightRegular (rootMinus i) InfoGeometry.Lie.SplitOctonionEllCrossChannel.uPlus = 0 ∧
      rightRegular (rootMinus i) InfoGeometry.Lie.SplitOctonionEllCrossChannel.uMinus = rootMinus i := by
  exact ⟨rightRegular_rootPlus_uPlus i,
    rightRegular_rootPlus_uMinus i,
    rightRegular_rootMinus_uPlus i,
    rightRegular_rootMinus_uMinus i⟩

end
end InfoGeometry.Physics.CircularChiralRightRegularCARFrame
