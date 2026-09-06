import InfoGeometry.Canonical.SplitOctonionCircularChiralClosure
import InfoGeometry.Canonical.SplitOctonionMalcev
import InfoGeometry.Canonical.SplitOctonionPolarizedJordanMalcev

/-!
# Canonical split-octonion chiral closure aggregate

This owner is an aggregation interface, not a second multiplication table.  It
re-exports the native circular Peirce packet, the raw Jacobiator obstruction,
and the typed rectangular Jordan-pair layer.
-/

namespace InfoGeometry.Canonical.SplitOctonionChiralClosure

open InfoGeometry.Algebra.ZornMatrix
open SplitOctonionCircularChiralClosure
open SplitOctonionMalcev
open SplitOctonionPolarizedJordanMalcev

theorem circular_chiral_laws_available :
    uPlus + uMinus =
      (I : SplitOctonionCircularChiralClosure.Carrier) := uPlus_add_uMinus

theorem raw_commutator_jacobi_defect :
    rawJacobiator
        (InfoGeometry.Algebra.ZornVectorMatrix.U 0 : SplitOctonionMalcev.Carrier)
        (InfoGeometry.Algebra.ZornVectorMatrix.U 1)
        (InfoGeometry.Algebra.ZornVectorMatrix.U 2) ≠
      InfoGeometry.Algebra.ZornVectorMatrix.zero :=
  raw_commutator_not_lie

theorem polarized_sheet_packet_available :
    ((E11 : SplitOctonionPolarizedJordanMalcev.Carrier) * E11 = E11 ∧
      (∀ i j : Fin 3,
        (U i : SplitOctonionPolarizedJordanMalcev.Carrier) * U j + U j * U i = 0) ∧
      (∀ i : Fin 3,
        (E11 : SplitOctonionPolarizedJordanMalcev.Carrier) * U i = U i) ∧
      (∀ i j : Fin 3,
        lowerLane ((U i : SplitOctonionPolarizedJordanMalcev.Carrier) * U j)) ∧
      (((U 0 : SplitOctonionPolarizedJordanMalcev.Carrier) * U 1) * U 2 -
        U 0 * (U 1 * U 2) = E22 - E11)) :=
  native_sheet_closure_packet

end InfoGeometry.Canonical.SplitOctonionChiralClosure
