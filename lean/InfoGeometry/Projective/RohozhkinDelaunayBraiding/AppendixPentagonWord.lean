import InfoGeometry.Topology.RohozhkinPentagonMatrix
import InfoGeometry.Topology.RohozhkinRepresentation

/-!
# Appendix A Pentagon Word

Conservative scaffolding that exposes Rohozhkin Appendix-A pentagon flips as a
concrete five-flip flip-word layer for the braid trajectory model.
-/

namespace InfoGeometry.Topology.RohozhkinDelaunayBraiding

open InfoGeometry.Topology.Delaunay
open InfoGeometry.Topology.PureBraid
open InfoGeometry.Topology.RohozhkinBoundary
open InfoGeometry.Topology.RohozhkinRepresentation

/-- The Appendix A five-flip word in the `n = 1` Delaunay presentation layer. -/
noncomputable def appendixPentagonWord
    (zi zj zk zl zm : ℚ) (h : Prop) : DelaunayFlipWord 1 :=
  { flips := appendixPentagonContexts zi zj zk zl zm
    admissible := h }

/-- The Appendix A pentagon word evaluates to the identity transport matrix. -/
theorem appendixPentagonWord_matrix_eq_one
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    Delaunay.rohozhkinMatrix
      (appendixPentagonWord zi zj zk zl zm
        (pentagonGamma5 zi zj zk zl zm * pentagonGamma4 zi zj zk zl zm *
          pentagonGamma3 zi zj zk zl zm * pentagonGamma2 zi zj zk zl zm *
          pentagonGamma1 zi zj zk zl zm =
            (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ))) =
      (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ) := by
  simpa [appendixPentagonWord] using
    (Delaunay.tiling_pentagon_braid_readout zi zj zk zl zm
      h_il h_ik h_km h_jm h_jl
      ([] : List (DelaunayFlipContext 1)) ([] : List (DelaunayFlipContext 1))
      (pentagonGamma5 zi zj zk zl zm * pentagonGamma4 zi zj zk zl zm *
        pentagonGamma3 zi zj zk zl zm * pentagonGamma2 zi zj zk zl zm *
        pentagonGamma1 zi zj zk zl zm =
          (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ))
      (pentagonGamma5 zi zj zk zl zm * pentagonGamma4 zi zj zk zl zm *
        pentagonGamma3 zi zj zk zl zm * pentagonGamma2 zi zj zk zl zm *
        pentagonGamma1 zi zj zk zl zm =
          (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ)))

/-- The Appendix A pentagon word is equivalent to the empty word in the Delaunay
quotient relation. -/
theorem appendixPentagonWord_equiv_empty
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    Delaunay.DelaunayEquiv
      (appendixPentagonWord zi zj zk zl zm
        (pentagonGamma5 zi zj zk zl zm * pentagonGamma4 zi zj zk zl zm *
          pentagonGamma3 zi zj zk zl zm * pentagonGamma2 zi zj zk zl zm *
          pentagonGamma1 zi zj zk zl zm =
            (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ)))
      ({ flips := [],
         admissible := pentagonGamma5 zi zj zk zl zm * pentagonGamma4 zi zj zk zl zm *
           pentagonGamma3 zi zj zk zl zm * pentagonGamma2 zi zj zk zl zm *
           pentagonGamma1 zi zj zk zl zm =
             (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ) } :
         DelaunayFlipWord 1) := by
  simpa [appendixPentagonWord] using
    (Delaunay.appendix_pentagon_delaunay_equiv zi zj zk zl zm
      h_il h_ik h_km h_jm h_jl
      ([] : List (DelaunayFlipContext 1)) ([] : List (DelaunayFlipContext 1))
      (pentagonGamma5 zi zj zk zl zm * pentagonGamma4 zi zj zk zl zm *
        pentagonGamma3 zi zj zk zl zm * pentagonGamma2 zi zj zk zl zm *
        pentagonGamma1 zi zj zk zl zm =
          (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ))
      (pentagonGamma5 zi zj zk zl zm * pentagonGamma4 zi zj zk zl zm *
        pentagonGamma3 zi zj zk zl zm * pentagonGamma2 zi zj zk zl zm *
        pentagonGamma1 zi zj zk zl zm =
          (1 : Matrix (Fin (rohozhkinDim 1)) (Fin (rohozhkinDim 1)) ℚ)))

end InfoGeometry.Topology.RohozhkinDelaunayBraiding
