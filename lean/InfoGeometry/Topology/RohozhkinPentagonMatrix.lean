import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import InfoGeometry.Topology.DelaunayFlipMatrix
import InfoGeometry.Topology.DelaunayPureBraidInvariant

/-!
# Rohozhkin Appendix A rational pentagon matrices

#### BUCKET 1: CLOSED FINITE THEOREMS
- `pentagon_appendix_identity`: the five concrete rational `3 × 3` Appendix A
  transport matrices multiply to the identity under explicit nonzero
  denominator assumptions.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
None.

#### BUCKET 3: OPEN CLOSURE DEBT
- Deriving these Appendix A matrices from a general `2n+1` triangle-basis
  insertion function.
- Bundling the inverse, far-commutativity, and pentagon identities into a
  pure-braid group homomorphism.
- Markov-move invariance and knot invariants.

This file is a rational Delaunay/pentagon layer.  It is not a unitary anyon
braid representation, not a Fibonacci `F/R` category construction, and not a
Yang--Baxter theorem.
-/

namespace InfoGeometry.Topology.Delaunay

/--
The first Appendix A transport matrix in the Rohozhkin five-flip pentagon
calculation.  It acts on a three-triangle basis and leaves the first basis
vector fixed.
-/
noncomputable def pentagonGamma1
    (zi _zj zk zl zm : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 0, 0],
    ![0, (zi - zm) / (zi - zl), (zi - zk) / (zi - zl)],
    ![0, (zm - zl) / (zi - zl), (zk - zl) / (zi - zl)]]

/-- The second Appendix A transport matrix in the five-flip pentagon. -/
noncomputable def pentagonGamma2
    (zi zj zk _zl zm : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![(zi - zm) / (zi - zk), (zi - zj) / (zi - zk), 0],
    ![(zm - zk) / (zi - zk), (zj - zk) / (zi - zk), 0],
    ![0, 0, 1]]

/-- The third Appendix A transport matrix in the five-flip pentagon. -/
noncomputable def pentagonGamma3
    (_zi zj zk zl zm : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![1, 0, 0],
    ![0, (zk - zl) / (zk - zm), (zk - zj) / (zk - zm)],
    ![0, (zl - zm) / (zk - zm), (zj - zm) / (zk - zm)]]

/-- The fourth Appendix A transport matrix in the five-flip pentagon. -/
noncomputable def pentagonGamma4
    (zi zj _zk zl zm : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![(zj - zl) / (zj - zm), 0, (zj - zi) / (zj - zm)],
    ![(zl - zm) / (zj - zm), 0, (zi - zm) / (zj - zm)],
    ![0, 1, 0]]

/-- The fifth Appendix A transport matrix in the five-flip pentagon. -/
noncomputable def pentagonGamma5
    (zi zj zk zl _zm : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![(zj - zk) / (zj - zl), 0, (zj - zi) / (zj - zl)],
    ![(zk - zl) / (zj - zl), 0, (zi - zl) / (zj - zl)],
    ![0, 1, 0]]

/--
Appendix-level rational pentagon identity for Rohozhkin's Delaunay flip
transport matrices.

This is the finite algebraic identity only: it does not claim a Voronoi
geometry construction, a Yang--Baxter representation, or Markov-move knot
invariance.
-/
theorem pentagon_appendix_identity
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    pentagonGamma5 zi zj zk zl zm *
      pentagonGamma4 zi zj zk zl zm *
      pentagonGamma3 zi zj zk zl zm *
      pentagonGamma2 zi zj zk zl zm *
      pentagonGamma1 zi zj zk zl zm = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [pentagonGamma1, pentagonGamma2, pentagonGamma3, pentagonGamma4,
      pentagonGamma5, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp [h_il, h_ik, h_km, h_jm, h_jl] <;>
    ring

/--
The Appendix A matrices instantiate the abstract `pentagonStatement` target
from the Delaunay flip-matrix layer.
-/
theorem pentagon_appendix_statement
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0) :
    pentagonStatement zi zj zk zl zm
      (pentagonGamma5 zi zj zk zl zm)
      (pentagonGamma4 zi zj zk zl zm)
      (pentagonGamma3 zi zj zk zl zm)
      (pentagonGamma2 zi zj zk zl zm)
      (pentagonGamma1 zi zj zk zl zm) :=
  pentagon_appendix_identity zi zj zk zl zm h_il h_ik h_km h_jm h_jl

/-- The Appendix A five-flip block as `n = 1` Delaunay flip contexts. -/
noncomputable def appendixPentagonContexts
    (zi zj zk zl zm : ℚ) : List (DelaunayFlipContext 1) :=
  [{ matrix := pentagonGamma5 zi zj zk zl zm },
   { matrix := pentagonGamma4 zi zj zk zl zm },
   { matrix := pentagonGamma3 zi zj zk zl zm },
   { matrix := pentagonGamma2 zi zj zk zl zm },
   { matrix := pentagonGamma1 zi zj zk zl zm }]

/--
The Appendix A pentagon is a concrete witnessed five-flip deletion move for the
`n = 1` Delaunay quotient layer.
-/
theorem rohozhkin_invariant_under_appendix_pentagon_move
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0)
    (w₁ w₂ : List (DelaunayFlipContext 1))
    (hbefore hafter : Prop) :
    rohozhkinMatrix
        (⟨w₁ ++ (appendixPentagonContexts zi zj zk zl zm) ++ w₂, hbefore⟩ :
          DelaunayFlipWord 1) =
      rohozhkinMatrix
        (⟨w₁ ++ w₂, hafter⟩ : DelaunayFlipWord 1) := by
  dsimp [appendixPentagonContexts]
  exact rohozhkin_invariant_under_pentagon_move w₁ w₂
    { matrix := pentagonGamma5 zi zj zk zl zm }
    { matrix := pentagonGamma4 zi zj zk zl zm }
    { matrix := pentagonGamma3 zi zj zk zl zm }
    { matrix := pentagonGamma2 zi zj zk zl zm }
    { matrix := pentagonGamma1 zi zj zk zl zm }
    (pentagon_appendix_identity zi zj zk zl zm h_il h_ik h_km h_jm h_jl)
    hbefore hafter

/--
The Appendix A five-flip pentagon is a single witnessed step in the Delaunay
flip-word equivalence relation.

This is the precise presentation-level "tiling pentagon" move used by the
pure-braid quotient layer.
-/
theorem appendix_pentagon_delaunay_equiv
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0)
    (w₁ w₂ : List (DelaunayFlipContext 1))
    (hbefore hafter : Prop) :
    DelaunayEquiv
        (⟨w₁ ++ (appendixPentagonContexts zi zj zk zl zm) ++ w₂, hbefore⟩ :
          DelaunayFlipWord 1)
        (⟨w₁ ++ w₂, hafter⟩ : DelaunayFlipWord 1) := by
  dsimp [appendixPentagonContexts]
  exact DelaunayEquiv.step .pentagon _ _
    (DelaunayMoveList.pentagon w₁ w₂
      { matrix := pentagonGamma5 zi zj zk zl zm }
      { matrix := pentagonGamma4 zi zj zk zl zm }
      { matrix := pentagonGamma3 zi zj zk zl zm }
      { matrix := pentagonGamma2 zi zj zk zl zm }
      { matrix := pentagonGamma1 zi zj zk zl zm }
      (pentagon_appendix_identity zi zj zk zl zm h_il h_ik h_km h_jm h_jl))

/--
Named tiling-pentagon braid readout: deleting the witnessed Appendix A
five-flip pentagon block preserves the Rohozhkin rational transport matrix.

No anyon, Yang--Baxter, or full pure-braid homomorphism is asserted here.
-/
theorem tiling_pentagon_braid_readout
    (zi zj zk zl zm : ℚ)
    (h_il : zi - zl ≠ 0)
    (h_ik : zi - zk ≠ 0)
    (h_km : zk - zm ≠ 0)
    (h_jm : zj - zm ≠ 0)
    (h_jl : zj - zl ≠ 0)
    (w₁ w₂ : List (DelaunayFlipContext 1))
    (hbefore hafter : Prop) :
    rohozhkinMatrix
        (⟨w₁ ++ (appendixPentagonContexts zi zj zk zl zm) ++ w₂, hbefore⟩ :
          DelaunayFlipWord 1) =
      rohozhkinMatrix
        (⟨w₁ ++ w₂, hafter⟩ : DelaunayFlipWord 1) :=
  rohozhkin_invariant_under_equiv
    (appendix_pentagon_delaunay_equiv zi zj zk zl zm
      h_il h_ik h_km h_jm h_jl w₁ w₂ hbefore hafter)

end InfoGeometry.Topology.Delaunay
