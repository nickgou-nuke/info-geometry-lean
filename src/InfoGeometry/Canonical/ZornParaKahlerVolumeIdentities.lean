/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornVectorMatrixExplicit

/-!
# Para-Kähler commutator and volume identities in native Zorn coordinates

This file reuses `ZornVectorMatrixExplicit.ZornCoord`, its dot/cross product,
and its multiplication. It proves the para-Kähler commutator and the primal
triple-volume formulas on that owner carrier. These are finite coordinate
identities; no metriplectic bracket or dissipative dynamics is defined here.
The file does not identify the Zorn product with associative matrix product.
-/

namespace InfoGeometry.Canonical.ZornParaKahlerVolumeIdentities

open InfoGeometry.Canonical.ZornVectorMatrixExplicit

abbrev ParaVector := Vec3 × Vec3

def offDiagonal (z : ParaVector) : ZornCoord := zornMk 0 0 z.1 z.2

def paraMetric (z w : ParaVector) : ℝ := dot3 z.1 w.2 + dot3 w.1 z.2

def paraSymplectic (z w : ParaVector) : ℝ := dot3 z.1 w.2 - dot3 w.1 z.2

def paraK (z : ParaVector) : ParaVector := (z.1, -z.2)

/-- The paired Hodge cross term in the off-diagonal blocks of a Zorn product. -/
def paraHodgeCross (z w : ParaVector) : ParaVector :=
  (-cross3 z.2 w.2, cross3 z.1 w.1)

def paraGrading : ZornCoord := zornMk 1 (-1) 0 0

def paraTriple (u v w : Vec3) : ℝ := dot3 (cross3 u v) w

def zornAssociator (x y z : ZornCoord) : ZornCoord :=
  zornMul (zornMul x y) z - zornMul x (zornMul y z)

theorem paraMetric_K_eq_symplectic (z w : ParaVector) :
    paraMetric (paraK z) w = paraSymplectic z w := by
  rcases z with ⟨u, v⟩
  rcases w with ⟨x, y⟩
  simp [paraMetric, paraSymplectic, paraK, dot3]
  ring

/-- The full coordinate decomposition of a product of off-diagonal Zorn vectors.

Its diagonal entries are the half-sum and half-difference of the para-metric
and para-symplectic forms; the off-diagonal entries are the two Hodge cross
terms. This is a finite coordinate identity for `zornMul`. -/
theorem offDiagonal_product_decomposition (z w : ParaVector) :
    zornMul (offDiagonal z) (offDiagonal w) =
      zornMk
        ((paraMetric z w + paraSymplectic z w) / 2)
        ((paraMetric z w - paraSymplectic z w) / 2)
        (paraHodgeCross z w).1
        (paraHodgeCross z w).2 := by
  rcases z with ⟨u₁, v₁⟩
  rcases w with ⟨u₂, v₂⟩
  apply Prod.ext
  · simp [offDiagonal, zornMul, zornMk, zornA, zornB, zornX, zornY,
      paraMetric, paraSymplectic, paraHodgeCross, dot3, cross3]
  · apply Prod.ext
    · simp [offDiagonal, zornMul, zornMk, zornA, zornB, zornX, zornY,
        paraMetric, paraSymplectic, paraHodgeCross, dot3, cross3]
      ring
    · apply Prod.ext
      · funext i
        fin_cases i <;>
          simp [offDiagonal, zornMul, zornMk, zornA, zornB, zornX, zornY,
            paraHodgeCross, dot3, cross3]
      · funext i
        fin_cases i <;>
          simp [offDiagonal, zornMul, zornMk, zornA, zornB, zornX, zornY,
            paraHodgeCross, dot3, cross3]

theorem paraGrading_commutator (z : ParaVector) :
    zornMul paraGrading (offDiagonal z) - zornMul (offDiagonal z) paraGrading =
      zornMk 0 0 (2 • z.1) (2 • (-z.2)) := by
  rcases z with ⟨u, v⟩
  apply Prod.ext
  · simp [paraGrading, offDiagonal, zornMul, zornMk, zornA, zornB,
      zornX, zornY, dot3, cross3]
  · apply Prod.ext
    · simp [paraGrading, offDiagonal, zornMul, zornMk, zornA, zornB,
        zornX, zornY, dot3, cross3]
    · apply Prod.ext
      · funext i
        fin_cases i <;> simp [paraGrading, offDiagonal, zornMul, zornMk,
          zornA, zornB, zornX, zornY, dot3, cross3] <;> ring
      · funext i
        fin_cases i <;> simp [paraGrading, offDiagonal, zornMul, zornMk,
          zornA, zornB, zornX, zornY, dot3, cross3] <;> ring

/-- The Peirce grading element anticommutes with every off-diagonal vector. -/
theorem paraGrading_anticommutator_zero (z : ParaVector) :
    zornMul paraGrading (offDiagonal z) + zornMul (offDiagonal z) paraGrading = 0 := by
  rcases z with ⟨u, v⟩
  apply Prod.ext
  · simp [paraGrading, offDiagonal, zornMul, zornMk, zornA, zornB,
      zornX, zornY, dot3, cross3]
  · apply Prod.ext
    · simp [paraGrading, offDiagonal, zornMul, zornMk, zornA, zornB,
        zornX, zornY, dot3, cross3]
    · apply Prod.ext
      · funext i
        fin_cases i <;> simp [paraGrading, offDiagonal, zornMul, zornMk,
          zornA, zornB, zornX, zornY, dot3, cross3]
      · funext i
        fin_cases i <;> simp [paraGrading, offDiagonal, zornMul, zornMk,
          zornA, zornB, zornX, zornY, dot3, cross3]

theorem paraMetric_sq_symplectic_sq_lagrange (z w : ParaVector) :
    (paraMetric z w)^2 - (paraSymplectic z w)^2 +
      4 * dot3 (cross3 z.1 w.1) (cross3 z.2 w.2) =
      paraMetric z z * paraMetric w w := by
  rcases z with ⟨u, v⟩
  rcases w with ⟨x, y⟩
  simp [paraMetric, paraSymplectic, dot3, cross3]
  ring

theorem primal_triple_singlet (u v w : Vec3) :
    zornMul (zornMul (offDiagonal (u, 0)) (offDiagonal (v, 0)))
        (offDiagonal (w, 0)) +
      zornMul (offDiagonal (u, 0))
        (zornMul (offDiagonal (v, 0)) (offDiagonal (w, 0))) =
      scalarZorn (paraTriple u v w) := by
  apply Prod.ext
  · simp [offDiagonal, scalarZorn, zornMul, zornMk, zornA, zornB,
      zornX, zornY, dot3, cross3, paraTriple]; ring
  · apply Prod.ext
    · simp [offDiagonal, scalarZorn, zornMul, zornMk, zornA, zornB,
        zornX, zornY, dot3, cross3, paraTriple]
    · apply Prod.ext
      · funext i
        fin_cases i <;> simp [offDiagonal, scalarZorn, zornMul, zornMk,
          zornA, zornB, zornX, zornY, dot3, cross3, paraTriple]
      · funext i
        fin_cases i <;> simp [offDiagonal, scalarZorn, zornMul, zornMk,
          zornA, zornB, zornX, zornY, dot3, cross3, paraTriple]

theorem primal_associator_eq_neg_volume_grading (u v w : Vec3) :
    zornAssociator (offDiagonal (u, 0)) (offDiagonal (v, 0))
        (offDiagonal (w, 0)) =
      zornMk (-paraTriple u v w) (paraTriple u v w) 0 0 := by
  apply Prod.ext
  · simp [zornAssociator, offDiagonal, zornMul, zornMk, zornA, zornB,
      zornX, zornY, dot3, cross3, paraTriple]; ring
  · apply Prod.ext
    · simp [zornAssociator, offDiagonal, zornMul, zornMk, zornA, zornB,
        zornX, zornY, dot3, cross3, paraTriple]
    · apply Prod.ext
      · funext i
        fin_cases i <;> simp [zornAssociator, offDiagonal, zornMul, zornMk,
          zornA, zornB, zornX, zornY, dot3, cross3, paraTriple]
      · funext i
        fin_cases i <;> simp [zornAssociator, offDiagonal, zornMul, zornMk,
          zornA, zornB, zornX, zornY, dot3, cross3, paraTriple]

end InfoGeometry.Canonical.ZornParaKahlerVolumeIdentities
