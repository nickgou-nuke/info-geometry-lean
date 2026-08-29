/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Projective.CrossRatioPGL2

namespace InfoGeometry.Canonical

open InfoGeometry.Projective.CrossRatioPGL2 Matrix Complex

/-- 🏆 GRAND CANONICAL CAPSTONE: Projective Cross-Ratio and PGL(2, ℂ) Invariance Synthesis -/
theorem grand_canonical_cross_ratio_pgl2_synthesis
    (s : ℂ)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0)
    (P1 P2 P3 P4 : ℂ × ℂ) :
    let z0 : ℂ := ⟨3 / 2, 0⟩
    let p0 : ℂ := ⟨-1 / 2, 0⟩
    (apollonianCrossRatio (affinePoint s) (affinePoint z0) (affinePoint p0) pointInfinity = (s - z0) / (s - p0)) ∧
    (detBracket (matrixAction M P1) (matrixAction M P2) = M.det * detBracket P1 P2) ∧
    (crossRatio (matrixAction M P1) (matrixAction M P2) (matrixAction M P3) (matrixAction M P4) =
     crossRatio P1 P2 P3 P4) :=
  grand_cross_ratio_pgl2_synthesis s M hM P1 P2 P3 P4

end InfoGeometry.Canonical
