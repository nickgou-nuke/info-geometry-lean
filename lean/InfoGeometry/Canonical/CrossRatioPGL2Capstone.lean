import InfoGeometry.Projective.CrossRatioPGL2
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Canonical.CrossRatioPGL2Capstone

open Matrix Complex
open InfoGeometry.Projective.CrossRatioPGL2
open InfoGeometry.Canonical.YangBaxterProof

noncomputable section

/-! The projective readout and the independent finite Yang--Baxter packet are
assembled directly from their owners. -/
theorem grand_canonical_cross_ratio_pgl2_synthesis
    (s : ℂ) (hs : s - p0 ≠ 0)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0) :
    (detBracket (affinePoint s) pointAtInfinity = -1) ∧
    (crossRatio (affinePoint s) (affinePoint z0) (affinePoint p0) pointAtInfinity =
     (s - z0) / (s - p0)) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) := by
  exact ⟨detBracket_infinity s,
    apollonian_cross_ratio_eq_moebius s hs,
    F_sq,
    F_B_F_eq_R⟩

end
end InfoGeometry.Canonical.CrossRatioPGL2Capstone
