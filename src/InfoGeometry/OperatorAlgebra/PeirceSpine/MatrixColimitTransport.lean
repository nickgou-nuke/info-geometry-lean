import InfoGeometry.OperatorAlgebra.PeirceSpine.RingHomTransport
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Peirce polynomial operators in the existing full-matrix direct limit

The carrier, bonding maps, and universal property are supplied by
`Cl11TensorTowerLimit` and `DirectLimitSuperClosureLemmas`. This file proves
coherence of the four homogenized channels and the perturbed-grading square
inside that actual limit. It introduces no replacement limit carrier.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower

/-- The square identity holds with arbitrary amplitudes in the limit ring. -/
theorem matrix_limit_grading_phi_sq (n : ℕ) {P : Stage n} (hP : P * P = P)
    (A C : Limit) :
    (invS (ofStage n P) + genPhi (ofStage n P) A C) *
      (invS (ofStage n P) + genPhi (ofStage n P) A C) =
      zetaPlusFactor (ofStage n P) A C :=
  grading_add_phi_sq (map_idempotent (ofStage n) hP) A C

theorem matrix_limit_hProjV_bond (n : ℕ) (P A C X : Stage n) :
    ofStage (n + 1) (hProjV (stageEmbed n P) (stageEmbed n A)
      (stageEmbed n C) (stageEmbed n X)) = ofStage n (hProjV P A C X) := by
  rw [map_hProjV, map_hProjV]
  simp only [ofStage_apply_bond]

theorem matrix_limit_hProjPhi_bond (n : ℕ) (P A C X : Stage n) :
    ofStage (n + 1) (hProjPhi (stageEmbed n P) (stageEmbed n A)
      (stageEmbed n C) (stageEmbed n X)) = ofStage n (hProjPhi P A C X) := by
  rw [map_hProjPhi, map_hProjPhi]
  simp only [ofStage_apply_bond]

theorem matrix_limit_hProjJ_bond (n : ℕ) (P A C X : Stage n) :
    ofStage (n + 1) (hProjJ (stageEmbed n P) (stageEmbed n A)
      (stageEmbed n C) (stageEmbed n X)) = ofStage n (hProjJ P A C X) := by
  rw [map_hProjJ, map_hProjJ]
  simp only [ofStage_apply_bond]

theorem matrix_limit_hProjSig_bond (n : ℕ) (P A C X : Stage n) :
    ofStage (n + 1) (hProjSig (stageEmbed n P) (stageEmbed n A)
      (stageEmbed n C) (stageEmbed n X)) = ofStage n (hProjSig P A C X) := by
  rw [map_hProjSig, map_hProjSig]
  simp only [ofStage_apply_bond]

end InfoGeometry.OperatorAlgebra.PeirceSpine
