import InfoGeometry.Nuclear.NuclearChirality
import InfoGeometry.Canonical.ZornCore
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

namespace InfoGeometry.Nuclear.TrialityExperimental

open NuclearChirality
open ZornCore

/--
  Embeds the emergent nuclear geometry into the off-diagonal
  Split-Octonionic (Zorn) vector space, matching the Triality coordinates.
-/
noncomputable def emergentToZorn (E : EmergentGeometry) : Zorn :=
  { a := 0, -- Massless chiral limits on the diagonal
    b := 0,
    u := ![E.matter.j_pi ⟨0, by decide⟩, E.matter.j_pi ⟨1, by decide⟩, E.matter.j_pi ⟨2, by decide⟩],
    v := ![E.matter.j_nu ⟨0, by decide⟩, E.matter.j_nu ⟨1, by decide⟩, E.matter.j_nu ⟨2, by decide⟩] }

/-- 
  The nuclear dot product corresponds to the Zorn off-diagonal trace. 
-/
theorem zorn_pairing_eq_nuclear_dot (E : EmergentGeometry) :
    ZornCore.dot (emergentToZorn E).u (emergentToZorn E).v = NuclearChirality.dotProduct E.matter.j_pi E.matter.j_nu := by
  simp [emergentToZorn, NuclearChirality.dotProduct, ZornCore.dot, Fin.sum_univ_three, Matrix.cons_val_zero]

/-- 
  The determinant of the Zorn state captures the exact chiral pairing interaction.
-/
theorem zorn_det_eq_neg_pairing (E : EmergentGeometry) :
    ZornCore.det (emergentToZorn E) = - (NuclearChirality.dotProduct E.matter.j_pi E.matter.j_nu) := by
  have hd : ZornCore.det (emergentToZorn E) = - (ZornCore.dot (emergentToZorn E).u (emergentToZorn E).v) := by
    simp [ZornCore.det, emergentToZorn, ZornCore.dot, Fin.sum_univ_three, Matrix.cons_val_zero]
  rw [hd, zorn_pairing_eq_nuclear_dot]

/--
  The experimental QRPA energy eigenvalue condition.
-/
def TrialityInvariantSecular (S : ChiralQRPASystem) (Z : Zorn) : Prop :=
  S.A^2 - S.B^2 + (S.geom.G_eff * S.geom.frame.omega ⟨0, by decide⟩ * (-ZornCore.det Z))^2 - S.omega^2 = 0

/-- 
  Theorem (The Experimental Triality Principle):
  The physical energy splitting (observable S.omega) derived from the Zorn representation
  is exactly preserved under the full Cartan Triality permutation. 
  The experimentalist sees the exact same QRPA eigenvalues regardless of which 
  Triality sector (Core, Left-Spinor, Right-Spinor) is probed.
-/
theorem experimental_qrpa_triality_symmetry (S : ChiralQRPASystem) :
    TrialityInvariantSecular S (emergentToZorn S.geom) ↔ 
    TrialityInvariantSecular S (ZornCore.triality (emergentToZorn S.geom)) := by
  unfold TrialityInvariantSecular
  have h_inv : ZornCore.det (ZornCore.triality (emergentToZorn S.geom)) = ZornCore.det (emergentToZorn S.geom) := by
    apply ZornCore.det_invariant
  rw [h_inv]

end InfoGeometry.Nuclear.TrialityExperimental
