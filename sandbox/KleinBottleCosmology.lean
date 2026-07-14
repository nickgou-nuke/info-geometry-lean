import Mathlib
import InfoGeometry.Topology.Q8MonodromySpinorCover
import InfoGeometry.Topology.BrillouinKleinBottleManifold
import InfoGeometry.Canonical.KleinBottleSewing
import InfoGeometry.Canonical.KleinBoundaryStates
import InfoGeometry.Clifford.Pin55ReflectionGlide
import InfoGeometry.Physics.KleinBottleDefects

namespace InfoGeometry.Physics.KleinBottleCosmology

open InfoGeometry.Topology.Q8MonodromySpinorCover
open InfoGeometry.Topology.BrillouinKleinBottleManifold
open InfoGeometry.Clifford.Pin55ReflectionGlide

noncomputable section

/-- Matrix-level Q₈ generators satisfy the defining square relations. -/
theorem quaternions_M_i_sq : M_i * M_i = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_i, Matrix.mul_apply]

/-- Matrix-level Q₈ generators satisfy the defining square relations. -/
theorem quaternions_M_j_sq : M_j * M_j = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_j, Matrix.mul_apply]

/-- Matrix-level Q₈ generators satisfy the defining square relations. -/
theorem quaternions_M_k_sq : M_k * M_k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_k, Matrix.mul_apply]

/-- Matrix-level Q₈ anticommutation of two generators. -/
theorem quaternions_M_i_M_j_anticommute : M_i * M_j = -(M_j * M_i) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_i,
    InfoGeometry.Topology.Q8MonodromySpinorCover.M_j, Matrix.mul_apply]

/-- `M_i*M_j*M_k = -1` follows directly from matrix evaluation. -/
theorem quaternions_M_i_M_j_M_k : M_i * M_j * M_k = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [InfoGeometry.Topology.Q8MonodromySpinorCover.M_i,
    InfoGeometry.Topology.Q8MonodromySpinorCover.M_j,
    InfoGeometry.Topology.Q8MonodromySpinorCover.M_k, Matrix.mul_apply]

/-- Full local Q₈ certificate used by the physical Klein spinor cover story. -/
structure QuaternionsSpinorCoverCertificate where
  M_i_sq : M_i * M_i = -1
  M_j_sq : M_j * M_j = -1
  M_k_sq : M_k * M_k = -1
  M_i_M_j_anticommute : M_i * M_j = -(M_j * M_i)
  M_i_M_j_M_k : M_i * M_j * M_k = -1

/-- Concrete instantiation of the Q₈ certificate. -/
def instQuaternionsSpinorCoverCertificate : QuaternionsSpinorCoverCertificate where
  M_i_sq := quaternions_M_i_sq
  M_j_sq := quaternions_M_j_sq
  M_k_sq := quaternions_M_k_sq
  M_i_M_j_anticommute := quaternions_M_i_M_j_anticommute
  M_i_M_j_M_k := quaternions_M_i_M_j_M_k

/-- Glide conjugates the vertical loop to its inverse in the finite Brillouin chart. -/
theorem brillouin_glide_conjugates_to_inverse (p : KPoint) :
    glide (yLoop (glideInv p)) = yLoopInv p := by
  ext i
  fin_cases i
  · simp [InfoGeometry.Topology.BrillouinKleinBottleManifold.glide,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.glideInv,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoop,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoopInv]
  · simp [InfoGeometry.Topology.BrillouinKleinBottleManifold.glide,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.glideInv,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoop,
      InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoopInv]
    ring

/-- Klein boundary word reduction of one conjugated vertical loop. -/
theorem brillouin_boundary_word (p : KPoint) :
    glide (yLoop (glideInv (yLoop p))) = p := by
  rw [brillouin_glide_conjugates_to_inverse]
  ext i
  fin_cases i <;> simp [InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoop,
    InfoGeometry.Topology.BrillouinKleinBottleManifold.yLoopInv]

/-- Reflection+half-translation glide squares to a unit translation in Split(5,5). -/
theorem pin55_glide_square_eq_translation (x : Split55) :
    InfoGeometry.Clifford.Pin55ReflectionGlide.glide (InfoGeometry.Clifford.Pin55ReflectionGlide.glide x)
      = InfoGeometry.Clifford.Pin55ReflectionGlide.translateP 1 x := by
  unfold InfoGeometry.Clifford.Pin55ReflectionGlide.glide
  rw [pinReflection_translateP_comm]
  rw [pinReflection_involutive]
  rw [translateP_add]
  norm_num

/-- Sewing symmetry implies vanishing chiral trace readout. -/
theorem sewn_boundary_chiral_index_vanishes (s : BoundaryState) (h : isSewn s) :
    chiralIndex s = 0 :=
  klein_throat_anomaly_vanishes s h

/-- `5`-`7` defect balance on the trivalent Klein/Torus topology. -/
theorem klein_bottle_five_seven_balance
  (V E F F5 F6 F7 : ℕ)
  (hEuler : V + F = E)
  (hRegular : 3 * V = 2 * E)
  (hFaces : F = F5 + F6 + F7)
  (hEdges : 2 * E = 5 * F5 + 6 * F6 + 7 * F7) :
  F5 = F7 :=
  InfoGeometry.Physics.klein_bottle_defects_balance V E F F5 F6 F7 hEuler hRegular hFaces hEdges

/-- Nonorientability reverses signed Chern data; therefore the invariant vanishes. -/
theorem orientation_reversal_forces_zero (c : ℤ) (h : c = -c) :
    c = 0 := by
  omega

/-- Full finite bridge packet for the Klein-cosmology lane. -/
structure KleinBottleCosmologyPacket (p : KPoint) (x : Split55) (s : BoundaryState) (hSew : isSewn s) where
  M_i_sq : M_i * M_i = -1
  M_j_sq : M_j * M_j = -1
  M_k_sq : M_k * M_k = -1
  M_i_M_j_anticommute : M_i * M_j = -(M_j * M_i)
  glide_conj : glide (yLoop (glideInv p)) = yLoopInv p
  boundary_word : glide (yLoop (glideInv (yLoop p))) = p
  pin55_glide_sq : InfoGeometry.Clifford.Pin55ReflectionGlide.glide (InfoGeometry.Clifford.Pin55ReflectionGlide.glide x) = InfoGeometry.Clifford.Pin55ReflectionGlide.translateP 1 x
  chiral_index : chiralIndex s = 0

/-- Concrete instantiation of the Klein-cosmology packet. -/
def instKleinBottleCosmologyPacket
    (p : KPoint)
    (x : Split55)
    (s : BoundaryState)
    (hSew : isSewn s) : KleinBottleCosmologyPacket p x s hSew where
  M_i_sq := quaternions_M_i_sq
  M_j_sq := quaternions_M_j_sq
  M_k_sq := quaternions_M_k_sq
  M_i_M_j_anticommute := quaternions_M_i_M_j_anticommute
  glide_conj := brillouin_glide_conjugates_to_inverse p
  boundary_word := brillouin_boundary_word p
  pin55_glide_sq := pin55_glide_square_eq_translation x
  chiral_index := sewn_boundary_chiral_index_vanishes s hSew

end
end InfoGeometry.Physics.KleinBottleCosmology
