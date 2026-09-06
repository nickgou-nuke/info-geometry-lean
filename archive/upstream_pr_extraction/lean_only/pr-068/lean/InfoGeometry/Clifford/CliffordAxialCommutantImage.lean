/-
# Axial Clifford bivectors and their opposite-frame image

For a three-direction operator frame, the antisymmetric commutator channel is
a bivector channel.  The axial channel is its oriented cyclic/Hodge readout,
with any parity factor kept explicit.  An anti-automorphism reverses products;
therefore it sends a commutator to the negative commutator of the transformed
generators and moves a left parity factor to the right:
`Θ (χ * B) = Θ B * Θ χ` (with the commutator sign contained in `Θ B`).

This owner proves only algebraic anti-transport identities.  It does not
identify an arbitrary anti-automorphism with modular conjugation, a spectral
triple commutant, a Morita equivalence, or a differential spin connection.
-/

import InfoGeometry.Clifford.OperatorValuedChiralCliffordFrame
import InfoGeometry.Physics.AlgebraicTomitaTakesakiBridge

noncomputable section

namespace InfoGeometry.Clifford.CliffordAxialCommutantImage

open InfoGeometry.Clifford.OperatorValuedChiralCliffordFrame
open InfoGeometry.Physics
open InfoGeometry.Physics.AlgebraicTomitaTakesaki

variable {R Op : Type*}
variable [Field R] [CharZero R] [Ring Op] [Algebra R Op]

theorem anti_map_zero (J : AntiAutomorphism Op) :
    J.toFun 0 = 0 := by
  have h := J.map_add 0 0
  have h' : J.toFun 0 + 0 = J.toFun 0 + J.toFun 0 := by
    simpa using h
  exact (add_left_cancel h').symm

theorem anti_map_neg (J : AntiAutomorphism Op) (x : Op) :
    J.toFun (-x) = -J.toFun x := by
  have h := J.map_add x (-x)
  rw [show x + -x = 0 by simp, anti_map_zero J] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem anti_map_sub (J : AntiAutomorphism Op) (x y : Op) :
    J.toFun (x - y) = J.toFun x - J.toFun y := by
  rw [sub_eq_add_neg, J.map_add, anti_map_neg]
  simp only [sub_eq_add_neg]

def mirroredFrame
    (J : AntiAutomorphism Op) (F : Frame (Fin 3) R Op) : Frame (Fin 3) R Op where
  gamma := fun i => J.toFun (F.gamma i)
  metric := F.metric

def rawBivector
    (F : Frame (Fin 3) R Op) (i j : Fin 3) : Op :=
  F.gamma i * F.gamma j - F.gamma j * F.gamma i

def cyclicPair : Fin 3 → Fin 3 × Fin 3
  | ⟨0, _⟩ => (⟨1, by decide⟩, ⟨2, by decide⟩)
  | ⟨1, _⟩ => (⟨2, by decide⟩, ⟨0, by decide⟩)
  | ⟨2, _⟩ => (⟨0, by decide⟩, ⟨1, by decide⟩)
  | ⟨n + 3, h⟩ => Fin.elim0 (by omega)

def hodgeAxialReadout (B : Fin 3 → Fin 3 → Op) (k : Fin 3) : Op :=
  B (cyclicPair k).1 (cyclicPair k).2

def axialGenerator (F : Frame (Fin 3) R Op) (k : Fin 3) : Op :=
  hodgeAxialReadout (fun i j => rawBivector F i j) k

def chiralAxialGenerator
    (χ : Op) (F : Frame (Fin 3) R Op) (k : Fin 3) : Op :=
  χ * axialGenerator F k

def mirroredChiralAxialGenerator
    (J : AntiAutomorphism Op) (χ : Op) (F : Frame (Fin 3) R Op) (k : Fin 3) : Op :=
  -(axialGenerator (mirroredFrame J F) k) * J.toFun χ

theorem anti_image_rawBivector
    (J : AntiAutomorphism Op) (F : Frame (Fin 3) R Op) (i j : Fin 3) :
    J.toFun (rawBivector F i j) =
      -rawBivector (mirroredFrame J F) i j := by
  unfold rawBivector mirroredFrame
  rw [anti_map_sub, J.map_mul, J.map_mul]
  noncomm_ring

theorem anti_image_axialGenerator
    (J : AntiAutomorphism Op) (F : Frame (Fin 3) R Op) (k : Fin 3) :
    J.toFun (axialGenerator F k) =
      -axialGenerator (mirroredFrame J F) k := by
  unfold axialGenerator
  exact anti_image_rawBivector J F _ _

theorem anti_image_chiralAxialGenerator
    (J : AntiAutomorphism Op) (χ : Op) (F : Frame (Fin 3) R Op) (k : Fin 3) :
    J.toFun (chiralAxialGenerator χ F k) =
      mirroredChiralAxialGenerator J χ F k := by
  unfold chiralAxialGenerator mirroredChiralAxialGenerator
  rw [J.map_mul, anti_image_axialGenerator]

end InfoGeometry.Clifford.CliffordAxialCommutantImage
