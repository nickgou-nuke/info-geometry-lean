import Mathlib.Tactic
import InfoGeometry.Projective.ArnoldRelations

/-!
# Three-Point Amplituhedron Boundary Operators

This file records the finite algebraic surface behind the requested
three-channel boundary calculation.

Closed here:

* a three-point boundary packet has three nilpotent on-shell edge operators and
  three logarithmic channel forms;
* the advertised "super-amplitude volume" is exactly the three-term mixed
  expression;
* left multiplication by an on-shell nilpotent edge removes its own channel;
* if a separate owner supplies that the mixed expression vanishes, an arbitrary
  BCFW-style readout follows through the supplied comparison implication.

Not closed here:

* no amplituhedron or positive Grassmannian is constructed;
* no theorem identifies this algebraic packet with `F_Q(C^4,3)` de Rham
  cohomology;
* no BCFW recursion theorem is derived;
* no `N = 4` SYM state-count theorem or rank-32 cohomology theorem is proved.
-/

namespace InfoGeometry.Topology.AmplituhedronBoundary

open InfoGeometry.Projective.Amplituhedron

variable (R : Type*) [CommRing R] (ι : Type*)

noncomputable instance : Ring (ArnoldAlgebra R ι) :=
  inferInstanceAs (Ring (RingQuot (ArnoldRel R ι)))

structure ThreePointPacket where
  i : ι
  j : ι
  k : ι
  edge_ij : ArnoldAlgebra R ι
  edge_jk : ArnoldAlgebra R ι
  edge_ki : ArnoldAlgebra R ι
  chan_ij : ArnoldAlgebra R ι
  chan_jk : ArnoldAlgebra R ι
  chan_ki : ArnoldAlgebra R ι
  nil_ij : edge_ij * edge_ij = 0
  nil_jk : edge_jk * edge_jk = 0
  nil_ki : edge_ki * edge_ki = 0
  rem_ij : edge_ij * chan_ij = 0
  rem_jk : edge_jk * chan_jk = 0
  rem_ki : edge_ki * chan_ki = 0

variable {R ι}

noncomputable def superAmplitudeVolume (p : ThreePointPacket R ι) : ArnoldAlgebra R ι :=
  p.chan_ij * p.chan_jk + p.chan_jk * p.chan_ki + p.chan_ki * p.chan_ij

lemma edge_mul_vol_eq (p : ThreePointPacket R ι) :
    p.edge_ij * superAmplitudeVolume p = p.edge_ij * (p.chan_jk * p.chan_ki + p.chan_ki * p.chan_ij) := by
  dsimp [superAmplitudeVolume]
  rw [mul_add, mul_add]
  have h1 : p.edge_ij * (p.chan_ij * p.chan_jk) = 0 := by
    rw [← mul_assoc, p.rem_ij, zero_mul]
  rw [h1, zero_add, ← mul_add]

theorem bcfw_readout (p : ThreePointPacket R ι) (h_vol : superAmplitudeVolume p = 0) :
    p.edge_ij * (p.chan_jk * p.chan_ki + p.chan_ki * p.chan_ij) = 0 := by
  rw [← edge_mul_vol_eq, h_vol, mul_zero]

lemma omega_sq_zero (i j : ι) : omega R ι i j * omega R ι i j = 0 := by
  dsimp [omega]
  change (RingQuot.mkRingHom (ArnoldRel R ι)) (w R ι i j) * (RingQuot.mkRingHom (ArnoldRel R ι)) (w R ι i j) = 0
  rw [← map_mul]
  have h : w R ι i j * w R ι i j = 0 := ExteriorAlgebra.ι_sq_zero (Finsupp.single (i, j) (1 : R))
  rw [h, map_zero]

noncomputable def standardPacket (i j k : ι) : ThreePointPacket R ι where
  i := i
  j := j
  k := k
  edge_ij := omega R ι i j
  edge_jk := omega R ι j k
  edge_ki := omega R ι k i
  chan_ij := omega R ι i j
  chan_jk := omega R ι j k
  chan_ki := omega R ι k i
  nil_ij := omega_sq_zero i j
  nil_jk := omega_sq_zero j k
  nil_ki := omega_sq_zero k i
  rem_ij := omega_sq_zero i j
  rem_jk := omega_sq_zero j k
  rem_ki := omega_sq_zero k i

end InfoGeometry.Topology.AmplituhedronBoundary
