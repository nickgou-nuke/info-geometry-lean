/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Finite Maxwell-Duality and Quaternion Interference Identities

The first section proves an identity for a specified transformation of finite
three-coordinate fields and dipoles. The second uses Mathlib's `Quaternion R`
carrier to prove norm preservation for left multiplication by a unit-norm
quaternion and the corresponding finite interference-norm expansion.

These algebraic results do not construct Maxwell dynamics, a Wu–Yang holonomy,
an `SU(2)` representation, a path-dependent Aharonov–Casher phase, or a
normalized Born probability. Those interpretations require additional objects
and proved bridges.
-/

namespace InfoGeometry.QuantumContext.WuYangDualAB

variable {R : Type*} [CommRing R]

/-! ### 1. Finite 3D Vector Identities for the Specified Dual Transformation -/

@[ext]
structure Vec3 (R : Type*) where
  x : R
  y : R
  z : R
  deriving DecidableEq, Repr, Inhabited

namespace Vec3

variable {R : Type*} [CommRing R]

def zeroVec3 : Vec3 R := ⟨0, 0, 0⟩

def sampleVec3Int : Vec3 ℤ := ⟨1, 2, 3⟩

theorem sampleVec3Int_ne_zero :
    sampleVec3Int ≠ zeroVec3 := by
  decide

def neg (u : Vec3 R) : Vec3 R :=
  ⟨-u.x, -u.y, -u.z⟩

def sub (u v : Vec3 R) : Vec3 R :=
  ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

def cross (u v : Vec3 R) : Vec3 R where
  x := u.y * v.z - u.z * v.y
  y := u.z * v.x - u.x * v.z
  z := u.x * v.y - u.y * v.x

/-- Non-commutativity of the 3D cross product over `ℤ`. -/
theorem cross_noncommutative_int :
    let u : Vec3 ℤ := ⟨1, 0, 0⟩
    let v : Vec3 ℤ := ⟨0, 1, 0⟩
    cross u v ≠ cross v u := by
  decide

end Vec3

/-- Electromagnetic field doublet `(E, B)`. -/
@[ext]
structure EMFieldDoublet (R : Type*) where
  E : Vec3 R
  B : Vec3 R
  deriving DecidableEq, Repr, Inhabited

def zeroEMFieldDoublet : EMFieldDoublet R := ⟨Vec3.zeroVec3, Vec3.zeroVec3⟩

def sampleEMFieldDoubletInt : EMFieldDoublet ℤ := ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩⟩

theorem sampleEMFieldDoubletInt_ne_zero :
    sampleEMFieldDoubletInt ≠ zeroEMFieldDoublet := by
  decide

/-- Dipole doublet `(d, μ)` of an electric dipole `d` and magnetic spin dipole `μ`. -/
@[ext]
structure DipoleDoublet (R : Type*) where
  d  : Vec3 R
  mu : Vec3 R
  deriving DecidableEq, Repr, Inhabited

def zeroDipoleDoublet : DipoleDoublet R := ⟨Vec3.zeroVec3, Vec3.zeroVec3⟩

def sampleDipoleDoubletInt : DipoleDoublet ℤ := ⟨⟨0, 1, 0⟩, ⟨0, 0, 1⟩⟩

theorem sampleDipoleDoubletInt_ne_zero :
    sampleDipoleDoubletInt ≠ zeroDipoleDoublet := by
  decide

/-- Maxwell duality transformation on electromagnetic fields: `(E, B) ↦ (B, -E)`. -/
def maxwellFieldDual (F : EMFieldDoublet R) : EMFieldDoublet R :=
  ⟨F.B, Vec3.neg F.E⟩

/-- Maxwell duality transformation on dipoles: `(d, μ) ↦ (μ, -d)`. -/
def maxwellDipoleDual (D : DipoleDoublet R) : DipoleDoublet R :=
  ⟨D.mu, Vec3.neg D.d⟩

/-- Difference of the two finite cross-product coordinates used in the model.
This definition alone does not encode a path-dependent topological phase. -/
def dualCrossProductDifference (D : DipoleDoublet R) (F : EMFieldDoublet R) : Vec3 R :=
  Vec3.sub (Vec3.cross D.mu F.E) (Vec3.cross D.d F.B)

/-- The displayed finite cross-product difference is invariant under the two
specified dual transformations. This is an algebraic identity, not a theorem
about electromagnetic dynamics or a path-dependent phase. -/
theorem dualCrossProductDifference_maxwell_invariant (D : DipoleDoublet R) (F : EMFieldDoublet R) :
    dualCrossProductDifference (maxwellDipoleDual D) (maxwellFieldDual F) =
      dualCrossProductDifference D F := by
  dsimp [dualCrossProductDifference, maxwellDipoleDual, maxwellFieldDual,
         Vec3.sub, Vec3.cross, Vec3.neg]
  ext <;> ring

/-- Applying Maxwell duality four times is the identity operator (order-4 cycle). -/
theorem maxwell_duality_order_four (F : EMFieldDoublet R) :
    maxwellFieldDual (maxwellFieldDual (maxwellFieldDual (maxwellFieldDual F))) = F := by
  dsimp [maxwellFieldDual, Vec3.neg]
  ext <;> ring

/-! ### 2. Hamilton-quaternion interference norm -/

/-- Left multiplication by a unit-norm quaternion preserves squared norm.
This is the finite algebraic isometry consequence of the quaternion norm law;
`U` is constrained by `hU` rather than assumed to be an `SU(2)` holonomy. -/
theorem unit_quaternion_left_mul_preserves_normSq
    (U Ψ : Quaternion R) (hU : Quaternion.normSq U = 1) :
    Quaternion.normSq (U * Ψ) = Quaternion.normSq Ψ := by
  rw [Quaternion.normSq.map_mul, hU, one_mul]

/-- Squared norm of the finite quaternion-coordinate interference sum.
This scalar is not asserted to be a normalized Born probability. -/
def quaternionInterferenceNormSq
    (Ψ_pos Ψ_neg U : Quaternion R) : R :=
  Quaternion.normSq (Ψ_pos + U * Ψ_neg)

/-- Expansion of the interference norm using the native quaternion norm.
The cross term is the real scalar part of `Ψ_pos * star (U * Ψ_neg)`. -/
theorem quaternion_interference_normSq_expansion
    (Ψ_pos Ψ_neg U : Quaternion R) :
    quaternionInterferenceNormSq Ψ_pos Ψ_neg U =
      Quaternion.normSq Ψ_pos +
        Quaternion.normSq U * Quaternion.normSq Ψ_neg +
        2 * (Ψ_pos * star (U * Ψ_neg)).re := by
  unfold quaternionInterferenceNormSq
  rw [Quaternion.normSq_add, Quaternion.normSq.map_mul]

/-- The finite quaternion interference norm is nonnegative over an ordered
commutative ring. -/
theorem quaternion_interference_normSq_nonneg
    {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (Ψ_pos Ψ_neg U : Quaternion K) :
    0 ≤ quaternionInterferenceNormSq Ψ_pos Ψ_neg U :=
  Quaternion.normSq_nonneg

/-- At the scalar element `-1`, equal quaternion amplitudes cancel exactly.
No path or spin-rotation interpretation is included in this identity. -/
theorem scalar_minus_one_interference_cancellation (Ψ : Quaternion R) :
    quaternionInterferenceNormSq Ψ Ψ (-1) = 0 := by
  simp [quaternionInterferenceNormSq]

end InfoGeometry.QuantumContext.WuYangDualAB
