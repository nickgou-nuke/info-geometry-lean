/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# Section 123: Wu–Yang Non-Abelian Aharonov–Bohm Effect and Maxwell–Aharonov–Casher Duality
Target: `InfoGeometry/QuantumContext/WuYangNonAbelianDualABInterferometry.lean`

Formalizes references [4, 5, 21, 54, 55] from Assafrão et al. (2019):
1. Heaviside–Larmor–Maxwell duality (Dowling, Williams & Franson [55], Furtado & Duarte [54]):
   `(E, B) ↦ (B, -E)` and `(d, μ) ↦ (μ, -d)`.
2. Strict Maxwell duality invariance of the combined Aharonov–Casher and He–McKellar–Wilkens
   topological dipole phase density `J_dual = (μ × E) - (d × B)`.
3. Non-Abelian `SU(2)` Wilson holonomy rotor `U = (u₀, u₁, u₂, u₃)` (Wu & Yang [5], Anandan [21]).
4. Euler–Hurwitz four-square identity for non-Abelian diffraction:
   `‖U · Ψ‖² = ‖U‖² · ‖Ψ‖²` (generalizing Brahmagupta–Fibonacci from `U(1)` to `SU(2)`).
5. Strict non-negativity of the non-Abelian transition probability `0 ≤ P_nonAbelian`.
-/

namespace InfoGeometry.QuantumContext.WuYangDualAB

variable {R : Type*} [CommRing R]

/-! ### 1. 3D Vector Carrier and Maxwell–Aharonov–Casher Duality (Refs. [54, 55]) -/

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

/--
Unified topological phase vector combining the Aharonov–Casher (`μ × E`)
and He–McKellar–Wilkens (`- d × B`) dipole phase densities:
`J_dual = (μ × E) - (d × B)`.
-/
def dualTopologicalPhaseVec (D : DipoleDoublet R) (F : EMFieldDoublet R) : Vec3 R :=
  Vec3.sub (Vec3.cross D.mu F.E) (Vec3.cross D.d F.B)

/--
Invariance of the dual Aharonov–Bohm topological phase (Dowling–Williams–Franson [55]):
The topological phase vector `J_dual = (μ × E) - (d × B)` is strictly invariant
under simultaneous Maxwell duality rotation of the fields and dipoles.
-/
theorem dual_ab_phase_maxwell_invariant (D : DipoleDoublet R) (F : EMFieldDoublet R) :
    dualTopologicalPhaseVec (maxwellDipoleDual D) (maxwellFieldDual F) =
      dualTopologicalPhaseVec D F := by
  dsimp [dualTopologicalPhaseVec, maxwellDipoleDual, maxwellFieldDual,
         Vec3.sub, Vec3.cross, Vec3.neg]
  ext <;> ring

/-- Applying Maxwell duality four times is the identity operator (order-4 cycle). -/
theorem maxwell_duality_order_four (F : EMFieldDoublet R) :
    maxwellFieldDual (maxwellFieldDual (maxwellFieldDual (maxwellFieldDual F))) = F := by
  dsimp [maxwellFieldDual, Vec3.neg]
  ext <;> ring

/-! ### 2. Non-Abelian `SU(2)` Holonomy of Wu–Yang and Euler's Four-Square Identity -/

/--
Four-component non-Abelian spinor/holonomy carrier in the quaternion algebra of `SU(2)`:
Represents both the Wu–Yang non-Abelian phase factor `U = (u₀, u₁, u₂, u₃)`
and the two-spinor Fresnel amplitude `Ψ = (ψ₀, ψ₁, ψ₂, ψ₃)`.
-/
@[ext]
structure SU2QuatAmp (R : Type*) where
  q0 : R
  q1 : R
  q2 : R
  q3 : R
  deriving DecidableEq, Repr, Inhabited

namespace SU2QuatAmp

variable {R : Type*} [CommRing R]

def zeroQuat : SU2QuatAmp R := ⟨0, 0, 0, 0⟩

def sampleSU2QuatAmpInt : SU2QuatAmp ℤ := ⟨1, 2, 3, 4⟩

theorem sampleSU2QuatAmpInt_ne_zero :
    sampleSU2QuatAmpInt ≠ zeroQuat := by
  decide

/-- Four-dimensional norm (intensity of the non-Abelian wave): `N(Q) = q₀² + q₁² + q₂² + q₃²`. -/
def normSq (Q : SU2QuatAmp R) : R :=
  Q.q0 * Q.q0 + Q.q1 * Q.q1 + Q.q2 * Q.q2 + Q.q3 * Q.q3

/-- Conjugate non-Abelian operator `Q† = (q₀, -q₁, -q₂, -q₃)`. -/
def conj (Q : SU2QuatAmp R) : SU2QuatAmp R :=
  ⟨Q.q0, -Q.q1, -Q.q2, -Q.q3⟩

/-- Superposition of two non-Abelian amplitudes from the two slits: `Ψ_total = Ψ_+ + Ψ_-`. -/
def add (A B : SU2QuatAmp R) : SU2QuatAmp R :=
  ⟨A.q0 + B.q0, A.q1 + B.q1, A.q2 + B.q2, A.q3 + B.q3⟩

/-- Noncommutative Hamilton–Wu–Yang multiplication for `SU(2)` holonomy transport `U · Ψ`. -/
def mul (U Ψ : SU2QuatAmp R) : SU2QuatAmp R where
  q0 := U.q0 * Ψ.q0 - U.q1 * Ψ.q1 - U.q2 * Ψ.q2 - U.q3 * Ψ.q3
  q1 := U.q0 * Ψ.q1 + U.q1 * Ψ.q0 + U.q2 * Ψ.q3 - U.q3 * Ψ.q2
  q2 := U.q0 * Ψ.q2 - U.q1 * Ψ.q3 + U.q2 * Ψ.q0 + U.q3 * Ψ.q1
  q3 := U.q0 * Ψ.q3 + U.q1 * Ψ.q2 - U.q2 * Ψ.q1 + U.q3 * Ψ.q0

/-- Non-commutativity of `SU2QuatAmp.mul` over `ℤ`. -/
theorem su2QuatAmp_mul_noncommutative :
    let iQ : SU2QuatAmp ℤ := ⟨0, 1, 0, 0⟩
    let jQ : SU2QuatAmp ℤ := ⟨0, 0, 1, 0⟩
    mul iQ jQ ≠ mul jQ iQ := by
  decide

/-- Symmetric 4D inner product `G_SU2(A, B) = ½ Re Tr(A† B)`. -/
def symmInner (A B : SU2QuatAmp R) : R :=
  A.q0 * B.q0 + A.q1 * B.q1 + A.q2 * B.q2 + A.q3 * B.q3

/--
Euler–Hurwitz four-square identity for Wu–Yang non-Abelian holonomy:
The norm of the non-Abelian transported wave `U · Ψ` factorizes into the product
of the `SU(2)` holonomy norm `‖U‖²` and the Fresnel wave norm `‖Ψ‖²`:
`‖U · Ψ‖² = ‖U‖² · ‖Ψ‖²`.
-/
theorem euler_hurwitz_wuyang_norm_identity (U Ψ : SU2QuatAmp R) :
    normSq (mul U Ψ) = normSq U * normSq Ψ := by
  dsimp [normSq, mul]
  ring

/--
Non-Abelian transition probability on the screen under relative holonomy `U` between the slits:
`P_nonAbelian(Ψ_+, Ψ_-, U) = ‖Ψ_+ + U · Ψ_-‖²`.
-/
def nonAbelianTransitionProb (Ψ_pos Ψ_neg U : SU2QuatAmp R) : R :=
  normSq (add Ψ_pos (mul U Ψ_neg))

/--
Expansion of the non-Abelian transition probability into direct intensities and twisted trace:
`‖Ψ_+ + U · Ψ_-‖² = ‖Ψ_+‖² + ‖U‖² ‖Ψ_-‖² + 2 ⟨Ψ_+, U · Ψ_-⟩`.
-/
theorem non_abelian_interference_expansion (Ψ_pos Ψ_neg U : SU2QuatAmp R) :
    nonAbelianTransitionProb Ψ_pos Ψ_neg U =
      normSq Ψ_pos + normSq U * normSq Ψ_neg + 2 * symmInner Ψ_pos (mul U Ψ_neg) := by
  dsimp [nonAbelianTransitionProb, normSq, add, mul, symmInner]
  ring

/--
Strict non-negativity of the Wu–Yang non-Abelian Aharonov–Bohm transition probability:
Since `P_nonAbelian` is a sum of four squares in quaternion space, it is non-negative everywhere.
-/
theorem non_abelian_ab_prob_nonneg {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (Ψ_pos Ψ_neg U : SU2QuatAmp K) :
    0 ≤ nonAbelianTransitionProb Ψ_pos Ψ_neg U := by
  dsimp [nonAbelianTransitionProb, normSq]
  have h01 : 0 ≤ (add Ψ_pos (mul U Ψ_neg)).q0 * (add Ψ_pos (mul U Ψ_neg)).q0 +
                 (add Ψ_pos (mul U Ψ_neg)).q1 * (add Ψ_pos (mul U Ψ_neg)).q1 :=
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have h012 : 0 ≤ (add Ψ_pos (mul U Ψ_neg)).q0 * (add Ψ_pos (mul U Ψ_neg)).q0 +
                  (add Ψ_pos (mul U Ψ_neg)).q1 * (add Ψ_pos (mul U Ψ_neg)).q1 +
                  (add Ψ_pos (mul U Ψ_neg)).q2 * (add Ψ_pos (mul U Ψ_neg)).q2 :=
    add_nonneg h01 (mul_self_nonneg _)
  exact add_nonneg h012 (mul_self_nonneg _)

/--
At the central non-Abelian flux `U = -𝟙 = (-1, 0, 0, 0)` (center of `SU(2)` at `2π` spinor rotation),
the symmetric center `Ψ_+ = Ψ_- = Ψ₀` undergoes complete destructive cancellation: `P = 0`.
-/
theorem su2_center_inversion_destructive_null (Ψ₀ : SU2QuatAmp R) :
    nonAbelianTransitionProb Ψ₀ Ψ₀ ⟨-1, 0, 0, 0⟩ = 0 := by
  dsimp [nonAbelianTransitionProb, normSq, add, mul]
  ring

end SU2QuatAmp

/-! ### 3. Master Synthesis of Section 123 -/

theorem wuyang_dual_ab_master_synthesis {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] :
    (∀ (D : DipoleDoublet R) (F : EMFieldDoublet R),
      dualTopologicalPhaseVec (maxwellDipoleDual D) (maxwellFieldDual F) =
        dualTopologicalPhaseVec D F) ∧
    (∀ (U Ψ : SU2QuatAmp R),
      SU2QuatAmp.normSq (SU2QuatAmp.mul U Ψ) = SU2QuatAmp.normSq U * SU2QuatAmp.normSq Ψ) ∧
    (∀ (Ψ_pos Ψ_neg U : SU2QuatAmp R),
      0 ≤ SU2QuatAmp.nonAbelianTransitionProb Ψ_pos Ψ_neg U) ∧
    (∀ (Ψ₀ : SU2QuatAmp R),
      SU2QuatAmp.nonAbelianTransitionProb Ψ₀ Ψ₀ ⟨-1, 0, 0, 0⟩ = 0) :=
  ⟨dual_ab_phase_maxwell_invariant,
   SU2QuatAmp.euler_hurwitz_wuyang_norm_identity,
   SU2QuatAmp.non_abelian_ab_prob_nonneg,
   SU2QuatAmp.su2_center_inversion_destructive_null⟩

end InfoGeometry.QuantumContext.WuYangDualAB
