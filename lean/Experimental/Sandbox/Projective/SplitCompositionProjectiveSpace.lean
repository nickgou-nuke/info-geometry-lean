import InfoGeometry.Clifford.CockleCoquaternionPlanarTriad
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false

/-!
# Voelkel Split Composition Projective Spaces, Hermitian Projectors, and the Motivic Quadric Sphere S^(4,2)

This module formalizes Pillar 1 of the Voelkel Motivic Cells roadmap
(`docs/VOELKEL_SPLIT_QUATERNION_MOTIVIC_CELLS_ROADMAP.md`), following:
- Konrad Voelkel, *Motivic Cell Structures for Projective Spaces over Split Quaternions*,
  PhD thesis, Freiburg, 2016 (Chapter 4, Definitions 4.1.7, 4.1.14, 4.1.16, Theorem 4.4.6).

## Mathematical Structure
1. **Split Quaternions and Involutive Conjugation**:
   - Carrier $\mathbb{D} = \mathrm{Coquaternion}(R)$ over any commutative ring $R$,
     with basis $\{1, e_1, e_2, \omega\}$ where $e_1^2 = +1, e_2^2 = -1, \omega^2 = +1$.
   - Principal anti-involution: $\overline{q} = \langle s, -x, -y, -z \rangle$.
   - Involution laws: $\overline{\overline{q}} = q$, $\overline{p \cdot q} = \overline{q} \cdot \overline{p}$.
   - Norm-scalar identity: $q \cdot \overline{q} = \overline{q} \cdot q = N(q) \cdot 1$.

2. **2D Projective Vector Carrier and Split Quadric Spheres**:
   - Vector carrier $v = (v_1, v_2) \in \mathbb{D}^2$.
   - Quadratic norm: $N_2(v) = N(v_1) + N(v_2)$.
   - Signature decomposition:
     * $\mathbb{D} \cong \mathbb{R}^4$ has signature $(2,2)$: $(s^2 + y^2) - (x^2 + z^2)$.
       The sphere $N(q) = 1$ is the affine quadric $Q_{2,2} \subset \mathbb{R}^4$,
       which is the geometric carrier of the motivic sphere $S^{(4,2)}$ (Voelkel Theorem 4.4.6).
     * $\mathbb{D}^2 \cong \mathbb{R}^8$ has signature $(4,4)$:
       $(s_1^2 + y_1^2 + s_2^2 + y_2^2) - (x_1^2 + z_1^2 + x_2^2 + z_2^2)$.
       The sphere $N_2(v) = 1$ is the affine quadric $Q_{4,4} \subset \mathbb{R}^8$.

3. **Voelkel's $\mathbb{D}\mathrm{P}^1$ Hermitian Projector Model**:
   - Projector matrix $P(v) = \begin{pmatrix} v_1 \overline{v}_1 & v_1 \overline{v}_2 \\ v_2 \overline{v}_1 & v_2 \overline{v}_2 \end{pmatrix} \in M_2(\mathbb{D})$.
   - Universal scaling identity: $P(v)^2 = N_2(v) \cdot P(v)$.
   - Idempotency on the sphere: $N_2(v) = 1 \implies P(v)^2 = P(v)$.
   - Unit trace: $\mathrm{Tr}(P(v)) = (N_2(v)) \cdot 1$, so $N_2(v) = 1 \implies \mathrm{Tr}(P(v)) = 1$.
   - Hermitian self-adjointness: $P(v)^* = P(v)$ under conjugate transpose.

4. **Affine Chart Trivialization and Coordinate Complement**:
   - In the affine chart $v_1 = 1, v_2 = z \in \mathbb{D}$:
     $P(1, z) = \begin{pmatrix} 1 & \overline{z} \\ z & N(z) \cdot 1 \end{pmatrix}$.
   - Normalized projector $P_c(z) = c \cdot P(1, z)$ where $c(1 + N(z)) = 1$:
     $P_c(z)^2 = P_c(z)$, $\mathrm{Tr}(P_c(z)) = 1$, and $P_c(z)^* = P_c(z)$.
-/

namespace InfoGeometry.Projective.SplitComposition

open Matrix
open InfoGeometry.Clifford.Coquaternion
open InfoGeometry.Clifford.Coquaternion.Coquaternion

variable {R : Type*} [CommRing R]

/-! ### Section 1: Involutive Conjugation on Coquaternions -/

/-- Principal anti-involution (quaternionic conjugation) on Cockle's coquaternions:
    conj(s, x, y, z) = ⟨s, -x, -y, -z⟩. -/
def conj (q : Coquaternion R) : Coquaternion R :=
  ⟨q.s, -q.x, -q.y, -q.z⟩

@[simp] theorem conj_s (q : Coquaternion R) : (conj q).s = q.s := rfl
@[simp] theorem conj_x (q : Coquaternion R) : (conj q).x = -q.x := rfl
@[simp] theorem conj_y (q : Coquaternion R) : (conj q).y = -q.y := rfl
@[simp] theorem conj_z (q : Coquaternion R) : (conj q).z = -q.z := rfl

/-- Involutive property: conj(conj(q)) = q. -/
@[simp]
theorem conj_conj (q : Coquaternion R) : conj (conj q) = q := by
  ext <;> simp [conj]

/-- Conjugation of zero is zero. -/
@[simp]
theorem conj_zero : conj (0 : Coquaternion R) = 0 := by
  ext <;> simp [conj]

/-- Conjugation of identity is identity. -/
@[simp]
theorem conj_one : conj (1 : Coquaternion R) = 1 := by
  ext <;> simp [conj]

/-- Conjugation is additive: conj(p + q) = conj(p) + conj(q). -/
theorem conj_add (p q : Coquaternion R) : conj (p + q) = conj p + conj q := by
  ext <;> { simp [conj]; try ring }

/-- Conjugation respects negation: conj(-q) = -conj(q). -/
theorem conj_neg (q : Coquaternion R) : conj (-q) = -conj q := by
  ext <;> simp [conj]

/-- Conjugation respects scalar multiplication: conj(c • q) = c • conj(q). -/
theorem conj_smul (c : R) (q : Coquaternion R) : conj (c • q) = c • conj q := by
  ext <;> simp [conj]

/-- Anti-multiplicative property of conjugation:
    conj(p * q) = conj(q) * conj(p). -/
theorem conj_mul (p q : Coquaternion R) : conj (p * q) = conj q * conj p := by
  ext <;> { simp [conj]; ring }

/-- Fundamental norm identity: q * conj(q) = normSq(q) • 1. -/
theorem mul_conj (q : Coquaternion R) : q * conj q = (normSq q) • (1 : Coquaternion R) := by
  ext <;> { simp [conj, normSq]; ring }

/-- Reverse fundamental norm identity: conj(q) * q = normSq(q) • 1. -/
theorem conj_mul_self (q : Coquaternion R) : conj q * q = (normSq q) • (1 : Coquaternion R) := by
  ext <;> { simp [conj, normSq]; ring }

/-- Conjugation of the norm scalar: conj(N(q) • 1) = N(q) • 1. -/
theorem conj_normSq_smul_one (q : Coquaternion R) :
    conj ((normSq q) • (1 : Coquaternion R)) = (normSq q) • (1 : Coquaternion R) := by
  ext <;> simp [conj]

/-- Scalar multiplication distributes across coquaternion multiplication:
    (c • p) * (d • q) = (c * d) • (p * q). -/
theorem smul_mul_smul_coquaternion (c d : R) (p q : Coquaternion R) :
    (c • p) * (d • q) = (c * d) • (p * q) := by
  ext <;> { simp; ring }

/-! ### Section 2: Module and Group Instances for Coquaternion -/

instance : AddCommGroup (Coquaternion R) where
  add_assoc := fun p q r => by ext <;> { simp; try ring }
  zero_add := fun q => by ext <;> simp
  add_zero := fun q => by ext <;> simp
  nsmul := nsmulRec
  add_comm := fun p q => by ext <;> { simp; try ring }
  neg_add_cancel := fun q => by ext <;> { simp; try ring }
  sub_eq_add_neg := fun p q => by ext <;> { simp; try ring }
  zsmul := zsmulRec

instance : MulAction R (Coquaternion R) where
  one_smul := fun q => by
    cases q
    ext <;> simp
  mul_smul := fun c d q => by
    cases q
    ext <;> { simp; try ring }

/-! ### Section 3: 2D Projective Vector Carrier and Split Quadric Spheres -/

/-- 2D vector carrier over the split composition algebra D = Coquaternion R. -/
@[ext]
structure SphereVector2 (R : Type*) where
  v1 : Coquaternion R
  v2 : Coquaternion R

namespace SphereVector2

/-- Zero vector in D^2. -/
def zero : SphereVector2 R := ⟨0, 0⟩

/-- Addition of vectors in D^2. -/
def add (u v : SphereVector2 R) : SphereVector2 R :=
  ⟨u.v1 + v.v1, u.v2 + v.v2⟩

/-- Scalar multiplication of vectors in D^2. -/
def smul (c : R) (v : SphereVector2 R) : SphereVector2 R :=
  ⟨c • v.v1, c • v.v2⟩

instance : Zero (SphereVector2 R) := ⟨zero⟩
instance : Add (SphereVector2 R) := ⟨add⟩
instance : SMul R (SphereVector2 R) := ⟨smul⟩

end SphereVector2

/-- Total split quadratic norm on D^2: N_2(v) = N(v1) + N(v2). -/
def normSq2 (v : SphereVector2 R) : R :=
  normSq v.v1 + normSq v.v2

/-- Positive definite part of the norm on D = R^4: s^2 + y^2 (2 positive squares). -/
def posNorm4 (q : Coquaternion R) : R :=
  q.s^2 + q.y^2

/-- Negative definite part of the norm on D = R^4: x^2 + z^2 (2 negative squares). -/
def negNorm4 (q : Coquaternion R) : R :=
  q.x^2 + q.z^2

/-- Signature (2,2) decomposition of the coquaternion reduced norm:
    N(q) = (s^2 + y^2) - (x^2 + z^2). -/
theorem normSq_signature_22 (q : Coquaternion R) :
    normSq q = posNorm4 q - negNorm4 q := by
  dsimp [normSq, posNorm4, negNorm4]
  ring

/-- Positive definite part of the norm on D^2 = R^8: 4 positive squares. -/
def posNorm8 (v : SphereVector2 R) : R :=
  posNorm4 v.v1 + posNorm4 v.v2

/-- Negative definite part of the norm on D^2 = R^8: 4 negative squares. -/
def negNorm8 (v : SphereVector2 R) : R :=
  negNorm4 v.v1 + negNorm4 v.v2

/-- Signature (4,4) decomposition of the 2D sphere norm on R^8:
    N_2(v) = (s1^2 + y1^2 + s2^2 + y2^2) - (x1^2 + z1^2 + x2^2 + z2^2). -/
theorem normSq2_signature_44 (v : SphereVector2 R) :
    normSq2 v = posNorm8 v - negNorm8 v := by
  dsimp [normSq2, posNorm8, negNorm8, posNorm4, negNorm4, normSq]
  ring

/-- Coordinate expansion of N_2(v) in all 8 scalar coordinates. -/
theorem normSq2_coordinate_expansion (v : SphereVector2 R) :
    normSq2 v = (v.v1.s^2 - v.v1.x^2 + v.v1.y^2 - v.v1.z^2) +
                (v.v2.s^2 - v.v2.x^2 + v.v2.y^2 - v.v2.z^2) := by
  dsimp [normSq2, normSq]

/-- Affine quadric Q_{2,2} ⊂ R^4, the geometric carrier of the motivic sphere S^(4,2)
    (Voelkel Theorem 4.4.6). -/
def IsQuadric22 (q : Coquaternion R) : Prop :=
  normSq q = 1

/-- Affine quadric Q_{4,4} ⊂ R^8, the geometric carrier of the 2D unit sphere D S^1. -/
def IsUnitSphere2 (v : SphereVector2 R) : Prop :=
  normSq2 v = 1

/-! ### Section 4: Voelkel's DP^1 Hermitian Projector Model -/

abbrev Mat2D (R : Type*) := Matrix (Fin 2) (Fin 2) (Coquaternion R)

/-- Voelkel's projector map P: D^2 → M_2(D), v ↦ v * v^*:
    P(v1, v2) = !![ v1 * conj v1, v1 * conj v2 ;
                    v2 * conj v1, v2 * conj v2 ]. -/
def projector (v : SphereVector2 R) : Mat2D R :=
  !![ v.v1 * conj v.v1, v.v1 * conj v.v2;
      v.v2 * conj v.v1, v.v2 * conj v.v2 ]

/-- Standard 2x2 matrix trace on M_2(D). -/
def trace2 (M : Mat2D R) : Coquaternion R :=
  M 0 0 + M 1 1

/-- Conjugate transpose involution on M_2(D): M^*(i, j) = conj(M(j, i)). -/
def conjTranspose2 (M : Mat2D R) : Mat2D R :=
  !![ conj (M 0 0), conj (M 1 0);
      conj (M 0 1), conj (M 1 1) ]

/-- Scalar trace formula: trace2(P(v)) = (N_2(v)) • 1. -/
theorem projector_trace2 (v : SphereVector2 R) :
    trace2 (projector v) = (normSq2 v) • (1 : Coquaternion R) := by
  dsimp [trace2, projector, normSq2]
  rw [mul_conj, mul_conj]
  ext <;> { simp; try ring }

/-- On the unit sphere N_2(v) = 1, the trace is the identity 1 • 1. -/
theorem projector_trace2_unit (v : SphereVector2 R) (hv : normSq2 v = 1) :
    trace2 (projector v) = 1 := by
  rw [projector_trace2, hv]
  ext <;> simp

/-- Matrix trace on M_2(D) matches trace2. -/
theorem matrix_trace_eq_trace2 (M : Mat2D R) :
    Matrix.trace M = trace2 M := by
  dsimp [trace2, Matrix.trace]
  rw [Fin.sum_univ_two]

/-- Projector trace in terms of Mathlib's Matrix.trace. -/
theorem projector_matrix_trace_unit (v : SphereVector2 R) (hv : normSq2 v = 1) :
    Matrix.trace (projector v) = 1 := by
  rw [matrix_trace_eq_trace2, projector_trace2_unit v hv]

/-- Hermitian self-adjointness: P(v)^* = P(v) holds unconditionally for any vector v. -/
theorem projector_hermitian (v : SphereVector2 R) :
    conjTranspose2 (projector v) = projector v := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> {
    dsimp [conjTranspose2, projector]
    rw [conj_mul, conj_conj]
  }

/-- Universal scaling identity: P(v) * P(v) = N_2(v) • P(v).
    This polynomial identity holds unconditionally over ANY commutative ring R. -/
theorem projector_sq_scaling (v : SphereVector2 R) :
    projector v * projector v = (normSq2 v) • projector v := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> {
    ext
    · simp [projector, normSq2, normSq, Matrix.mul_apply, Fin.sum_univ_two]; ring
    · simp [projector, normSq2, normSq, Matrix.mul_apply, Fin.sum_univ_two]; ring
    · simp [projector, normSq2, normSq, Matrix.mul_apply, Fin.sum_univ_two]; ring
    · simp [projector, normSq2, normSq, Matrix.mul_apply, Fin.sum_univ_two]; ring
  }

/-- Idempotency on the sphere: N_2(v) = 1 implies P(v)^2 = P(v). -/
theorem projector_idempotent (v : SphereVector2 R) (hv : normSq2 v = 1) :
    projector v * projector v = projector v := by
  rw [projector_sq_scaling, hv, one_smul]

/-! ### Section 5: Affine Chart Trivialization and Coordinate Complement -/

/-- Unnormalized affine projector for the standard chart v1 = 1, v2 = z:
    P_raw(z) = !![ 1, conj z ; z, N(z) • 1 ]. -/
def affineProjectorRaw (z : Coquaternion R) : Mat2D R :=
  !![ (1 : Coquaternion R), conj z;
      z, (normSq z) • (1 : Coquaternion R) ]

/-- Standard embedding of the affine coordinate z into D^2: z ↦ ⟨1, z⟩. -/
def toSphereVectorAffine (z : Coquaternion R) : SphereVector2 R :=
  ⟨1, z⟩

/-- Norm of the affine vector ⟨1, z⟩: N_2(⟨1, z⟩) = 1 + N(z). -/
theorem normSq2_affine (z : Coquaternion R) :
    normSq2 (toSphereVectorAffine z) = 1 + normSq z := by
  dsimp [normSq2, toSphereVectorAffine, normSq]
  ring

/-- The projector of the affine vector ⟨1, z⟩ equals the raw affine projector:
    P(⟨1, z⟩) = P_raw(z). -/
theorem projector_affine_chart (z : Coquaternion R) :
    projector (toSphereVectorAffine z) = affineProjectorRaw z := by
  ext i j : 1
  fin_cases i <;> fin_cases j
  · -- (0, 0)
    dsimp [projector, toSphereVectorAffine, affineProjectorRaw]
    rw [conj_one, mul_one_q]
  · -- (0, 1)
    dsimp [projector, toSphereVectorAffine, affineProjectorRaw]
    rw [one_mul_q]
  · -- (1, 0)
    dsimp [projector, toSphereVectorAffine, affineProjectorRaw]
    rw [conj_one, mul_one_q]
  · -- (1, 1)
    dsimp [projector, toSphereVectorAffine, affineProjectorRaw]
    rw [mul_conj]

/-- Universal scaling identity for the raw affine projector:
    P_raw(z)^2 = (1 + N(z)) • P_raw(z). -/
theorem affineProjectorRaw_sq_scaling (z : Coquaternion R) :
    affineProjectorRaw z * affineProjectorRaw z = (1 + normSq z) • affineProjectorRaw z := by
  have h := projector_sq_scaling (toSphereVectorAffine z)
  rw [projector_affine_chart, normSq2_affine] at h
  exact h

/-- Scalar multiplication distributes across 2x2 matrix multiplication:
    (c • M) * (d • N) = (c * d) • (M * N). -/
theorem mat2_smul_mul_smul (c d : R) (M N : Mat2D R) :
    (c • M) * (d • N) = (c * d) • (M * N) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> {
    ext
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  }

/-- Normalized affine projector: P_c(z) = c • P_raw(z) where c(1 + N(z)) = 1. -/
def affineProjector (c : R) (z : Coquaternion R) : Mat2D R :=
  c • affineProjectorRaw z

/-- Idempotency of the normalized affine projector:
    When c(1 + N(z)) = 1, P_c(z)^2 = P_c(z). -/
theorem affine_projector_idempotent (c : R) (z : Coquaternion R)
    (hc : c * (1 + normSq z) = 1) :
    affineProjector c z * affineProjector c z = affineProjector c z := by
  dsimp [affineProjector]
  rw [mat2_smul_mul_smul, affineProjectorRaw_sq_scaling, ← mul_smul]
  have h_scalar : c * c * (1 + normSq z) = c := by
    calc
      c * c * (1 + normSq z) = c * (c * (1 + normSq z)) := by ring
      _ = c * 1 := by rw [hc]
      _ = c := by ring
  rw [h_scalar]

/-- Trace of the normalized affine projector:
    When c(1 + N(z)) = 1, trace2(P_c(z)) = 1. -/
theorem affine_projector_trace2 (c : R) (z : Coquaternion R)
    (hc : c * (1 + normSq z) = 1) :
    trace2 (affineProjector c z) = 1 := by
  dsimp [affineProjector, trace2, affineProjectorRaw]
  ext
  · -- s component
    dsimp
    calc
      c * 1 + c * (normSq z * 1) = c * (1 + normSq z) := by ring
      _ = 1 := hc
  · -- x component
    dsimp; ring
  · -- y component
    dsimp; ring
  · -- z component
    dsimp; ring

/-- Matrix trace of the normalized affine projector:
    When c(1 + N(z)) = 1, Matrix.trace(P_c(z)) = 1. -/
theorem affine_projector_matrix_trace (c : R) (z : Coquaternion R)
    (hc : c * (1 + normSq z) = 1) :
    Matrix.trace (affineProjector c z) = 1 := by
  rw [matrix_trace_eq_trace2, affine_projector_trace2 c z hc]

/-- Conjugate transpose distributes across scalar multiplication on M_2(D). -/
theorem conjTranspose2_smul (c : R) (M : Mat2D R) :
    conjTranspose2 (c • M) = c • conjTranspose2 M := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> {
    dsimp [conjTranspose2]
    rw [conj_smul]
  }

/-- Unconditional Hermitian self-adjointness of the raw affine projector. -/
theorem affineProjectorRaw_hermitian (z : Coquaternion R) :
    conjTranspose2 (affineProjectorRaw z) = affineProjectorRaw z := by
  have h := projector_hermitian (toSphereVectorAffine z)
  rw [projector_affine_chart] at h
  exact h

/-- Hermitian self-adjointness of the normalized affine projector. -/
theorem affine_projector_hermitian (c : R) (z : Coquaternion R) :
    conjTranspose2 (affineProjector c z) = affineProjector c z := by
  dsimp [affineProjector]
  rw [conjTranspose2_smul, affineProjectorRaw_hermitian]

/-! ### Section 6: Master Verification Certificate -/

/-- Master verification certificate for Voelkel's split composition projective spaces,
    Hermitian projectors, and the motivic quadric sphere S^(4,2). -/
structure SplitCompositionProjectiveSpaceCertificate : Prop where
  -- 1. Split Quaternions and Involutive Conjugation
  conj_involutive : ∀ (R : Type) [CommRing R] (q : Coquaternion R),
    conj (conj q) = q
  conj_anti_multiplicative : ∀ (R : Type) [CommRing R] (p q : Coquaternion R),
    conj (p * q) = conj q * conj p
  norm_fundamental_identity : ∀ (R : Type) [CommRing R] (q : Coquaternion R),
    q * conj q = (normSq q) • (1 : Coquaternion R)
  norm_reverse_identity : ∀ (R : Type) [CommRing R] (q : Coquaternion R),
    conj q * q = (normSq q) • (1 : Coquaternion R)

  -- 2. Sign Signature Decompositions & Motivic Quadric Spheres
  signature_22 : ∀ (R : Type) [CommRing R] (q : Coquaternion R),
    normSq q = posNorm4 q - negNorm4 q
  signature_44 : ∀ (R : Type) [CommRing R] (v : SphereVector2 R),
    normSq2 v = posNorm8 v - negNorm8 v
  normSq2_expansion : ∀ (R : Type) [CommRing R] (v : SphereVector2 R),
    normSq2 v = (v.v1.s^2 - v.v1.x^2 + v.v1.y^2 - v.v1.z^2) +
                (v.v2.s^2 - v.v2.x^2 + v.v2.y^2 - v.v2.z^2)

  -- 3. Voelkel's DP^1 Hermitian Projector Model
  projector_scaling : ∀ (R : Type) [CommRing R] (v : SphereVector2 R),
    projector v * projector v = (normSq2 v) • projector v
  projector_idempotency : ∀ (R : Type) [CommRing R] (v : SphereVector2 R),
    normSq2 v = 1 → projector v * projector v = projector v
  projector_unit_trace : ∀ (R : Type) [CommRing R] (v : SphereVector2 R),
    normSq2 v = 1 → Matrix.trace (projector v) = 1
  projector_hermitian_symmetry : ∀ (R : Type) [CommRing R] (v : SphereVector2 R),
    conjTranspose2 (projector v) = projector v

  -- 4. Affine Chart Trivialization and Coordinate Complement
  affine_chart_projector : ∀ (R : Type) [CommRing R] (z : Coquaternion R),
    projector (toSphereVectorAffine z) = affineProjectorRaw z
  affine_scaling : ∀ (R : Type) [CommRing R] (z : Coquaternion R),
    affineProjectorRaw z * affineProjectorRaw z = (1 + normSq z) • affineProjectorRaw z
  affine_idempotency : ∀ (R : Type) [CommRing R] (c : R) (z : Coquaternion R),
    c * (1 + normSq z) = 1 → affineProjector c z * affineProjector c z = affineProjector c z
  affine_unit_trace : ∀ (R : Type) [CommRing R] (c : R) (z : Coquaternion R),
    c * (1 + normSq z) = 1 → Matrix.trace (affineProjector c z) = 1
  affine_hermitian_symmetry : ∀ (R : Type) [CommRing R] (c : R) (z : Coquaternion R),
    conjTranspose2 (affineProjector c z) = affineProjector c z

/-- Universal compilation theorem proving that the certificate holds unconditionally. -/
theorem compile_split_composition_projective_space :
    SplitCompositionProjectiveSpaceCertificate where
  conj_involutive := fun _ _ => conj_conj
  conj_anti_multiplicative := fun _ _ => conj_mul
  norm_fundamental_identity := fun _ _ => mul_conj
  norm_reverse_identity := fun _ _ => conj_mul_self
  signature_22 := fun _ _ => normSq_signature_22
  signature_44 := fun _ _ => normSq2_signature_44
  normSq2_expansion := fun _ _ => normSq2_coordinate_expansion
  projector_scaling := fun _ _ => projector_sq_scaling
  projector_idempotency := fun _ _ => projector_idempotent
  projector_unit_trace := fun _ _ => projector_matrix_trace_unit
  projector_hermitian_symmetry := fun _ _ => projector_hermitian
  affine_chart_projector := fun _ _ => projector_affine_chart
  affine_scaling := fun _ _ => affineProjectorRaw_sq_scaling
  affine_idempotency := fun _ _ => affine_projector_idempotent
  affine_unit_trace := fun _ _ => affine_projector_matrix_trace
  affine_hermitian_symmetry := fun _ _ => affine_projector_hermitian

end InfoGeometry.Projective.SplitComposition
