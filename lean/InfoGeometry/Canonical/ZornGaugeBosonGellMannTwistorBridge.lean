import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

import InfoGeometry.Canonical.GaugedZornDiracKahlerConnection

/-!
# Stratum 26: Unified Gauge Boson Generation, Gell-Mann Color Octet, & Twistor Incidence Bridge

This module formalizes the dynamic generation of gauge bosons and twistor incidence relations
from the non-associative Zorn vector matrix algebra:

1. **Quark-Antiquark Outer Product and $3 \otimes \bar{3} = 1 \oplus 8$ Decomposition**:
   - The outer product matrix $M(\mathbf{u}, \mathbf{v})_{ij} = u_i v_j$ of a quark triplet $\mathbf{u}$
     and antiquark triplet $\mathbf{v}$ has trace $\mathrm{tr}(M) = \mathbf{u} \cdot \mathbf{v}$ (color singlet).
   - The traceless color octet tensor $T(\mathbf{u}, \mathbf{v}) = 3 M(\mathbf{u}, \mathbf{v}) - (\mathbf{u} \cdot \mathbf{v}) I_3$
     is identically traceless over any commutative ring $R$: $\mathrm{tr}(T) = 0$.

2. **Gluon Field Strength Tensor $\hat{G}_{\mu\nu}$ from Quark Commutator**:
   - Spacetime 1-form quark matter fields generate the skew-symmetric tensor
     $F_{\mu\nu} = M(\mathbf{u}_\mu, \mathbf{v}_\nu) - M(\mathbf{u}_\nu, \mathbf{v}_\mu)$.
   - The traceless octet gluon curvature $\hat{G}_{\mu\nu} = T(\mathbf{u}_\mu, \mathbf{v}_\nu) - T(\mathbf{u}_\nu, \mathbf{v}_\mu)$
     satisfies:
     - $\mathrm{tr}(\hat{G}_{\mu\nu}) = 0$ (exact color $SU(3)$ curvature).
     - $\hat{G}_{\nu\mu} = - \hat{G}_{\mu\nu}$ (skew-symmetry).
     - $\hat{G}_{\mu\mu} = 0$ (self-annihilation).

3. **Gell-Mann Matrices Representation**:
   - Explicit definitions of the eight Gell-Mann matrices $\lambda_1, \dots, \lambda_8$ over any ring $R$.
   - Universal proof of tracelessness $\mathrm{tr}(\lambda_a) = 0$ for all $a \in \{1, \dots, 8\}$.

4. **Internal Zorn Commutator Generating the Krein Grading $J = P_+ - P_-$**:
   - The commutator between a quark operator $Q(\mathbf{u})$ and an antiquark operator $\bar{Q}(\mathbf{v})$
     evaluates identically to $[Q(\mathbf{u}), \bar{Q}(\mathbf{v})] = (\mathbf{u} \cdot \mathbf{v}) J$ on the diagonal,
     directly recovering the split hyperbolic unit / Krein grading $J = P_+ - P_- = \mathrm{diag}(1, -1)$.

5. **Split Peirce Parity / Charge-Conjugation Holonomy**:
   - The parity involution $T(a, b, \mathbf{u}, \mathbf{v}) = (b, a, \mathbf{v}, \mathbf{u})$ swaps $P_+ \leftrightarrow P_-$,
     inverts $J \mapsto -J$, and transposes quarks into antiquarks $Q(\mathbf{u}) \mapsto \bar{Q}(\mathbf{u})$.

6. **On-Shell Lightcone Constraint & Penrose Twistor Chiral Dyad Factorization**:
   - On-shell lightcone constraint $N(X) = 0 \iff a b = \mathbf{u} \cdot \mathbf{v}$.
   - Chiral dyad spinor factorization $\det(\pi \lambda^T) = 0$.
   - Operator incidence relation: $\omega = X \pi$ scaling linearly along the twistor line.
-/

namespace InfoGeometry.Canonical.ZornGaugeBosonGellMannTwistor

open InfoGeometry.Canonical.GaugedZornDiracKahler

variable {R : Type*} [CommRing R]

/-!
### Stratum 26.1: Quark-Antiquark Outer Product and 3 ⊗ 3̄ = 1 ⊕ 8 Decomposition
-/

/-- The 3x3 outer product matrix M(u, v)_ij = u_i * v_j of a quark triplet u and antiquark triplet v. -/
def outerProduct (u v : Vec3 R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => u i * v j

/-- The trace of the outer product matrix equals the dot product u · v (the color singlet). -/
theorem outerProduct_trace (u v : Vec3 R) :
    Matrix.trace (outerProduct u v) = dot3 u v := by
  dsimp [Matrix.trace]
  rw [Fin.sum_univ_three]
  dsimp [outerProduct, dot3]

/--
The traceless color octet tensor:
T(u, v) = 3 * M(u, v) - (u · v) * I₃.
Over any commutative ring R, this tensor is identically traceless without requiring 1/3.
-/
def tracelessOctet (u v : Vec3 R) : Matrix (Fin 3) (Fin 3) R :=
  fun i j => (3 : R) * (outerProduct u v i j) - (dot3 u v) * (if i = j then 1 else 0)

/-- The trace of the octet tensor is identically zero over any commutative ring. -/
theorem tracelessOctet_trace (u v : Vec3 R) :
    Matrix.trace (tracelessOctet u v) = 0 := by
  dsimp [Matrix.trace]
  rw [Fin.sum_univ_three]
  dsimp [tracelessOctet, outerProduct, dot3]
  ring

/-!
### Stratum 26.2: Gluon Field Strength Tensor G_μν from Quark Commutator
-/

/-- The skew-symmetric outer product difference F_μν = M(u_μ, v_ν) - M(u_ν, v_μ). -/
def gluonTensor (u v : Fin 4 → Vec3 R) (μ ν : Fin 4) : Matrix (Fin 3) (Fin 3) R :=
  outerProduct (u μ) (v ν) - outerProduct (u ν) (v μ)

/-- The gluon tensor is skew-symmetric under exchange of spacetime indices. -/
theorem gluonTensor_skew (u v : Fin 4 → Vec3 R) (μ ν : Fin 4) :
    gluonTensor u v ν μ = - gluonTensor u v μ ν := by
  ext i j
  dsimp [gluonTensor, outerProduct]
  ring

/-- The diagonal gluon tensor vanishes identically. -/
theorem gluonTensor_self (u v : Fin 4 → Vec3 R) (μ : Fin 4) :
    gluonTensor u v μ μ = 0 := by
  ext i j
  dsimp [gluonTensor, outerProduct]
  ring

/-- The traceless octet gluon curvature Ĝ_μν = T(u_μ, v_ν) - T(u_ν, v_μ). -/
def octetGluonCurvature (u v : Fin 4 → Vec3 R) (μ ν : Fin 4) : Matrix (Fin 3) (Fin 3) R :=
  tracelessOctet (u μ) (v ν) - tracelessOctet (u ν) (v μ)

/-- The octet gluon curvature is strictly traceless over any ring. -/
theorem octetGluonCurvature_trace (u v : Fin 4 → Vec3 R) (μ ν : Fin 4) :
    Matrix.trace (octetGluonCurvature u v μ ν) = 0 := by
  dsimp [octetGluonCurvature]
  rw [Matrix.trace_sub, tracelessOctet_trace, tracelessOctet_trace, sub_zero]

/-- The octet gluon curvature is skew-symmetric under spacetime index swap. -/
theorem octetGluonCurvature_skew (u v : Fin 4 → Vec3 R) (μ ν : Fin 4) :
    octetGluonCurvature u v ν μ = - octetGluonCurvature u v μ ν := by
  ext i j
  dsimp [octetGluonCurvature, tracelessOctet, outerProduct]
  ring

/-!
### Stratum 26.3: The 8 Gell-Mann Matrices and Tracelessness
-/

def gm1 : Matrix (Fin 3) (Fin 3) R :=
  ![![0, 1, 0],
    ![1, 0, 0],
    ![0, 0, 0]]

def gm2 : Matrix (Fin 3) (Fin 3) R :=
  ![![0, -1, 0],
    ![1, 0, 0],
    ![0, 0, 0]]

def gm3 : Matrix (Fin 3) (Fin 3) R :=
  ![![1, 0, 0],
    ![0, -1, 0],
    ![0, 0, 0]]

def gm4 : Matrix (Fin 3) (Fin 3) R :=
  ![![0, 0, 1],
    ![0, 0, 0],
    ![1, 0, 0]]

def gm5 : Matrix (Fin 3) (Fin 3) R :=
  ![![0, 0, -1],
    ![0, 0, 0],
    ![1, 0, 0]]

def gm6 : Matrix (Fin 3) (Fin 3) R :=
  ![![0, 0, 0],
    ![0, 0, 1],
    ![0, 1, 0]]

def gm7 : Matrix (Fin 3) (Fin 3) R :=
  ![![0, 0, 0],
    ![0, 0, -1],
    ![0, 1, 0]]

def gm8 : Matrix (Fin 3) (Fin 3) R :=
  ![![1, 0, 0],
    ![0, 1, 0],
    ![0, 0, -2]]

theorem gm1_trace : Matrix.trace (gm1 (R := R)) = 0 := by
  rw [Matrix.trace_fin_three]; simp [gm1]

theorem gm2_trace : Matrix.trace (gm2 (R := R)) = 0 := by
  rw [Matrix.trace_fin_three]; simp [gm2]

theorem gm3_trace : Matrix.trace (gm3 (R := R)) = 0 := by
  rw [Matrix.trace_fin_three]; simp [gm3]

theorem gm4_trace : Matrix.trace (gm4 (R := R)) = 0 := by
  rw [Matrix.trace_fin_three]; simp [gm4]

theorem gm5_trace : Matrix.trace (gm5 (R := R)) = 0 := by
  rw [Matrix.trace_fin_three]; simp [gm5]

theorem gm6_trace : Matrix.trace (gm6 (R := R)) = 0 := by
  rw [Matrix.trace_fin_three]; simp [gm6]

theorem gm7_trace : Matrix.trace (gm7 (R := R)) = 0 := by
  rw [Matrix.trace_fin_three]; simp [gm7]

theorem gm8_trace : Matrix.trace (gm8 (R := R)) = 0 := by
  rw [Matrix.trace_fin_three]; simp [gm8]; ring

/-!
### Stratum 26.4: Zorn Commutator Generating the Krein Grading J = P₊ - P₋
-/

/-- The Krein grading / split hyperbolic unit J = P₊ - P₋ = diag(1, -1). -/
def zornJ : ZornMatrix R :=
  ZornMatrix.sub ZornMatrix.PPlus ZornMatrix.PMinus

/--
The Zorn commutator [Q(u), Q̄(v)] = Q(u) Q̄(v) - Q̄(v) Q(u)
evaluates exactly to (u · v) • J on the diagonal.
-/
theorem zorn_quark_antiquark_commutator (u v : Vec3 R) :
    ZornMatrix.sub
      (ZornMatrix.zornMul (ZornMatrix.quark u) (ZornMatrix.antiquark v))
      (ZornMatrix.zornMul (ZornMatrix.antiquark v) (ZornMatrix.quark u)) =
    ZornMatrix.smul (dot3 u v) (zornJ (R := R)) := by
  apply ZornMatrix.ext
  · dsimp [ZornMatrix.sub, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.antiquark,
           ZornMatrix.smul, zornJ, ZornMatrix.PPlus, ZornMatrix.PMinus, dot3]; ring
  · dsimp [ZornMatrix.sub, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.antiquark,
           ZornMatrix.smul, zornJ, ZornMatrix.PPlus, ZornMatrix.PMinus, dot3]; ring
  · dsimp [ZornMatrix.sub, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.antiquark,
           ZornMatrix.smul, zornJ, ZornMatrix.PPlus, ZornMatrix.PMinus, cross3]
    ext i; fin_cases i <;> { dsimp; ring }
  · dsimp [ZornMatrix.sub, ZornMatrix.zornMul, ZornMatrix.quark, ZornMatrix.antiquark,
           ZornMatrix.smul, zornJ, ZornMatrix.PPlus, ZornMatrix.PMinus, cross3]
    ext i; fin_cases i <;> { dsimp; ring }

/-!
### Stratum 26.5: Split Peirce Charge-Conjugation / Parity Involution
-/

/-- The charge conjugation / parity swap operator on Zorn matrices: a ↔ b, u ↔ v. -/
def zornParity {S : Type*} (X : ZornMatrix S) : ZornMatrix S :=
  ⟨X.b, X.a, X.v, X.u⟩

theorem zornParity_involutive {S : Type*} (X : ZornMatrix S) :
    zornParity (zornParity X) = X := by
  cases X; rfl

theorem zornParity_swap_peirce_plus :
    zornParity (ZornMatrix.PPlus (R := R)) = ZornMatrix.PMinus := by
  apply ZornMatrix.ext <;> rfl

theorem zornParity_swap_peirce_minus :
    zornParity (ZornMatrix.PMinus (R := R)) = ZornMatrix.PPlus := by
  apply ZornMatrix.ext <;> rfl

theorem zornParity_neg_j :
    zornParity (zornJ (R := R)) = ZornMatrix.smul (-1) zornJ := by
  apply ZornMatrix.ext
  · dsimp [zornParity, zornJ, ZornMatrix.sub, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.smul]; ring
  · dsimp [zornParity, zornJ, ZornMatrix.sub, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.smul]; ring
  · ext i; fin_cases i <;> { dsimp [zornParity, zornJ, ZornMatrix.sub, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.smul]; ring }
  · ext i; fin_cases i <;> { dsimp [zornParity, zornJ, ZornMatrix.sub, ZornMatrix.PPlus, ZornMatrix.PMinus, ZornMatrix.smul]; ring }

theorem zornParity_quark_to_antiquark (u : Vec3 R) :
    zornParity (ZornMatrix.quark u) = ZornMatrix.antiquark u := by
  apply ZornMatrix.ext <;> rfl

/-!
### Stratum 26.6: Lightcone Constraint and Twistor Chiral Dyad Factorization
-/

/--
The on-shell lightcone condition on a Zorn matrix: N(X) = 0,
meaning a * b = dot3 u v.
-/
def IsOnShellLightcone (X : ZornMatrix R) : Prop :=
  ZornMatrix.norm X = 0

theorem onShell_iff_ab_eq_dot (X : ZornMatrix R) :
    IsOnShellLightcone X ↔ X.a * X.b = dot3 X.u X.v := by
  dsimp [IsOnShellLightcone, ZornMatrix.norm]
  exact sub_eq_zero

/--
A 2x2 spinor matrix X formed as a dyad X = π lamᵀ has vanishing determinant:
det(π lamᵀ) = 0.
-/
def spinorDyad (π lam : Fin 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  fun i j => π i * lam j

theorem spinorDyad_det_zero (π lam : Fin 2 → R) :
    Matrix.det (spinorDyad π lam) = 0 := by
  rw [Matrix.det_fin_two]
  dsimp [spinorDyad]
  ring

/--
The twistor incidence equation: ω = X π for an on-shell dyad X = (c • lam) lamᵀ.
-/
theorem twistor_incidence_scaling (lam π : Fin 2 → R) (c : R) :
    (spinorDyad (fun i => c * lam i) lam).mulVec π =
    fun i => (c * (lam 0 * π 0 + lam 1 * π 1)) * lam i := by
  ext i
  change (∑ j : Fin 2, (spinorDyad (fun i => c * lam i) lam i j) * π j) = _
  rw [Fin.sum_univ_two]
  dsimp [spinorDyad]
  ring

/-!
### Stratum 26.7: Master Synthesis Packet for Stratum 26
-/

structure ZornGaugeBosonGellMannTwistorPacket (R : Type*) [CommRing R] where
  outer_trace : ∀ u v : Vec3 R, Matrix.trace (outerProduct u v) = dot3 u v
  octet_traceless : ∀ u v : Vec3 R, Matrix.trace (tracelessOctet u v) = 0
  gluon_skew : ∀ (u v : Fin 4 → Vec3 R) (μ ν : Fin 4),
    gluonTensor u v ν μ = - gluonTensor u v μ ν
  octet_gluon_traceless : ∀ (u v : Fin 4 → Vec3 R) (μ ν : Fin 4),
    Matrix.trace (octetGluonCurvature u v μ ν) = 0
  zorn_commutator_j : ∀ u v : Vec3 R,
    ZornMatrix.sub
      (ZornMatrix.zornMul (ZornMatrix.quark u) (ZornMatrix.antiquark v))
      (ZornMatrix.zornMul (ZornMatrix.antiquark v) (ZornMatrix.quark u)) =
    ZornMatrix.smul (dot3 u v) zornJ
  parity_involutive : ∀ {S : Type*} (X : ZornMatrix S), zornParity (zornParity X) = X
  parity_swap_peirce :
    zornParity (ZornMatrix.PPlus (R := R)) = ZornMatrix.PMinus ∧
    zornParity (ZornMatrix.PMinus (R := R)) = ZornMatrix.PPlus
  parity_neg_j : zornParity (zornJ (R := R)) = ZornMatrix.smul (-1) zornJ
  dyad_det_zero : ∀ π lam : Fin 2 → R, Matrix.det (spinorDyad π lam) = 0
  twistor_incidence : ∀ (lam π : Fin 2 → R) (c : R),
    (spinorDyad (fun i => c * lam i) lam).mulVec π =
    fun i => (c * (lam 0 * π 0 + lam 1 * π 1)) * lam i

def makeZornGaugeBosonGellMannTwistorPacket (R : Type*) [CommRing R] :
    ZornGaugeBosonGellMannTwistorPacket R where
  outer_trace := outerProduct_trace
  octet_traceless := tracelessOctet_trace
  gluon_skew := gluonTensor_skew
  octet_gluon_traceless := octetGluonCurvature_trace
  zorn_commutator_j := zorn_quark_antiquark_commutator
  parity_involutive := zornParity_involutive
  parity_swap_peirce := ⟨zornParity_swap_peirce_plus, zornParity_swap_peirce_minus⟩
  parity_neg_j := zornParity_neg_j
  dyad_det_zero := spinorDyad_det_zero
  twistor_incidence := twistor_incidence_scaling

end InfoGeometry.Canonical.ZornGaugeBosonGellMannTwistor
