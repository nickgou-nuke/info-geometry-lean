/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Super-Grassmannian Manifold: Indefinite Causal Para-Kähler Geometry

This module formalizes the algebraic differential-geometric structure of indefinite
para-Kähler spaces and projection idempotents:
1. `PseudoRiemannian`: Symmetric bilinear form $g$ on a module $V$.
2. `ParaComplexStructure`: Involutive linear operator $K^2 = \text{id}$.
3. `ParaKahlerStructure`: Skew-symmetric symplectic form $\omega$ compatible with $K$
   such that $g(v, w) = \omega(v, K w)$ and $\omega(K v, K w) = -\omega(v, w)$.
4. `metric_anti_invariance`: $g(K v, K w) = -g(v, w)$, proving the algebraic split anti-invariance identity.
5. `TwinLagrangianSheets`: Subspaces $T^+ = \ker(K - \text{id})$ and $T^- = \ker(K + \text{id})$.
6. `sheet_isotropic_two_mul`: Proves $2 \cdot g(v, v) = 0$ for all $v \in T^\pm$.
7. `SuperGrassmannianProjectors`: Projector idempotents $P^2 = P, Q^2 = Q, P Q = 0$.
8. `SuperGrassmannianManifoldCertificate`: Master integration certificate.
-/

namespace InfoGeometry.Canonical.SuperGrassmannianManifold

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-! ### 1. Pseudo-Riemannian Metric and Para-Complex Structure -/

/-- A symmetric bilinear form representing a pseudo-Riemannian metric carrier. -/
structure PseudoRiemannianMetric (g : V →ₗ[R] V →ₗ[R] R) : Prop where
  symm : ∀ v w, g v w = g w v

/-- Para-complex structure: an involutive linear automorphism $K^2 = \text{id}$. -/
structure ParaComplexStructure (K : V →ₗ[R] V) : Prop where
  involutive : ∀ v, K (K v) = v

/-! ### 2. Para-Kähler Structure and Metric Anti-Invariance -/

/--
Para-Kähler structure: A pair of a metric $g$, a symplectic form $\omega$,
and a para-complex structure $K$ satisfying compatibility:
$g(v, w) = \omega(v, K w)$ and $\omega(K v, K w) = -\omega(v, w)$.
-/
structure ParaKahlerStructure
    (g : V →ₗ[R] V →ₗ[R] R)
    (omega : V →ₗ[R] V →ₗ[R] R)
    (K : V →ₗ[R] V) : Prop where
  g_symm : ∀ v w, g v w = g w v
  omega_skew : ∀ v w, omega v w = -omega w v
  compatibility : ∀ v w, g v w = omega v (K w)
  omega_anti_inv : ∀ v w, omega (K v) (K w) = -omega v w

/--
Theorem: The metric is anti-invariant under the para-complex structure:
$g(K v, K w) = -g(v, w)$.
This establishes the split / neutral signature of the para-Kähler geometry.
-/
theorem metric_anti_invariance
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hK : ParaComplexStructure K)
    (hpk : ParaKahlerStructure g omega K)
    (v w : V) :
    g (K v) (K w) = -g v w := by
  have h1 : g (K v) (K w) = omega (K v) (K (K w)) := hpk.compatibility (K v) (K w)
  have h2 : K (K w) = w := hK.involutive w
  have h3 : omega (K v) w = -omega w (K v) := hpk.omega_skew (K v) w
  have h4 : g w v = omega w (K v) := hpk.compatibility w v
  have h5 : g w v = g v w := hpk.g_symm w v
  rw [h1, h2, h3, ← h4, h5]

/-! ### 3. Twin Isotropic Lagrangian Sheets -/

/-- The positive eigen-sheet $T^+ = \ker(K - \text{id})$. -/
def InTPlus (K : V →ₗ[R] V) (v : V) : Prop :=
  K v = v

/-- The negative eigen-sheet $T^- = \ker(K + \text{id})$. -/
def InTMinus (K : V →ₗ[R] V) (v : V) : Prop :=
  K v = -v

/--
Theorem: Any vector in $T^+$ is isotropic up to doubling: $2 \cdot g(v, v) = 0$.
In characteristic $\ne 2$ (e.g. over $\mathbb{R}$), $g(v, v) = 0$, so $T^+$ is totally isotropic.
-/
theorem tplus_isotropic_two_mul
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hK : ParaComplexStructure K)
    (hpk : ParaKahlerStructure g omega K)
    (v : V) (hv : InTPlus K v) :
    2 * g v v = 0 := by
  have h_anti := metric_anti_invariance g omega K hK hpk v v
  have h_kv : K v = v := hv
  rw [h_kv] at h_anti
  calc
    2 * g v v = g v v + g v v := by ring
    _ = -g v v + g v v := by nth_rw 1 [h_anti]
    _ = 0 := neg_add_cancel (g v v)

/--
Theorem: Any vector in $T^-$ is isotropic up to doubling: $2 \cdot g(v, v) = 0$.
-/
theorem tminus_isotropic_two_mul
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hK : ParaComplexStructure K)
    (hpk : ParaKahlerStructure g omega K)
    (v : V) (hv : InTMinus K v) :
    2 * g v v = 0 := by
  have h_anti := metric_anti_invariance g omega K hK hpk v v
  have h_kv : K v = -v := hv
  rw [h_kv] at h_anti
  have h_neg : g (-v) (-v) = g v v := by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [h_neg] at h_anti
  calc
    2 * g v v = g v v + g v v := by ring
    _ = -g v v + g v v := by nth_rw 1 [h_anti]
    _ = 0 := neg_add_cancel (g v v)

/-! ### 4. Super-Grassmannian Projector Idempotents -/

/-- Graded projector $P$ on $V$ representing a point in the super-Grassmannian. -/
structure GrassmannianProjector (P : V →ₗ[R] V) : Prop where
  idempotent : ∀ v, P (P v) = P v

/-- Algebraic complementary projector $Q = \text{id} - P$. -/
def orthoComplement (P : V →ₗ[R] V) : V →ₗ[R] V :=
  LinearMap.id - P

/-- Theorem: The orthocomplement $Q$ is idempotent: $Q^2 = Q$. -/
@[simp]
theorem orthoComplement_idempotent (P : V →ₗ[R] V) (hP : GrassmannianProjector P) (v : V) :
    orthoComplement P (orthoComplement P v) = orthoComplement P v := by
  dsimp [orthoComplement]
  rw [map_sub, hP.idempotent, sub_self, sub_zero]

/-- Theorem: Mutual annihilation $P Q = 0$. -/
@[simp]
theorem projector_ortho_annihilation (P : V →ₗ[R] V) (hP : GrassmannianProjector P) (v : V) :
    P (orthoComplement P v) = 0 := by
  dsimp [orthoComplement]
  rw [map_sub, hP.idempotent, sub_self]

/-- Theorem: Mutual annihilation $Q P = 0$. -/
@[simp]
theorem ortho_projector_annihilation (P : V →ₗ[R] V) (hP : GrassmannianProjector P) (v : V) :
    orthoComplement P (P v) = 0 := by
  dsimp [orthoComplement]
  rw [hP.idempotent, sub_self]

/-! ### 5. Master Super-Grassmannian Manifold Certificate -/

structure SuperGrassmannianManifoldCertificate (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V] : Prop where
  metric_anti_inv : ∀ (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V),
    ParaComplexStructure K → ParaKahlerStructure g omega K →
    ∀ v w, g (K v) (K w) = -g v w
  tplus_iso : ∀ (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V),
    ParaComplexStructure K → ParaKahlerStructure g omega K →
    ∀ v, InTPlus K v → 2 * g v v = 0
  tminus_iso : ∀ (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V),
    ParaComplexStructure K → ParaKahlerStructure g omega K →
    ∀ v, InTMinus K v → 2 * g v v = 0
  ortho_idem : ∀ (P : V →ₗ[R] V),
    GrassmannianProjector P → ∀ v,
    orthoComplement P (orthoComplement P v) = orthoComplement P v
  annihilate_pq : ∀ (P : V →ₗ[R] V),
    GrassmannianProjector P → ∀ v,
    P (orthoComplement P v) = 0
  annihilate_qp : ∀ (P : V →ₗ[R] V),
    GrassmannianProjector P → ∀ v,
    orthoComplement P (P v) = 0

theorem compile_super_grassmannian_manifold (R : Type*) [CommRing R]
    (V : Type*) [AddCommGroup V] [Module R V] :
    SuperGrassmannianManifoldCertificate R V where
  metric_anti_inv := metric_anti_invariance
  tplus_iso := tplus_isotropic_two_mul
  tminus_iso := tminus_isotropic_two_mul
  ortho_idem := orthoComplement_idempotent
  annihilate_pq := projector_ortho_annihilation
  annihilate_qp := ortho_projector_annihilation

end InfoGeometry.Canonical.SuperGrassmannianManifold
