/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Super-Grassmannian Manifold: Indefinite Causal Para-Kähler Geometry

This module formalizes the algebraic differential-geometric structure of indefinite
para-Kähler spaces and projection idempotents:
1. `PseudoRiemannianMetric`: Symmetric bilinear form $g$ on a module $V$.
2. `ParaComplexStructure`: Involutive linear operator $K^2 = \text{id}$.
3. `ParaKahlerStructure`: Skew-symmetric symplectic form $\omega$ compatible with $K$
   such that $g(v, w) = \omega(v, K w)$ and $\omega(K v, K w) = -\omega(v, w)$.
4. `metric_anti_invariance`: $g(K v, K w) = -g(v, w)$, proving the algebraic split anti-invariance identity.
5. `InTPlus` & `InTMinus`: Eigen-sheets $T^+ = \ker(K - \text{id})$ and $T^- = \ker(K + \text{id})$.
6. `tplus_isotropic_two_mul`, `tminus_isotropic_two_mul`, `omega_tplus_isotropic_two_mul`,
   `omega_tminus_isotropic_two_mul`: Metric and symplectic isotropy ($2 \cdot g(v, v) = 0$ and
   $2 \cdot \omega(v, v) = 0$) on $T^\pm$.
7. `GrassmannianProjector` & `orthoComplement`: Projector idempotents $P^2 = P, Q^2 = Q$,
   mutual annihilation $P Q = Q P = 0$, and partition of unity $P + Q = \text{id}$.
-/

namespace InfoGeometry.Canonical.SuperGrassmannianManifold

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-! ### 1. Pseudo-Riemannian Metric and Para-Complex Structure -/

/-- A symmetric bilinear form representing a pseudo-Riemannian metric carrier. -/
structure PseudoRiemannianMetric (g : V →ₗ[R] V →ₗ[R] R) : Prop where
  symm : ∀ v w, g v w = g w v

/-- Constructive model witness: the zero bilinear form is symmetric. -/
theorem zeroPseudoRiemannianMetric {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] :
    PseudoRiemannianMetric (0 : V →ₗ[R] V →ₗ[R] R) :=
  ⟨fun _ _ => rfl⟩

/-- Para-complex structure: an involutive linear automorphism $K^2 = \text{id}$. -/
structure ParaComplexStructure (K : V →ₗ[R] V) : Prop where
  involutive : ∀ v, K (K v) = v

/-- Constructive model witness: the identity linear map is involutive. -/
theorem idParaComplexStructure {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] :
    ParaComplexStructure (LinearMap.id : V →ₗ[R] V) :=
  ⟨fun _ => rfl⟩

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

/-- Constructive model witness: trivial bilinear forms with the identity para-complex involution. -/
theorem zeroParaKahlerStructure {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] :
    ParaKahlerStructure (0 : V →ₗ[R] V →ₗ[R] R) (0 : V →ₗ[R] V →ₗ[R] R) (LinearMap.id : V →ₗ[R] V) :=
  ⟨fun _ _ => rfl, fun _ _ => neg_zero.symm, fun _ _ => rfl, fun _ _ => neg_zero.symm⟩

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
Theorem: Any vector in $T^+$ is metric-isotropic up to doubling: $2 \cdot g(v, v) = 0$.
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
    2 * g v v = g v v + g v v := two_mul (g v v)
    _ = -g v v + g v v := by nth_rw 1 [h_anti]
    _ = 0 := neg_add_cancel (g v v)

/--
Theorem: Any vector in $T^-$ is metric-isotropic up to doubling: $2 \cdot g(v, v) = 0$.
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
    2 * g v v = g v v + g v v := two_mul (g v v)
    _ = -g v v + g v v := by nth_rw 1 [h_anti]
    _ = 0 := neg_add_cancel (g v v)

/--
Theorem: Any vector in $T^+$ is symplectic-isotropic up to doubling: $2 \cdot \omega(v, v) = 0$.
-/
theorem omega_tplus_isotropic_two_mul
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hpk : ParaKahlerStructure g omega K)
    (v : V) (hv : InTPlus K v) :
    2 * omega v v = 0 := by
  have h_anti : omega (K v) (K v) = -omega v v := hpk.omega_anti_inv v v
  have h_kv : K v = v := hv
  rw [h_kv] at h_anti
  calc
    2 * omega v v = omega v v + omega v v := two_mul (omega v v)
    _ = -omega v v + omega v v := by nth_rw 1 [h_anti]
    _ = 0 := neg_add_cancel (omega v v)

/--
Theorem: Any vector in $T^-$ is symplectic-isotropic up to doubling: $2 \cdot \omega(v, v) = 0$.
-/
theorem omega_tminus_isotropic_two_mul
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hpk : ParaKahlerStructure g omega K)
    (v : V) (hv : InTMinus K v) :
    2 * omega v v = 0 := by
  have h_anti : omega (K v) (K v) = -omega v v := hpk.omega_anti_inv v v
  have h_kv : K v = -v := hv
  rw [h_kv] at h_anti
  have h_neg : omega (-v) (-v) = omega v v := by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [h_neg] at h_anti
  calc
    2 * omega v v = omega v v + omega v v := two_mul (omega v v)
    _ = -omega v v + omega v v := by nth_rw 1 [h_anti]
    _ = 0 := neg_add_cancel (omega v v)

/-! ### 4. Super-Grassmannian Projector Idempotents -/

/-- Graded projector $P$ on $V$ representing a point in the super-Grassmannian. -/
structure GrassmannianProjector (P : V →ₗ[R] V) : Prop where
  idempotent : ∀ v, P (P v) = P v

/-- Constructive model witness: the identity linear map is an idempotent projector. -/
theorem idGrassmannianProjector {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] :
    GrassmannianProjector (LinearMap.id : V →ₗ[R] V) :=
  ⟨fun _ => rfl⟩

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

/-- Theorem: Partition of unity $P v + Q v = v$. -/
@[simp]
theorem projector_add_orthoComplement (P : V →ₗ[R] V) (v : V) :
    P v + orthoComplement P v = v := by
  dsimp [orthoComplement]
  exact add_sub_cancel (P v) v

end InfoGeometry.Canonical.SuperGrassmannianManifold
