/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Algebraic Para-Kähler Bilinear Carriers and Complementary Projectors

This base module defines **ungraded algebraic linear and bilinear carrier structures
on an $R$-module $V$** (without assuming nondegeneracy, manifold charts, a
$\mathbb{Z}_2$ super-grading, metric orthogonality, or differential-form
closedness $d\omega = 0$; nondegenerate half-dimension and bilinear
$\omega$-Lagrangian sheets are proved in `ParaKahlerLagrangianDimension.lean`
and `ParaKahlerSymplecticLagrangian.lean`):
1. `PseudoRiemannianMetric`: Symmetric bilinear form $g$ on a module $V$ (no
   nondegeneracy assumed in this base carrier).
2. `ParaComplexStructure`: Involutive linear endomorphism $K^2 = \text{id}$ on $V$.
3. `ParaKahlerStructure`: Algebraic compatibility between a symmetric bilinear
   form $g$, a skew-symmetric bilinear form $\omega$, and an endomorphism $K$
   satisfying $g(v, w) = \omega(v, K w)$ and $\omega(K v, K w) = -\omega(v, w)$.
4. `metric_anti_invariance`: $g(K v, K w) = -g(v, w)$, proving the algebraic
   anti-invariance of $g$ under $K$.
5. `InTPlus` & `InTMinus`: $+1$ and $-1$ eigenspace predicates
   $T^+ = \{v \mid K v = v\}$ and $T^- = \{v \mid K v = -v\}$.
6. Diagonal and bilinear $2$-torsion isotropy identities (`tplus_isotropic_two_mul`,
   `tminus_isotropic_two_mul`, `omega_tplus_isotropic_two_mul`,
   `omega_tminus_isotropic_two_mul`, `tplus_bilinear_isotropic_two_mul`,
   `tminus_bilinear_isotropic_two_mul`, `omega_tplus_bilinear_isotropic_two_mul`,
   `omega_tminus_bilinear_isotropic_two_mul`): $2 \cdot g(v, w) = 0$ and
   $2 \cdot \omega(v, w) = 0$ on $T^\pm$.
7. `GrassmannianProjector` & `orthoComplement`: Ungraded idempotent linear
   projectors $P^2 = P$ and their algebraic complement $Q = \text{id} - P$
   satisfying $Q^2 = Q$, $P Q = Q P = 0$, and $P + Q = \text{id}$.
-/

namespace InfoGeometry.Canonical.SuperGrassmannianManifold

variable {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-! ### 1. Symmetric Bilinear Carrier and Involutive Endomorphism -/

/-- A symmetric bilinear form on $V$ (algebraic carrier without a nondegeneracy hypothesis). -/
structure PseudoRiemannianMetric (g : V →ₗ[R] V →ₗ[R] R) : Prop where
  symm : ∀ v w, g v w = g w v

/-- Constructive model witness: the zero bilinear form is symmetric. -/
theorem zeroPseudoRiemannianMetric {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] :
    PseudoRiemannianMetric (0 : V →ₗ[R] V →ₗ[R] R) :=
  ⟨fun _ _ => rfl⟩

/-- Algebraic para-complex structure on $V$: an involutive linear endomorphism $K^2 = \text{id}$. -/
structure ParaComplexStructure (K : V →ₗ[R] V) : Prop where
  involutive : ∀ v, K (K v) = v

/-- Constructive model witness: the identity linear map is involutive. -/
theorem idParaComplexStructure {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] :
    ParaComplexStructure (LinearMap.id : V →ₗ[R] V) :=
  ⟨fun _ => rfl⟩

/-! ### 2. Algebraic Para-Kähler Compatibility and Metric Anti-Invariance -/

/--
Algebraic para-Kähler compatibility triple on $V$: a symmetric bilinear form $g$,
a skew-symmetric bilinear form $\omega$, and a linear endomorphism $K$ satisfying
$g(v, w) = \omega(v, K w)$ and $\omega(K v, K w) = -\omega(v, w)$ (without
nondegeneracy or differential-form closedness $d\omega = 0$).
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
Theorem: The symmetric form $g$ is anti-invariant under $K$:
$g(K v, K w) = -g(v, w)$.
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

/-! ### 3. Plus/Minus Eigenspaces and Isotropy Identities -/

/-- Membership in the $+1$ eigenspace $T^+ = \{v \mid K v = v\}$. -/
def InTPlus (K : V →ₗ[R] V) (v : V) : Prop :=
  K v = v

/-- Membership in the $-1$ eigenspace $T^- = \{v \mid K v = -v\}$. -/
def InTMinus (K : V →ₗ[R] V) (v : V) : Prop :=
  K v = -v

/--
Theorem: Any vector in $T^+$ is quadratically $g$-isotropic up to doubling: $2 \cdot g(v, v) = 0$.
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
Theorem: Any vector in $T^-$ is quadratically $g$-isotropic up to doubling: $2 \cdot g(v, v) = 0$.
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
Theorem: Diagonal $\omega$-isotropy up to doubling on $T^+$: $2 \cdot \omega(v, v) = 0$.
(Note: diagonal vanishing $2 \cdot \omega(v, v) = 0$ holds for any skew-symmetric form;
for off-diagonal bilinear $\omega$-isotropy on $T^+ \times T^+$, see
`omega_tplus_bilinear_isotropic_two_mul`.)
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
Theorem: Diagonal $\omega$-isotropy up to doubling on $T^-$: $2 \cdot \omega(v, v) = 0$.
(Note: diagonal vanishing $2 \cdot \omega(v, v) = 0$ holds for any skew-symmetric form;
for off-diagonal bilinear $\omega$-isotropy on $T^- \times T^-$, see
`omega_tminus_bilinear_isotropic_two_mul`.)
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

/--
Theorem: Any pair of vectors in $T^+$ is bilinearly $g$-isotropic up to doubling:
$2 \cdot g(v, w) = 0$.
-/
theorem tplus_bilinear_isotropic_two_mul
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hK : ParaComplexStructure K)
    (hpk : ParaKahlerStructure g omega K)
    (v w : V) (hv : InTPlus K v) (hw : InTPlus K w) :
    2 * g v w = 0 := by
  have h_anti := metric_anti_invariance g omega K hK hpk v w
  have h_kv : K v = v := hv
  have h_kw : K w = w := hw
  rw [h_kv, h_kw] at h_anti
  calc
    2 * g v w = g v w + g v w := two_mul (g v w)
    _ = -g v w + g v w := by nth_rw 1 [h_anti]
    _ = 0 := neg_add_cancel (g v w)

/--
Theorem: Any pair of vectors in $T^-$ is bilinearly $g$-isotropic up to doubling:
$2 \cdot g(v, w) = 0$.
-/
theorem tminus_bilinear_isotropic_two_mul
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hK : ParaComplexStructure K)
    (hpk : ParaKahlerStructure g omega K)
    (v w : V) (hv : InTMinus K v) (hw : InTMinus K w) :
    2 * g v w = 0 := by
  have h_anti := metric_anti_invariance g omega K hK hpk v w
  have h_kv : K v = -v := hv
  have h_kw : K w = -w := hw
  rw [h_kv, h_kw] at h_anti
  have h_neg : g (-v) (-w) = g v w := by
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [h_neg] at h_anti
  calc
    2 * g v w = g v w + g v w := two_mul (g v w)
    _ = -g v w + g v w := by nth_rw 1 [h_anti]
    _ = 0 := neg_add_cancel (g v w)

/--
Theorem: Any pair of vectors in $T^+$ is bilinearly $\omega$-isotropic up to doubling:
$2 \cdot \omega(v, w) = 0$. Unlike the diagonal identity `omega_tplus_isotropic_two_mul`,
this genuine off-diagonal vanishing uses para-Kähler compatibility $g(v, w) = \omega(v, K w)$
together with $K w = w$.
-/
theorem omega_tplus_bilinear_isotropic_two_mul
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hK : ParaComplexStructure K)
    (hpk : ParaKahlerStructure g omega K)
    (v w : V) (hv : InTPlus K v) (hw : InTPlus K w) :
    2 * omega v w = 0 := by
  have h_comp : g v w = omega v (K w) := hpk.compatibility v w
  have h_kw : K w = w := hw
  rw [h_kw] at h_comp
  rw [← h_comp]
  exact tplus_bilinear_isotropic_two_mul g omega K hK hpk v w hv hw

/--
Theorem: Any pair of vectors in $T^-$ is bilinearly $\omega$-isotropic up to doubling:
$2 \cdot \omega(v, w) = 0$. Unlike the diagonal identity `omega_tminus_isotropic_two_mul`,
this genuine off-diagonal vanishing uses para-Kähler compatibility $g(v, w) = \omega(v, K w)$
together with $K w = -w$.
-/
theorem omega_tminus_bilinear_isotropic_two_mul
    (g omega : V →ₗ[R] V →ₗ[R] R) (K : V →ₗ[R] V)
    (hK : ParaComplexStructure K)
    (hpk : ParaKahlerStructure g omega K)
    (v w : V) (hv : InTMinus K v) (hw : InTMinus K w) :
    2 * omega v w = 0 := by
  have h_comp : g v w = omega v (K w) := hpk.compatibility v w
  have h_kw : K w = -w := hw
  rw [h_kw, map_neg] at h_comp
  have h_g : 2 * g v w = 0 :=
    tminus_bilinear_isotropic_two_mul g omega K hK hpk v w hv hw
  rw [h_comp, mul_neg, neg_eq_zero] at h_g
  exact h_g

/-! ### 4. Algebraic Idempotent Projectors and Complementary Split -/

/-- Ungraded idempotent linear projector $P^2 = P$ on $V$. -/
structure GrassmannianProjector (P : V →ₗ[R] V) : Prop where
  idempotent : ∀ v, P (P v) = P v

/-- Constructive model witness: the identity linear map is an idempotent projector. -/
theorem idGrassmannianProjector {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] :
    GrassmannianProjector (LinearMap.id : V →ₗ[R] V) :=
  ⟨fun _ => rfl⟩

/-- Algebraic complementary projector $Q = \text{id} - P$ (defined without reference to a metric). -/
def orthoComplement (P : V →ₗ[R] V) : V →ₗ[R] V :=
  LinearMap.id - P

/-- Theorem: The algebraic complement $Q = \text{id} - P$ is idempotent: $Q^2 = Q$. -/
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
