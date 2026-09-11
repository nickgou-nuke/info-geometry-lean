import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Krein BRST Ghost Confinement & Physical Decoupling

This module formalizes:
1. **The Krein Space Structure $(V, J)$**:
   An indefinite inner product space equipped with a fundamental symmetry $J$
   satisfying $J^2 = \mathbb{I}$ and $J^\dagger = J$.
2. **The Indefinite Krein Pairing and Charge**:
   $[x, y]_J = \langle J x, y \rangle$ and $[v, v]_J = \langle J v, v \rangle$.
3. **The Nilpotent BRST Supercharge $Q$**:
   $Q : V \toₗ[ℝ] V$ satisfying strict nilpotency $Q^2 = 0$.
4. **Physical and Ghost Classification**:
   - Physical (closed) states: $Q \psi = 0$ ($\psi \in \ker Q$).
   - Exact (gauge-trivial ghost) states: $v = Q w$ ($v \in \mathrm{range} Q$).
   - Inclusion $\mathrm{range} Q \subseteq \ker Q$ (exact states are closed).
5. **Krein-BRST Compatibility**:
   Formulated for both skew-adjoint ($\langle J(Qx), y \rangle = - \langle Jx, Qy \rangle$)
   and self-adjoint ($\langle J(Qx), y \rangle = \langle Jx, Qy \rangle$) gradings.
6. **The Ghost Charge Collapse Theorem**:
   Every BRST-exact state $v = Q w$ has identically vanishing Krein charge $[v, v]_J = 0$.
7. **Physical State Decoupling Orthogonality**:
   Every physical state $\psi \in \ker Q$ is strictly Krein-orthogonal to every exact ghost state $v \in \mathrm{range} Q$:
   $[v, \psi]_J = 0$.
-/

open RealInnerProductSpace

namespace InfoGeometry.Physics.KreinBRSTGhostConfinement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Architecture carrier for Krein fundamental symmetry $J$ ($J^2 = \mathbb{I}, J^\dagger = J$). -/
structure KreinSpace (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  J : V →ₗ[ℝ] V
  J_sq : J.comp J = LinearMap.id
  J_self_adjoint : ∀ x y : V, inner (𝕜 := ℝ) (J x) y = inner (𝕜 := ℝ) x (J y)

variable (K : KreinSpace V)

/-- Krein indefinite inner product: $[x, y]_J = \langle J x, y \rangle$. -/
def kreinInner (x y : V) : ℝ := inner (𝕜 := ℝ) (K.J x) y

/-- Krein charge (indefinite norm): $[v, v]_J = \langle J v, v \rangle$. -/
def kreinCharge (v : V) : ℝ := kreinInner K v v

/-- Definition of a nilpotent BRST supercharge $Q$: $Q^2 = 0$. -/
structure BRSTCharge (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  Q : V →ₗ[ℝ] V
  Q_nilpotent : Q.comp Q = 0

variable (B : BRSTCharge V)

/-- BRST-closed state (physical state condition): $Q v = 0$. -/
def IsBRSTClosed (v : V) : Prop := B.Q v = 0

/-- BRST-exact state (gauge-trivial ghost state): $v = Q w$. -/
def IsBRSTExact (v : V) : Prop := ∃ w : V, B.Q w = v

/-- Krein-BRST skew-compatibility: $\langle J(Q x), y \rangle = - \langle J x, Q y \rangle$. -/
def IsKreinBRSTSkew (K : KreinSpace V) (B : BRSTCharge V) : Prop :=
  ∀ x y : V, inner (𝕜 := ℝ) (K.J (B.Q x)) y = - inner (𝕜 := ℝ) (K.J x) (B.Q y)

/-- Krein-BRST self-adjoint compatibility: $\langle J(Q x), y \rangle = \langle J x, Q y \rangle$. -/
def IsKreinBRSTSelfAdjoint (K : KreinSpace V) (B : BRSTCharge V) : Prop :=
  ∀ x y : V, inner (𝕜 := ℝ) (K.J (B.Q x)) y = inner (𝕜 := ℝ) (K.J x) (B.Q y)

/-- 🏆 THEOREM: BRST squared annihilation $Q(Q v) = 0$. -/
theorem brst_squared_annihilation (v : V) : B.Q (B.Q v) = 0 := by
  have h := LinearMap.congr_fun B.Q_nilpotent v
  exact h

/-- 🏆 THEOREM: Every BRST exact state is BRST closed: $\mathrm{range}(Q) \subseteq \ker(Q)$. -/
theorem brst_exact_is_closed (v : V) (h : IsBRSTExact B v) : IsBRSTClosed B v := by
  dsimp [IsBRSTClosed]
  rcases h with ⟨w, rfl⟩
  exact brst_squared_annihilation B w

/-- 🏆 THEOREM: Ghost charge collapse under skew compatibility:
    For any BRST-exact state $v = Q w$, $[v, v]_J = 0$. -/
theorem brst_ghost_charge_collapse_skew
    (h_skew : IsKreinBRSTSkew K B) (v : V) (h_exact : IsBRSTExact B v) :
    kreinCharge K v = 0 := by
  dsimp [kreinCharge, kreinInner]
  rcases h_exact with ⟨w, rfl⟩
  rw [h_skew w (B.Q w)]
  have h_nil := brst_squared_annihilation B w
  rw [h_nil, inner_zero_right, neg_zero]

/-- 🏆 THEOREM: Ghost charge collapse under self-adjoint compatibility:
    For any BRST-exact state $v = Q w$, $[v, v]_J = 0$. -/
theorem brst_ghost_charge_collapse_self_adjoint
    (h_adj : IsKreinBRSTSelfAdjoint K B) (v : V) (h_exact : IsBRSTExact B v) :
    kreinCharge K v = 0 := by
  dsimp [kreinCharge, kreinInner]
  rcases h_exact with ⟨w, rfl⟩
  rw [h_adj w (B.Q w)]
  have h_nil := brst_squared_annihilation B w
  rw [h_nil, inner_zero_right]

/-- 🏆 THEOREM: Physical state decoupling (skew):
    Any physical state $\psi$ ($Q \psi = 0$) is Krein-orthogonal to every exact ghost state $v = Q w$. -/
theorem brst_physical_ghost_decoupling_skew
    (h_skew : IsKreinBRSTSkew K B) (psi : V) (h_phys : IsBRSTClosed B psi)
    (v : V) (h_exact : IsBRSTExact B v) :
    kreinInner K v psi = 0 := by
  dsimp [kreinInner]
  rcases h_exact with ⟨w, rfl⟩
  rw [h_skew w psi]
  dsimp [IsBRSTClosed] at h_phys
  rw [h_phys, inner_zero_right, neg_zero]

/-- 🏆 THEOREM: Physical state decoupling (self-adjoint):
    Any physical state $\psi$ ($Q \psi = 0$) is Krein-orthogonal to every exact ghost state $v = Q w$. -/
theorem brst_physical_ghost_decoupling_self_adjoint
    (h_adj : IsKreinBRSTSelfAdjoint K B) (psi : V) (h_phys : IsBRSTClosed B psi)
    (v : V) (h_exact : IsBRSTExact B v) :
    kreinInner K v psi = 0 := by
  dsimp [kreinInner]
  rcases h_exact with ⟨w, rfl⟩
  rw [h_adj w psi]
  dsimp [IsBRSTClosed] at h_phys
  rw [h_phys, inner_zero_right]

/-- 🏆 MASTER SYNTHESIS: Krein BRST Ghost Confinement & Physical Decoupling. -/
theorem certified_krein_brst_ghost_confinement_synthesis
    (h_skew : IsKreinBRSTSkew K B) (psi : V) (h_phys : IsBRSTClosed B psi)
    (v : V) (h_exact : IsBRSTExact B v) :
    (B.Q (B.Q v) = 0) ∧
    (IsBRSTClosed B v) ∧
    (kreinCharge K v = 0) ∧
    (kreinInner K v psi = 0) :=
  ⟨brst_squared_annihilation B v,
   brst_exact_is_closed B v h_exact,
   brst_ghost_charge_collapse_skew K B h_skew v h_exact,
   brst_physical_ghost_decoupling_skew K B h_skew psi h_phys v h_exact⟩

end InfoGeometry.Physics.KreinBRSTGhostConfinement
