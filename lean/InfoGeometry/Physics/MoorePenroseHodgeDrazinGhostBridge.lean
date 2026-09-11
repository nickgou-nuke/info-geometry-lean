import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Moore-Penrose Hodge Diffusion & Drazin-BRST Ghost Filtration

This module formalizes the exact duality between:
1. **The Regular Sector (Moore-Penrose Hodge-Green Resolution)**:
   - Self-adjoint Hodge-Laplacian $\Delta = \Delta^\dagger \ge 0$.
   - Commuting Moore-Penrose pseudo-inverse $G = \Delta^+$ satisfying:
     $$\Delta G \Delta = \Delta, \quad G \Delta G = G, \quad \Delta G = G \Delta$$
   - Harmonic projector $P_{\mathcal{H}} = \mathbb{I} - \Delta G$ and regular projector $P_{\mathrm{reg}} = \Delta G$.
   - Idempotence: $P_{\mathcal{H}}^2 = P_{\mathcal{H}}$ and $P_{\mathrm{reg}}^2 = P_{\mathrm{reg}}$.
   - Exact kernel identification: $\Delta (P_{\mathcal{H}} x) = 0$.
   - Exact inversion on regular image: $\Delta (G (P_{\mathrm{reg}} y)) = P_{\mathrm{reg}} y$.
   - Real heat diffusion energy dissipation: $\langle -\Delta x, x \rangle \le 0$.
2. **The Gauge Sector (Drazin Inversion & BRST-Krein Ghost Filtration)**:
   - Nilpotent BRST supercharge $Q$ ($Q^2 = 0$) and Krein space $(V, J)$ ($J^2 = \mathbb{I}, J^\dagger = J$).
   - Exact states $v = Q w \in \mathrm{range}(Q) \subseteq \ker(Q)$ (Faddeev-Popov ghosts).
   - Krein charge collapse: $[v, v]_J = \langle J v, v \rangle = 0$ for all ghosts $v = Q w$.
   - Physical state decoupling: $[v, \psi]_J = \langle J v, \psi \rangle = 0$ for all physical states $\psi \in \ker(Q)$.
   - Drazin index-1 inversion: Every commuting Moore-Penrose pseudo-inverse is unconditionally a Drazin inverse of index 1.
   - Drazin annihilation of unphysical null modes: $T v = 0 \implies T_D v = 0$, filtering unphysical zeros into trivial ghosts.
-/

open RealInnerProductSpace

noncomputable section

namespace InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## 1. The Regular Sector: Moore-Penrose Hodge-Green Resolution -/

/-- Commuting Moore-Penrose pseudo-inverse for a self-adjoint operator `Δ`. -/
structure MoorePenroseHodge (Δ G : V →ₗ[ℝ] V) : Prop where
  mp1 : Δ.comp (G.comp Δ) = Δ
  mp2 : G.comp (Δ.comp G) = G
  comm : Δ.comp G = G.comp Δ
  self_adjoint_Δ : ∀ x y : V, inner (𝕜 := ℝ) (Δ x) y = inner (𝕜 := ℝ) x (Δ y)
  self_adjoint_G : ∀ x y : V, inner (𝕜 := ℝ) (G x) y = inner (𝕜 := ℝ) x (G y)
  pos_semidef_Δ : ∀ x : V, 0 ≤ inner (𝕜 := ℝ) (Δ x) x

/-- Harmonic projector: $P_{\mathcal{H}} = \mathbb{I} - \Delta \circ G$. -/
def harmonicProjector (Δ G : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  LinearMap.id - Δ.comp G

/-- Regular image projector: $P_{\mathrm{reg}} = \Delta \circ G$. -/
def regularProjector (Δ G : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  Δ.comp G

/-- 🏆 THEOREM: Regular projector and harmonic projector sum to identity. -/
theorem regular_add_harmonic_id (Δ G : V →ₗ[ℝ] V) :
    regularProjector Δ G + harmonicProjector Δ G = LinearMap.id := by
  dsimp [regularProjector, harmonicProjector]
  ext x
  simp

/-- 🏆 THEOREM: Regular projector is idempotent: $P_{\mathrm{reg}}^2 = P_{\mathrm{reg}}$. -/
theorem regular_projector_idempotent {Δ G : V →ₗ[ℝ] V} (h : MoorePenroseHodge Δ G) :
    (regularProjector Δ G).comp (regularProjector Δ G) = regularProjector Δ G := by
  dsimp [regularProjector]
  have h1 : (Δ.comp G).comp (Δ.comp G) = (Δ.comp (G.comp Δ)).comp G := by
    ext x
    dsimp
  rw [h1, h.mp1]

/-- 🏆 THEOREM: Harmonic projector is idempotent: $P_{\mathcal{H}}^2 = P_{\mathcal{H}}$. -/
theorem harmonic_projector_idempotent {Δ G : V →ₗ[ℝ] V} (h : MoorePenroseHodge Δ G) :
    (harmonicProjector Δ G).comp (harmonicProjector Δ G) = harmonicProjector Δ G := by
  dsimp [harmonicProjector]
  ext x
  simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  have h_reg : (Δ.comp G) ((Δ.comp G) x) = (Δ.comp G) x := by
    have h_idemp := LinearMap.congr_fun (regular_projector_idempotent h) x
    exact h_idemp
  calc x - (Δ.comp G) x - (Δ.comp G) (x - (Δ.comp G) x)
    _ = x - (Δ.comp G) x - ((Δ.comp G) x - (Δ.comp G) ((Δ.comp G) x)) := by
      rw [map_sub]
    _ = x - (Δ.comp G) x - ((Δ.comp G) x - (Δ.comp G) x) := by rw [h_reg]
    _ = x - (Δ.comp G) x := by abel

/-- 🏆 THEOREM: Harmonic projector maps into the nullspace of the Laplacian $\Delta$. -/
theorem harmonic_projector_in_kernel {Δ G : V →ₗ[ℝ] V} (h : MoorePenroseHodge Δ G) (x : V) :
    Δ (harmonicProjector Δ G x) = 0 := by
  dsimp [harmonicProjector]
  rw [map_sub]
  have h_comp : Δ (Δ (G x)) = Δ x := by
    have hcomm : Δ.comp G = G.comp Δ := h.comm
    calc Δ (Δ (G x)) = (Δ.comp (Δ.comp G)) x := rfl
      _ = (Δ.comp (G.comp Δ)) x := by rw [hcomm]
      _ = Δ x := by rw [h.mp1]
  rw [h_comp, sub_self]

/-- 🏆 THEOREM: Moore-Penrose exact inversion on the regular image sector. -/
theorem regular_sector_exact_inversion {Δ G : V →ₗ[ℝ] V} (h : MoorePenroseHodge Δ G) (y : V) :
    Δ (G (regularProjector Δ G y)) = regularProjector Δ G y := by
  dsimp [regularProjector]
  have h_mp1 := LinearMap.congr_fun h.mp1 (G y)
  exact h_mp1

/-- 🏆 THEOREM: Real Hodge diffusion energy dissipation: $\langle -\Delta x, x \rangle \le 0$. -/
theorem hodge_diffusion_dissipation {Δ G : V →ₗ[ℝ] V} (h : MoorePenroseHodge Δ G) (x : V) :
    inner (𝕜 := ℝ) (- Δ x) x ≤ 0 := by
  rw [inner_neg_left]
  have h_pos := h.pos_semidef_Δ x
  linarith

/-! ## 2. The Gauge Sector: Drazin Inversion & BRST-Krein Ghost Filtration -/

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

/-- Nilpotent BRST supercharge $Q$ ($Q^2 = 0$). -/
structure BRSTCharge (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  Q : V →ₗ[ℝ] V
  Q_nilpotent : Q.comp Q = 0

variable (B : BRSTCharge V)

/-- Physical (BRST-closed) state: $Q v = 0$. -/
def IsBRSTClosed (v : V) : Prop := B.Q v = 0

/-- Gauge-trivial (BRST-exact) ghost state: $v = Q w$. -/
def IsBRSTExact (v : V) : Prop := ∃ w : V, B.Q w = v

/-- Krein-BRST skew compatibility: $\langle J(Q x), y \rangle = - \langle J x, Q y \rangle$. -/
def IsKreinBRSTSkew (K : KreinSpace V) (B : BRSTCharge V) : Prop :=
  ∀ x y : V, inner (𝕜 := ℝ) (K.J (B.Q x)) y = - inner (𝕜 := ℝ) (K.J x) (B.Q y)

/-- 🏆 THEOREM: BRST squared annihilation $Q(Q v) = 0$. -/
theorem brst_squared_annihilation (v : V) : B.Q (B.Q v) = 0 :=
  LinearMap.congr_fun B.Q_nilpotent v

/-- 🏆 THEOREM: Every BRST exact state is closed: $\mathrm{range}(Q) \subseteq \ker(Q)$. -/
theorem brst_exact_is_closed (v : V) (h : IsBRSTExact B v) : IsBRSTClosed B v := by
  dsimp [IsBRSTClosed]
  rcases h with ⟨w, rfl⟩
  exact brst_squared_annihilation B w

/-- 🏆 THEOREM: Ghost Krein charge collapse: $[v, v]_J = 0$ for all $v = Q w$. -/
theorem brst_ghost_charge_collapse (h_skew : IsKreinBRSTSkew K B) (v : V) (h_exact : IsBRSTExact B v) :
    kreinCharge K v = 0 := by
  dsimp [kreinCharge, kreinInner]
  rcases h_exact with ⟨w, rfl⟩
  rw [h_skew w (B.Q w)]
  have h_nil := brst_squared_annihilation B w
  rw [h_nil, inner_zero_right, neg_zero]

/-- 🏆 THEOREM: Physical state decoupling: physical states $\psi$ decouple orthogonally from ghosts $v = Q w$. -/
theorem brst_physical_ghost_decoupling (h_skew : IsKreinBRSTSkew K B) (psi : V) (h_phys : IsBRSTClosed B psi)
    (v : V) (h_exact : IsBRSTExact B v) :
    kreinInner K v psi = 0 := by
  dsimp [kreinInner]
  rcases h_exact with ⟨w, rfl⟩
  rw [h_skew w psi]
  dsimp [IsBRSTClosed] at h_phys
  rw [h_phys, inner_zero_right, neg_zero]

/-- Drazin inverse conditions of index 1 (group inverse) for an endomorphism $T$:
    $T^2 T_D = T$, $T_D T T_D = T_D$, $T T_D = T_D T$. -/
structure DrazinIndexOne (T T_D : V →ₗ[ℝ] V) : Prop where
  drazin1 : (T.comp T).comp T_D = T
  drazin2 : (T_D.comp T).comp T_D = T_D
  comm : T.comp T_D = T_D.comp T

/-- 🏆 THEOREM: Any commuting Moore-Penrose pseudo-inverse is a Drazin inverse of index 1. -/
theorem moore_penrose_is_drazin_index_one {Δ G : V →ₗ[ℝ] V} (h : MoorePenroseHodge Δ G) :
    DrazinIndexOne Δ G := by
  have h_comm : Δ.comp G = G.comp Δ := h.comm
  have h_dr1 : (Δ.comp Δ).comp G = Δ := by
    calc (Δ.comp Δ).comp G = Δ.comp (Δ.comp G) := by ext x; rfl
      _ = Δ.comp (G.comp Δ) := by rw [h_comm]
      _ = Δ := h.mp1
  have h_dr2 : (G.comp Δ).comp G = G := by
    calc (G.comp Δ).comp G = G.comp (Δ.comp G) := by ext x; rfl
      _ = G := h.mp2
  exact ⟨h_dr1, h_dr2, h_comm⟩

/-- 🏆 THEOREM: Drazin propagator annihilates all null modes of $T$: $T v = 0 \implies T_D v = 0$. -/
theorem drazin_annihilates_null {T T_D : V →ₗ[ℝ] V} (h : DrazinIndexOne T T_D) (v : V) (hv : T v = 0) :
    T_D v = 0 := by
  have h2 := LinearMap.congr_fun h.drazin2 v
  have h_step : (T_D.comp (T.comp T_D)) v = T_D v := h2
  have h_comm : T.comp T_D = T_D.comp T := h.comm
  rw [h_comm] at h_step
  dsimp at h_step
  rw [hv, map_zero, map_zero] at h_step
  exact h_step.symm

/-- 🏆 MASTER SYNTHESIS: Moore-Penrose Hodge Diffusion & Drazin-BRST Ghost Confinement. -/
theorem certified_mp_hodge_drazin_ghost_synthesis
    {Δ G : V →ₗ[ℝ] V} (h_mp : MoorePenroseHodge Δ G)
    (h_skew : IsKreinBRSTSkew K B) (psi : V) (h_phys : IsBRSTClosed B psi)
    (v : V) (h_exact : IsBRSTExact B v) (x : V) :
    (regularProjector Δ G + harmonicProjector Δ G = LinearMap.id) ∧
    (Δ (harmonicProjector Δ G x) = 0) ∧
    (inner (𝕜 := ℝ) (- Δ x) x ≤ 0) ∧
    (DrazinIndexOne Δ G) ∧
    (B.Q (B.Q v) = 0) ∧
    (IsBRSTClosed B v) ∧
    (kreinCharge K v = 0) ∧
    (kreinInner K v psi = 0) :=
  ⟨regular_add_harmonic_id Δ G,
   harmonic_projector_in_kernel h_mp x,
   hodge_diffusion_dissipation h_mp x,
   moore_penrose_is_drazin_index_one h_mp,
   brst_squared_annihilation B v,
   brst_exact_is_closed B v h_exact,
   brst_ghost_charge_collapse K B h_skew v h_exact,
   brst_physical_ghost_decoupling K B h_skew psi h_phys v h_exact⟩

end InfoGeometry.Physics.MoorePenroseHodgeDrazinGhostBridge
