import Mathlib

open scoped BigOperators

namespace InfoGeometry.Foundations.AxiomaticDependencyGraph

noncomputable section

/-!
--- AUDIT PROTOCOL MAP ---

BUCKET 1: CLOSED FINITE THEOREMS:
  - tri_facet_resolution (Geometric sum to identity of the exact, coexact, and harmonic projectors)
  - exact_projector_idempotent (Idempotency of the exact projection sector)
  - coexact_projector_idempotent (Idempotency of the coexact projection sector)
  - harmonic_projector_idempotent (Idempotency of the harmonic boundary projection sector)
  - exact_coexact_disjoint (Orthogonal decoupling of exact and coexact projections)
  - coexact_exact_disjoint (Orthogonal decoupling of coexact and exact projections)
  - exact_harmonic_disjoint (Orthogonal decoupling of exact and harmonic projections)
  - coexact_harmonic_disjoint (Orthogonal decoupling of coexact and harmonic projections)
  - harmonic_exact_disjoint (Orthogonal decoupling of harmonic and exact projections)
  - harmonic_coexact_disjoint (Orthogonal decoupling of harmonic and coexact projections)
  - hodge_krein_orthogonality (Symmetric decoupling of exact and coexact sectors under the Krein metric)
  - shear_preserves_kernel (Nilpotent boundary operator preserves the topological zero-mode kernel)
  - shear_zero_on_harmonic_image (Boundary shear stabilizes the isolated harmonic projection sector)
  - verlinde_symm_ab (Permutation symmetry of fusion coefficients between channels a and b)
  - verlinde_symm_bc (Permutation symmetry of fusion coefficients between channels b and c)
  - verlinde_symm_ac (Permutation symmetry of fusion coefficients between channels a and c)

BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES:
  - All theorems are conditional on the explicit witnesses bundled in:
    Node0_KreinSpace, Node1_TriFacetOperator, Node3_NilpotentShear, and Node5_VerlindeFusionRing.

BUCKET 3: OPEN CLOSURE DEBT:
  - None.
--------------------------
-/

section HodgeKreinTriFacet

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

class Node0_KreinSpace (V : Type*) [AddCommGroup V] [Module ℝ V] where
  B : V → V → ℝ
  B_add_left : ∀ x y z, B (x + y) z = B x z + B y z
  B_smul_left : ∀ c x y, B (c • x) y = c * B x y
  B_comm : ∀ x y, B x y = B y x
  J : V →ₗ[ℝ] V
  J_sq : ∀ x, J (J x) = x
  J_adj : ∀ x y, B (J x) y = B x (J y)

class Node1_TriFacetOperator (V : Type*) [AddCommGroup V] [Module ℝ V] [Node0_KreinSpace V] where
  O : V →ₗ[ℝ] V
  O_cubed : ∀ x, O (O (O x)) = O x
  O_adj : ∀ x y, Node0_KreinSpace.B (O x) y = Node0_KreinSpace.B x (O y)

variable [Node0_KreinSpace V] [Node1_TriFacetOperator V]

def exact_projector (x : V) : V :=
  (1 / 2 : ℝ) • (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) + Node1_TriFacetOperator.O x)

def coexact_projector (x : V) : V :=
  (1 / 2 : ℝ) • (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) - Node1_TriFacetOperator.O x)

def harmonic_projector (x : V) : V :=
  x - Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x)

theorem tri_facet_resolution (x : V) :
    exact_projector x + coexact_projector x + harmonic_projector x = x := by
  dsimp [exact_projector, coexact_projector, harmonic_projector]
  rw [smul_add, smul_sub]
  have h : (1 / 2 : ℝ) • Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) + (1 / 2 : ℝ) • Node1_TriFacetOperator.O x +
           ((1 / 2 : ℝ) • Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) - (1 / 2 : ℝ) • Node1_TriFacetOperator.O x) =
           (1 / 2 : ℝ) • Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) + (1 / 2 : ℝ) • Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) := by abel
  rw [h, ← add_smul]
  have h_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  rw [h_num, one_smul]
  abel

theorem exact_projector_idempotent (x : V) :
    exact_projector (exact_projector x) = exact_projector x := by
  have hO : Node1_TriFacetOperator.O (exact_projector x) = exact_projector x := by
    dsimp [exact_projector]
    rw [map_smul, map_add, Node1_TriFacetOperator.O_cubed, add_comm]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (exact_projector x)) = exact_projector x := by
    rw [hO, hO]
  rw [exact_projector, hOO, hO]
  have h_add : exact_projector x + exact_projector x = (2 : ℝ) • exact_projector x := by
    rw [← one_smul ℝ (exact_projector x), ← add_smul]
    norm_num
  rw [h_add, ← mul_smul]
  norm_num

theorem coexact_projector_idempotent (x : V) :
    coexact_projector (coexact_projector x) = coexact_projector x := by
  have hO : Node1_TriFacetOperator.O (coexact_projector x) = - coexact_projector x := by
    dsimp [coexact_projector]
    rw [map_smul, map_sub, Node1_TriFacetOperator.O_cubed, ← smul_neg, neg_sub]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (coexact_projector x)) = coexact_projector x := by
    rw [hO, LinearMap.map_neg, hO, neg_neg]
  rw [coexact_projector, hOO, hO, sub_neg_eq_add]
  have h_add : coexact_projector x + coexact_projector x = (2 : ℝ) • coexact_projector x := by
    rw [← one_smul ℝ (coexact_projector x), ← add_smul]
    norm_num
  rw [h_add, ← mul_smul]
  norm_num

theorem harmonic_projector_idempotent (x : V) :
    harmonic_projector (harmonic_projector x) = harmonic_projector x := by
  have hO : Node1_TriFacetOperator.O (harmonic_projector x) = 0 := by
    dsimp [harmonic_projector]
    rw [map_sub, Node1_TriFacetOperator.O_cubed, sub_self]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (harmonic_projector x)) = 0 := by
    rw [hO, LinearMap.map_zero]
  rw [harmonic_projector, hOO, sub_zero]

theorem exact_coexact_disjoint (x : V) :
    exact_projector (coexact_projector x) = 0 := by
  have hO : Node1_TriFacetOperator.O (coexact_projector x) = - coexact_projector x := by
    dsimp [coexact_projector]
    rw [map_smul, map_sub, Node1_TriFacetOperator.O_cubed, ← smul_neg, neg_sub]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (coexact_projector x)) = coexact_projector x := by
    rw [hO, LinearMap.map_neg, hO, neg_neg]
  rw [exact_projector, hOO, hO, add_neg_cancel, smul_zero]

theorem coexact_exact_disjoint (x : V) :
    coexact_projector (exact_projector x) = 0 := by
  have hO : Node1_TriFacetOperator.O (exact_projector x) = exact_projector x := by
    dsimp [exact_projector]
    rw [map_smul, map_add, Node1_TriFacetOperator.O_cubed, add_comm]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (exact_projector x)) = exact_projector x := by
    rw [hO, hO]
  rw [coexact_projector, hOO, hO, sub_self, smul_zero]

theorem exact_harmonic_disjoint (x : V) :
    exact_projector (harmonic_projector x) = 0 := by
  have hO : Node1_TriFacetOperator.O (harmonic_projector x) = 0 := by
    dsimp [harmonic_projector]
    rw [map_sub, Node1_TriFacetOperator.O_cubed, sub_self]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (harmonic_projector x)) = 0 := by
    rw [hO, LinearMap.map_zero]
  rw [exact_projector, hOO, hO, add_zero, smul_zero]

theorem coexact_harmonic_disjoint (x : V) :
    coexact_projector (harmonic_projector x) = 0 := by
  have hO : Node1_TriFacetOperator.O (harmonic_projector x) = 0 := by
    dsimp [harmonic_projector]
    rw [map_sub, Node1_TriFacetOperator.O_cubed, sub_self]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (harmonic_projector x)) = 0 := by
    rw [hO, LinearMap.map_zero]
  rw [coexact_projector, hOO, hO, sub_zero, smul_zero]

theorem harmonic_exact_disjoint (x : V) :
    harmonic_projector (exact_projector x) = 0 := by
  have hO : Node1_TriFacetOperator.O (exact_projector x) = exact_projector x := by
    dsimp [exact_projector]
    rw [map_smul, map_add, Node1_TriFacetOperator.O_cubed, add_comm]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (exact_projector x)) = exact_projector x := by
    rw [hO, hO]
  rw [harmonic_projector, hOO, sub_self]

theorem harmonic_coexact_disjoint (x : V) :
    harmonic_projector (coexact_projector x) = 0 := by
  have hO : Node1_TriFacetOperator.O (coexact_projector x) = - coexact_projector x := by
    dsimp [coexact_projector]
    rw [map_smul, map_sub, Node1_TriFacetOperator.O_cubed, ← smul_neg, neg_sub]
  have hOO : Node1_TriFacetOperator.O (Node1_TriFacetOperator.O (coexact_projector x)) = coexact_projector x := by
    rw [hO, LinearMap.map_neg, hO, neg_neg]
  rw [harmonic_projector, hOO, sub_self]

theorem hodge_krein_orthogonality (x y : V) :
    Node0_KreinSpace.B (exact_projector x) (coexact_projector y) = 0 := by
  dsimp [exact_projector, coexact_projector]
  have h_add_left : ∀ (u1 u2 v : V), Node0_KreinSpace.B (u1 + u2) v = Node0_KreinSpace.B u1 v + Node0_KreinSpace.B u2 v := Node0_KreinSpace.B_add_left
  have h_smul1 : ∀ (c : ℝ) (u v : V), Node0_KreinSpace.B (c • u) v = c * Node0_KreinSpace.B u v := Node0_KreinSpace.B_smul_left
  have h_smul2 : ∀ (c : ℝ) (u v : V), Node0_KreinSpace.B u (c • v) = c * Node0_KreinSpace.B u v := by
    intro c u v
    rw [Node0_KreinSpace.B_comm u (c • v), h_smul1, Node0_KreinSpace.B_comm u v]
  have h_add_right : ∀ (u v1 v2 : V), Node0_KreinSpace.B u (v1 + v2) = Node0_KreinSpace.B u v1 + Node0_KreinSpace.B u v2 := by
    intro u v1 v2
    rw [Node0_KreinSpace.B_comm u (v1 + v2), h_add_left, Node0_KreinSpace.B_comm v1 u, Node0_KreinSpace.B_comm v2 u]
  have B_zero_right : ∀ (u : V), Node0_KreinSpace.B u 0 = 0 := by
    intro u
    have h : Node0_KreinSpace.B u (0 + 0) = Node0_KreinSpace.B u 0 + Node0_KreinSpace.B u 0 := h_add_right u 0 0
    have h0 : (0 : V) + 0 = 0 := add_zero 0
    rw [h0] at h
    linarith
  have h_neg_right : ∀ (u v : V), Node0_KreinSpace.B u (-v) = - Node0_KreinSpace.B u v := by
    intro u v
    have h : Node0_KreinSpace.B u (v + -v) = Node0_KreinSpace.B u v + Node0_KreinSpace.B u (-v) := h_add_right u v (-v)
    have h' : (0 : ℝ) = Node0_KreinSpace.B u v + Node0_KreinSpace.B u (-v) := by
      simpa [B_zero_right u] using h
    linarith
  have h_sub_right : ∀ (u v1 v2 : V), Node0_KreinSpace.B u (v1 - v2) = Node0_KreinSpace.B u v1 - Node0_KreinSpace.B u v2 := by
    intro u v1 v2
    have h : v1 - v2 = v1 + -v2 := sub_eq_add_neg v1 v2
    rw [h, h_add_right, h_neg_right]
    rfl
  have h_smul_both : Node0_KreinSpace.B ((1 / 2 : ℝ) • (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) + Node1_TriFacetOperator.O x)) ((1 / 2 : ℝ) • (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O y) - Node1_TriFacetOperator.O y)) =
                     (1 / 2 : ℝ) * (1 / 2 : ℝ) * Node0_KreinSpace.B (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x) + Node1_TriFacetOperator.O x) (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O y) - Node1_TriFacetOperator.O y) := by
    rw [h_smul1, h_smul2, mul_assoc]
  rw [h_smul_both, h_add_left, h_sub_right, h_sub_right]
  have term1 : Node0_KreinSpace.B (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x)) (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O y)) =
               Node0_KreinSpace.B (Node1_TriFacetOperator.O x) (Node1_TriFacetOperator.O y) := by
    have h := Node1_TriFacetOperator.O_adj (Node1_TriFacetOperator.O x) (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O y))
    simpa [Node1_TriFacetOperator.O_cubed y] using h
  have term2 : Node0_KreinSpace.B (Node1_TriFacetOperator.O x) (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O y)) =
               Node0_KreinSpace.B (Node1_TriFacetOperator.O (Node1_TriFacetOperator.O x)) (Node1_TriFacetOperator.O y) := by
    simpa using (Node1_TriFacetOperator.O_adj (Node1_TriFacetOperator.O x) (Node1_TriFacetOperator.O y)).symm
  rw [term1, term2]
  ring

class Node3_NilpotentShear (V : Type*) [AddCommGroup V] [Module ℝ V]
  [Node0_KreinSpace V] [Node1_TriFacetOperator V] where
  N : V →ₗ[ℝ] V
  N_nilpotent : ∀ x, N (N x) = 0
  N_locks_kernel : ∀ x, Node1_TriFacetOperator.O x = 0 → N x = 0

variable [Node3_NilpotentShear V]

theorem shear_preserves_kernel (x : V) :
    Node1_TriFacetOperator.O x = 0 →
    Node1_TriFacetOperator.O (Node3_NilpotentShear.N x) = 0 := by
  intro h
  rw [Node3_NilpotentShear.N_locks_kernel x h]
  exact LinearMap.map_zero Node1_TriFacetOperator.O

theorem shear_zero_on_harmonic_image (x : V)
    (h : Node1_TriFacetOperator.O (harmonic_projector x) = 0) :
    Node3_NilpotentShear.N (harmonic_projector x) = 0 :=
  Node3_NilpotentShear.N_locks_kernel (harmonic_projector x) h

class Node4_MajoranaBEC (V : Type*) [AddCommGroup V] [Module ℝ V]
  [Node0_KreinSpace V] [Node1_TriFacetOperator V] [Node3_NilpotentShear V] where
  B_condensate : V →ₗ[ℝ] (V →ₗ[ℝ] ℝ)
  Condensate_energy_zero :
    ∀ x y,
    Node1_TriFacetOperator.O x = 0 →
    Node1_TriFacetOperator.O y = 0 →
    B_condensate x y = 0

class Node5_VerlindeFusionRing (Idx : Type*) [Fintype Idx] where
  vac : Idx
  S : Idx → Idx → ℝ
  N_fuse : Idx → Idx → Idx → ℝ
  verlinde_formula :
    ∀ a b c, N_fuse a b c = ∑ x, (S a x * S b x * S c x) / S vac x

theorem verlinde_symm_ab {Idx : Type*} [Fintype Idx] [Node5_VerlindeFusionRing Idx] (a b c : Idx) :
    Node5_VerlindeFusionRing.N_fuse a b c = Node5_VerlindeFusionRing.N_fuse b a c := by
  rw [Node5_VerlindeFusionRing.verlinde_formula a b c]
  rw [Node5_VerlindeFusionRing.verlinde_formula b a c]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem verlinde_symm_bc {Idx : Type*} [Fintype Idx] [Node5_VerlindeFusionRing Idx] (a b c : Idx) :
    Node5_VerlindeFusionRing.N_fuse a b c = Node5_VerlindeFusionRing.N_fuse a c b := by
  rw [Node5_VerlindeFusionRing.verlinde_formula a b c]
  rw [Node5_VerlindeFusionRing.verlinde_formula a c b]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem verlinde_symm_ac {Idx : Type*} [Fintype Idx] [Node5_VerlindeFusionRing Idx] (a b c : Idx) :
    Node5_VerlindeFusionRing.N_fuse a b c = Node5_VerlindeFusionRing.N_fuse c b a := by
  rw [Node5_VerlindeFusionRing.verlinde_formula a b c]
  rw [Node5_VerlindeFusionRing.verlinde_formula c b a]
  apply Finset.sum_congr rfl
  intro x _
  ring

end HodgeKreinTriFacet

end

end InfoGeometry.Foundations.AxiomaticDependencyGraph
